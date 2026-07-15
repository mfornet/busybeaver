import SQLite
import Std.Sync.Mutex
import Std.Sync.Channel

/-!
# Witness store

A SQLite-backed cache of per-machine decision outcomes, keyed by the canonical
machine code string (identical to `repr M`, e.g. `0RB---_0RC1RB_...`).

This is the *unverified* tooling layer behind `beaver L S --trusted`: it lets a
re-run skip re-executing the deciders by trusting a previously recorded result.
It deliberately constructs no Lean proof — see `memory/witness-store.md`.

This module knows nothing about `Busybeaver`/`Machine`; it speaks in `String`
codes and `ℕ`s so it stays a thin, reusable persistence layer. The translation
from a `HaltM` decision to a `Record` lives in the walk layer.
-/

namespace Witness

/-- The schema version persisted in the `meta` table. Bump on any incompatible
schema change so stale databases can be detected. -/
def schemaVersion : Nat := 1

/-- The three terminal classifications a machine can receive.
`unknown` (a holdout) is stored too, since we do full memoization. -/
inductive Kind where
  | halt
  | nonhalt
  | unknown
deriving DecidableEq, Repr, Inhabited

def Kind.toString : Kind → String
  | .halt => "halt"
  | .nonhalt => "nonhalt"
  | .unknown => "unknown"

def Kind.ofString? : String → Option Kind
  | "halt" => some .halt
  | "nonhalt" => some .nonhalt
  | "unknown" => some .unknown
  | _ => none

instance : ToString Kind := ⟨Kind.toString⟩

/-- One persisted row. For `halt`, `haltState`/`haltSymbol`/`haltSteps` are
populated (state+symbol drive child generation without re-simulation, steps feed
the BB value). `decider` records which `DeciderConfig` settled it (provenance;
`none` for `unknown`). -/
structure Record where
  code : String
  l : Nat
  s : Nat
  kind : Kind
  haltState : Option Nat := none
  haltSymbol : Option Nat := none
  haltSteps : Option Nat := none
  decider : Option String := none
deriving Repr, Inhabited

/-- Handle to an open witness DB plus the two hot prepared statements. -/
structure Store where
  db : SQLite
  insertStmt : SQLite.Stmt
  lookupStmt : SQLite.Stmt
  /-- Serializes ALL connection access (`put` and `get?`). The parallel walks touch
  this one connection and its shared prepared statements from many `Task` threads,
  so every read and write must go through this lock — resetting/binding/stepping a
  shared statement from two threads at once corrupts it. -/
  dbLock : Std.BaseMutex

namespace Store

/-! ## Nat ↔ Int64 / binding helpers -/

-- SQLite `INTEGER`s are signed 64-bit, so only `Nat`s below `2^63` round-trip.
-- All values stored here (step counts, cell indices, sizes) are far below that;
-- panic loudly rather than silently wrap if that ever stops being true.
private def natToI64 (n : Nat) : Int64 :=
  if n < 2 ^ 63 then Int64.ofNat n
  else panic! s!"witness: value {n} exceeds the signed 64-bit range"
private def i64ToNat (n : Int64) : Nat := n.toInt.toNat

private def bindOptNat (stmt : SQLite.Stmt) (idx : Int32) : Option Nat → IO Unit
  | some n => stmt.bindInt64 idx (natToI64 n)
  | none => stmt.bindNull idx

/-- Read an `INTEGER` column as `Option Nat`, mapping SQL `NULL` to `none`. -/
private def colOptNat (stmt : SQLite.Stmt) (idx : Int32) : IO (Option Nat) := do
  if ← stmt.columnNull idx then
    return none
  else
    return some (i64ToNat (← stmt.columnInt64 idx))

/-- Read a `TEXT` column as `Option String`, mapping SQL `NULL` to `none`. -/
private def colOptText (stmt : SQLite.Stmt) (idx : Int32) : IO (Option String) := do
  if ← stmt.columnNull idx then
    return none
  else
    return some (← stmt.columnText idx)

/-! ## Open / schema -/

private def ddl : String :=
  "CREATE TABLE IF NOT EXISTS witness (
     code TEXT PRIMARY KEY,
     l INTEGER NOT NULL,
     s INTEGER NOT NULL,
     kind TEXT NOT NULL,
     halt_state INTEGER,
     halt_symbol INTEGER,
     halt_steps INTEGER,
     decider TEXT
   ) STRICT;
   CREATE TABLE IF NOT EXISTS meta (
     key TEXT PRIMARY KEY,
     value TEXT NOT NULL
   ) STRICT;
   CREATE TABLE IF NOT EXISTS results (
     l INTEGER NOT NULL,
     s INTEGER NOT NULL,
     bb_value INTEGER NOT NULL,
     decided INTEGER NOT NULL,
     holdouts TEXT NOT NULL,
     PRIMARY KEY (l, s)
   ) STRICT;"

/-- Open (creating if absent) the witness DB at `path`, install the schema, and
prepare the insert/lookup statements. Uses WAL + `synchronous=NORMAL` for fast
bulk writes during a build. -/
def openAt (path : System.FilePath) : IO Store := do
  let db ← SQLite.«open» path
  db.exec "PRAGMA journal_mode=WAL;"
  db.exec "PRAGMA synchronous=NORMAL;"
  db.exec ddl
  -- Record the schema version if this is a fresh database.
  db.exec s!"INSERT OR IGNORE INTO meta (key, value) VALUES ('schema_version', '{schemaVersion}');"
  -- Validate it: the INSERT OR IGNORE sets it on a fresh DB but leaves an existing
  -- DB's own value, so a mismatch here means an incompatible witness file.
  let vstmt ← db.prepare "SELECT value FROM meta WHERE key = 'schema_version';"
  if ← vstmt.step then
    let stored ← vstmt.columnText 0
    if stored != toString schemaVersion then
      throw <| IO.userError
        s!"witness: DB {path} has schema version {stored}, expected {schemaVersion}; regenerate it"
  let insertStmt ← db.prepare
    "INSERT OR REPLACE INTO witness
       (code, l, s, kind, halt_state, halt_symbol, halt_steps, decider)
     VALUES (?, ?, ?, ?, ?, ?, ?, ?);"
  let lookupStmt ← db.prepare
    "SELECT kind, halt_state, halt_symbol, halt_steps, decider, l, s
     FROM witness WHERE code = ?;"
  let dbLock ← Std.BaseMutex.new
  return { db, insertStmt, lookupStmt, dbLock }

/-! ## Write / read -/

/-- Insert (or replace) one record. Thread-safe (guarded by `dbLock`), so the
parallel emit walk can call it concurrently. Call inside `runTransaction` for
bulk speed. -/
def put (store : Store) (r : Record) : IO Unit := do
  store.dbLock.lock
  try
    let stmt := store.insertStmt
    stmt.reset
    stmt.clearBindings
    stmt.bindText 1 r.code
    stmt.bindInt64 2 (natToI64 r.l)
    stmt.bindInt64 3 (natToI64 r.s)
    stmt.bindText 4 r.kind.toString
    bindOptNat stmt 5 r.haltState
    bindOptNat stmt 6 r.haltSymbol
    bindOptNat stmt 7 r.haltSteps
    match r.decider with
      | some d => stmt.bindText 8 d
      | none => stmt.bindNull 8
    discard stmt.step
  finally
    store.dbLock.unlock

/-- Look up a machine by its code. `none` means "not in the witness". Thread-safe
(guarded by `dbLock`): the shared `lookupStmt` must not be reset/bound/stepped by
two threads at once, which is exactly what the parallel `--trusted` self-healing
walk would otherwise do. -/
def get? (store : Store) (code : String) : IO (Option Record) := do
  store.dbLock.lock
  try
    let stmt := store.lookupStmt
    stmt.reset
    stmt.clearBindings
    stmt.bindText 1 code
    if ← stmt.step then
      let kindStr ← stmt.columnText 0
      let some kind := Kind.ofString? kindStr
        | throw <| IO.userError s!"witness: bad kind {kindStr} for {code}"
      let haltState ← colOptNat stmt 1
      let haltSymbol ← colOptNat stmt 2
      let haltSteps ← colOptNat stmt 3
      let decider ← colOptText stmt 4
      let l := i64ToNat (← stmt.columnInt64 5)
      let s := i64ToNat (← stmt.columnInt64 6)
      pure (some { code, l, s, kind, haltState, haltSymbol, haltSteps, decider })
    else
      pure none
  finally
    store.dbLock.unlock

/-- Run `act` inside a single SQL transaction (deferred). Wrap a batch of `put`s
in this — committing per row is ~100× slower. -/
def runTransaction (store : Store) (act : IO α) : IO α :=
  store.db.transaction act

/-- Number of stored rows (debugging / progress). -/
def count (store : Store) : IO Nat := do
  let stmt ← store.db.prepare "SELECT COUNT(*) FROM witness;"
  let _ ← stmt.step
  return i64ToNat (← stmt.columnInt64 0)

/-! ## Channel-fed bulk write

The parallel generation walk's threads only `send` records to a channel; this one
function drains it. Because exactly one thread runs it, it is the *sole* user of
the SQLite connection during generation — so writes never contend with each other
or with the deciders, they just overlap the parallel decode work. Returns once the
channel is closed and emptied. -/
private partial def drainLoop (store : Store) (chan : Std.CloseableChannel Record) : IO Unit := do
  match (← chan.recv).get with
  | some r => store.put r; drainLoop store chan
  | none => pure ()

/-- Drain `chan` into the witness table inside a single transaction. Run this as a
dedicated writer task while the walk feeds records into `chan`. -/
def drainChannel (store : Store) (chan : Std.CloseableChannel Record) : IO Unit :=
  store.runTransaction (drainLoop store chan)

/-! ## Aggregate result (for instant `--trusted` reads)

The final answer of a whole `beaver l s` run — the BB value, whether it was fully
decided, and the holdout codes — cached so `--trusted` is a single-row read
instead of an 858k-node walk. -/

/-- Store the aggregate result for size `(l, s)`. `holdouts` are the undecided
machine codes; `decided` is recorded as `holdouts.isEmpty`. -/
def putResult (store : Store) (l s bbValue : Nat) (holdouts : Array String) : IO Unit := do
  let stmt ← store.db.prepare
    "INSERT OR REPLACE INTO results (l, s, bb_value, decided, holdouts) VALUES (?, ?, ?, ?, ?);"
  stmt.bindInt64 1 (natToI64 l)
  stmt.bindInt64 2 (natToI64 s)
  stmt.bindInt64 3 (natToI64 bbValue)
  stmt.bindInt64 4 (if holdouts.isEmpty then 1 else 0)
  stmt.bindText 5 (String.intercalate "\n" holdouts.toList)
  discard stmt.step

/-- Read the cached aggregate result for `(l, s)`: `(bbValue, decided, holdouts)`.
`none` if this size hasn't been generated yet. -/
def getResult? (store : Store) (l s : Nat) : IO (Option (Nat × Bool × Array String)) := do
  let stmt ← store.db.prepare
    "SELECT bb_value, decided, holdouts FROM results WHERE l = ? AND s = ?;"
  stmt.bindInt64 1 (natToI64 l)
  stmt.bindInt64 2 (natToI64 s)
  if ← stmt.step then
    let bbValue := i64ToNat (← stmt.columnInt64 0)
    let decided := (← stmt.columnInt64 1) ≠ 0
    let holdoutsText ← stmt.columnText 2
    let holdouts := if holdoutsText.isEmpty then #[] else (holdoutsText.splitOn "\n").toArray
    return some (bbValue, decided, holdouts)
  else
    return none

end Store
end Witness
