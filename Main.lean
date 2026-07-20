import Busybeaver
import Witness
import Mathlib.Data.Nat.Notation
import Init.Data.String

import Lean.Data.Json

import Cli

import LeanTqdm

open TM TM.Table Pipeline

section DeciderCombinator

open Lean

def toLogDecider (cfg: List DeciderConfig) (quiet: Bool) (M: Machine l s): HaltM M Unit := do
  let res := toTableDecider cfg M
  if !quiet && !HaltM.decided res then
    dbg_trace s!"{repr M} {res}"
  res

/-- Emit-mode classifier: run the real deciders on `M`, write the resulting
record to the witness store, and report the `Outcome` so the walk can expand
children. The halt cell `(state, symbol)` and actual step count `n+1` are pulled
straight from the decider's `halts_prf` proof. -/
def classifyRecord (cfg: List DeciderConfig) (M: Machine l s):
    Witness.Record × Witness.Outcome :=
  let (res, who) := decideWithProvenance cfg M
  let code := reprStr M
  match res with
  | .halts_prf n C _ =>
      let st := C.state.val
      let sy := C.tape.head.val
      ({ code, l, s, kind := .halt,
         haltState := some st, haltSymbol := some sy, haltSteps := some (n + 1),
         decider := who }, .halt st sy (n + 1))
  | .loops_prf _ => ({ code, l, s, kind := .nonhalt, decider := who }, .nonhalt)
  | .unknown _ => ({ code, l, s, kind := .unknown }, .unknown)

/-- Direct-write emit classifier (writes via the locked `Store.put`; used by the
self-healing trusted fallback, where writes can be concurrent). -/
def emitClassify (store: Witness.Store) (cfg: List DeciderConfig) (M: Machine l s):
    IO Witness.Outcome := do
  let (rec, outcome) := classifyRecord cfg M
  store.put rec
  return outcome

/-- Channel-feeding emit classifier: the decider threads only `send` records, and
a single writer task drains the channel into SQLite. No write contention. -/
def emitClassifyChan (chan: Std.CloseableChannel Witness.Record) (cfg: List DeciderConfig)
    (M: Machine l s): IO Witness.Outcome := do
  let (rec, outcome) := classifyRecord cfg M
  -- Don't swallow the send result: a closed channel would otherwise drop the
  -- record silently, leaving an under-populated DB that `--trusted` trusts.
  match (← chan.send rec).get with
  | .ok _ => return outcome
  | .error _ => throw <| IO.userError s!"witness: channel send failed for {rec.code} (closed?)"

/-- Trusted-mode classifier: read `M`'s outcome from the store. On a miss, fall
back to `fallback` (typically `emitClassify`, which also self-heals the DB). -/
def trustedClassify (store: Witness.Store) (fallback: Machine l s → IO Witness.Outcome)
    (M: Machine l s): IO Witness.Outcome := do
  match ← store.get? (reprStr M) with
  | some rec =>
      match rec.kind with
      | .halt =>
          -- A halt row must carry its cell + step count; a NULL means a corrupt /
          -- partial write, so surface it rather than silently expanding cell (0,0).
          match rec.haltState, rec.haltSymbol, rec.haltSteps with
          | some st, some sy, some steps => return .halt st sy steps
          | _, _, _ =>
              throw <| IO.userError s!"witness: halt row for {reprStr M} has NULL halt metadata"
      | .nonhalt => return .nonhalt
      | .unknown => return .unknown
  | none => fallback M

def configFromFile (path: String): IO (Option <| List DeciderConfig) := do
  let content ← IO.FS.readFile path
  let Except.ok parsed := Json.parse content | throw <| IO.userError "Invalid JSON"
  let .ok done := fromJson? parsed | throw <| IO.userError "Invalid configuration"
  return done

def determineConfig (l s : ℕ): (Option String) → IO (List DeciderConfig)
| none => pure (defaultConfigFor l s)
| some path => do
    return match (← configFromFile path) with
    | none => defaultConfigFor l s
    | some cfg => cfg

end DeciderCombinator

section Progress

open Tqdm

instance {l s : ℕ} {M : Machine l s} [Inhabited α] : Inhabited (HaltM M α) := ⟨.unknown default⟩

/-- Advance `pb` by one as a deliberate side effect inside otherwise-pure code, then return `x`.
Modeled on `dbg_trace`: `@[never_extract]` keeps the compiler from dropping, hoisting, or CSE-ing
the call, and threading `x` through the return value creates a data dependency so the call is not
discarded.  The two `match` branches must differ (the unreachable `.error` panics) so the compiler
cannot merge them and elide the `unsafeIO` scrutinee as dead code — that scrutiny is what forces
the `IO` action to actually run. -/
@[never_extract] unsafe def tickReturn [Inhabited α] (pb : ProgressBar) (x : α) : α :=
  match unsafeIO pb.update with
  | .ok _ => x
  | .error _ => panic! "progress bar update failed"

/-- Compiled implementation of `tickDecider`: tick the bar, then defer to `dec`. -/
unsafe def tickDeciderImpl (pb : ProgressBar) (dec : (M : Machine l s) → HaltM M Unit)
    (M : Machine l s) : HaltM M Unit :=
  tickReturn pb (dec M)

/-- Decider wrapper that advances `pb` once per call.  The kernel sees the identity `fun M => dec M`
(so the correctness proof in `computeCmd` is unaffected), while the compiled code runs
`tickDeciderImpl` and ticks the progress bar.  The enumeration core invokes the decider exactly
once per visited machine, so the bar reflects machines processed. -/
@[implemented_by tickDeciderImpl]
def tickDecider (_pb : ProgressBar) (dec : (M : Machine l s) → HaltM M Unit)
    (M : Machine l s) : HaltM M Unit := dec M

end Progress

section Cli

open Cli

open TM.Parse

unsafe def save_to_file (path: String) (set: Multiset (Machine l s)): IO Unit :=
  IO.FS.withFile path IO.FS.Mode.write (λ file ↦ do
    for M in Quot.unquot set do
      file.putStrLn s!"{repr M}")

instance: ParseableType MParseRes where
  name := s!"Machine"
  parse? str := match TM.Parse.pmachine (⟨str, str.startPos⟩) with
    | .success _ M => some M
    | .error _ _ => none

def runDecideCmd (p: Parsed): IO UInt32 := do
  let ⟨l, s, M⟩ := p.positionalArg! "machine" |>.as! MParseRes

  IO.println s!"Parsed machine with {l + 1} labels and {s + 1} symbols: {repr M}"

  let cfg ← determineConfig l s ((p.flag? "config").map (Parsed.Flag.as! · String))
  let runAll := p.hasFlag "all"

  for d in cfg do
    let res := d.deciderTable M
    IO.println s!"{d}: {res}"
    if !runAll && HaltM.decided res then
      return 0

  return 0

unsafe def decideCmd := `[Cli|
  decide VIA runDecideCmd;
  "Runs the deciders on the provided machine."

  FLAGS:
    c, config: String; "Configuration of the deciders to run"
    a, all; "Keep running after a decider reaches a definite result"

  ARGS:
    machine: String; "The machine code"
]

def firstToken (line : String) : String :=
  (line.trimAscii.toString.takeWhile (!·.isWhitespace)).toString

def auditLine (resolveConfig : ℕ → ℕ → List DeciderConfig) (line : String) : IO Unit := do
  let code := firstToken line
  if code.isEmpty then
    return
  match TM.Parse.pmachine (⟨code, code.startPos⟩) with
  | .error _ err =>
      IO.println s!"{code} parse-error: {err}"
  | .success _ ⟨l, s, M⟩ =>
      match firstDecision? (resolveConfig l s) M with
      | none => IO.println s!"{code} unknown"
      | some (decider, result) => IO.println s!"{code} {result} by {decider}"

def runAuditCmd (p: Parsed): IO UInt32 := do
  let path := p.positionalArg! "input" |>.as! String
  let cfgPath? := (p.flag? "config").map (Parsed.Flag.as! · String)
  let limit? := (p.flag? "limit").map (Parsed.Flag.as! · ℕ)
  -- Resolve the config once: a supplied file is read and parsed a single time,
  -- while the default config is cheap to recompute per machine size.
  let resolveConfig ← match cfgPath? with
    | none => pure (fun l s => defaultConfigFor l s)
    | some path => do
        let loaded ← configFromFile path
        pure (fun l s => loaded.getD (defaultConfigFor l s))
  let content ← IO.FS.readFile path
  let lines := content.splitOn "\n" |>.filter (fun line => !line.trimAscii.toString.isEmpty)
  let lines := match limit? with
    | none => lines
    | some limit => lines.take limit
  for line in lines do
    auditLine resolveConfig line
  return 0

unsafe def auditCmd := `[Cli|
  audit VIA runAuditCmd;
  "Classifies machine codes from a file using the first deciding decider."

  FLAGS:
    c, config: String; "Configuration of the deciders to run"
    l, limit: ℕ; "Maximum number of input lines to classify"

  ARGS:
    input: String; "File containing machine codes, optionally followed by prior output text"
]

unsafe def runExploreCmd (p: Parsed): IO UInt32 := do
  let ⟨l, s, M⟩ := p.positionalArg! "machine" |>.as! MParseRes
  let depth := p.positionalArg! "depth" |>.as! ℕ
  let output := p.positionalArg! "output" |>.as! String

  IO.println s!"Parsed machine with {l + 1} labels and {s + 1} symbols: {repr M}"

  let doc := TM.SpaceTime.generate depth M

  IO.FS.writeFile output (toString doc)

  return 0

unsafe def exploreCmd := `[Cli|
  explore VIA runExploreCmd;
  "Creates a space time diagram of the machine"

  ARGS:
    machine: String; "The machine code"
    depth: ℕ; "Depth to explore"
    output: String; "Path to write the output"
]

/-- Walk the TNF enumeration tree, emitting one tab-separated line per enumerated machine:

    `<code>\t<verdict>\t<steps>\t<deciderJson>`

where `verdict ∈ {halt, nonhalt, undecided}`, `steps` is the halting step count (`n+1`) for
halting machines and empty otherwise, and `deciderJson` is the compact JSON of the deciding
`DeciderConfig` (empty for holdouts). This is the source feed for the explorer database; the
DFS emission order is a stable enumeration ordinal. -/
unsafe def exportRec (cfg: List DeciderConfig) (M: Machine l s)
    (emit: String → IO Unit): IO Unit := do
  let code := s!"{repr M}"
  match firstDecisionFull? cfg M with
  | none => emit s!"{code}\tundecided\t\t"
  | some (d, res) =>
      let dj := (Lean.toJson d).compress
      match res with
      | .unknown _ => emit s!"{code}\tundecided\t\t"
      -- `.loops_prf` carries a `¬ halts` proof from any decider, not necessarily a periodicity
      -- proof, so the verdict is the honest "nonhalt" rather than "loop".
      | .loops_prf _ => emit s!"{code}\tnonhalt\t\t{dj}"
      | .halts_prf n C _ =>
          emit s!"{code}\thalt\t{n + 1}\t{dj}"
          -- Expand the halting transition only when other cells remain to be filled.
          if M.n_halting_trans > 1 then
            for M' in Quot.unquot (Busybeaver.next_machines M C.state C.tape.head).val do
              exportRec cfg M' emit

unsafe def runExportCmd (p: Parsed): IO UInt32 := do
  let l := (p.positionalArg! "nlabs" |>.as! ℕ) - 1
  let s := (p.positionalArg! "nsyms" |>.as! ℕ) - 1
  let output := p.positionalArg! "output" |>.as! String
  let cfg ← determineConfig l s ((p.flag? "config").map (Parsed.Flag.as! · String))

  IO.FS.withFile output IO.FS.Mode.write fun h => do
    Tqdm.withProgressBar (cfg := {}) fun pb => do
      pb.setDescription s!"enumerate {l + 1}×{s + 1}"
      -- `exportRec` calls `emit` exactly once per enumerated machine, so ticking here counts
      -- machines streamed.  The total is unknown up front, so this is a count-only bar.
      let emit (line: String): IO Unit := do
        h.putStrLn line
        pb.update
      if l = 0 then
        -- Single-state machines are trivial; emit the lone seed result.
        exportRec cfg (Busybeaver.BBCompute.m1RB l s) emit
      else
        exportRec cfg (Busybeaver.BBCompute.m0RB l s) emit
        exportRec cfg (Busybeaver.BBCompute.m1RB l s) emit
  return 0

unsafe def exportCmd := `[Cli|
  enumerate VIA runExportCmd;
  "Streams every TNF-enumerated machine with its verdict and deciding decider to a file."

  FLAGS:
    c, config: String; "Configuration of the deciders to run"

  ARGS:
    nlabs: ℕ; "Number of labels (states) for the machines"
    nsyms: ℕ; "Number of symbols for the machines"
    output: String; "Path to write the enumeration stream"
]

unsafe def computeCmd (p: Parsed): IO UInt32 := do
  let start ← IO.monoMsNow
  let l := (p.positionalArg! "nlabs" |>.as! ℕ) - 1
  let s := (p.positionalArg! "nsyms" |>.as! ℕ) - 1

  let cfg ← determineConfig l s ((p.flag? "config").map (Parsed.Flag.as! · String))
  let witnessPath := (p.flag? "witness").map (Parsed.Flag.as! · String) |>.getD "witness.db"

  -- `--trusted` (unverified cache) and `--verify` (certified compute) are mutually
  -- exclusive; reject the combination rather than silently letting one win.
  if p.hasFlag "trusted" && p.hasFlag "verify" then
    throw <| IO.userError "cannot combine --trusted with --verify"

  let printResult (lbl : String) (bbValue : Nat) (holdouts : Array String) : IO Unit := do
    if holdouts.isEmpty then
      IO.println s!"{lbl}Busybeaver({l + 1}, {s + 1}) = {bbValue}"
    else
      IO.println s!"{lbl}#Undec: {holdouts.size}"
      IO.println s!"{lbl}Busybeaver({l + 1}, {s + 1}) ≥ {bbValue}"

  if p.hasFlag "trusted" then
    -- Unverified fast path. Prefer the cached aggregate (one row → instant); only
    -- if this size was never generated do we walk the witness (self-healing).
    if l = 0 then
      IO.println s!"Busybeaver(1, {s+1}) = 1"
    else
      let store ← Witness.Store.openAt witnessPath
      match ← store.getResult? l s with
      | some (bbValue, _decided, holdouts) =>
          printResult "[trusted] " bbValue holdouts
      | none =>
          -- No cached aggregate: walk the witness, self-healing misses with the real
          -- deciders. Each `put` self-commits (no wrapping transaction) so a failure
          -- in one parallel task cannot roll back the others' self-healed rows.
          IO.println "[trusted] no cached result; walking witness (self-healing misses)…"
          let res ← Witness.walkRootsPar (l := l) (s := s)
            (fun M => trustedClassify store (emitClassify store cfg) M)
          store.putResult l s res.bbValue res.holdouts
          printResult "[trusted] " res.bbValue res.holdouts
  else if p.hasFlag "verify" then
    -- Certified path: the pure verified `compute`, with a live progress bar. The
    -- printed value carries the `correct_complete` certificate. No emission.
    let dec := toLogDecider cfg (p.hasFlag "quiet")
    if hl: l = 0 then
      have _: Busybeaver l s = 0 := by {
        rw [hl]
        exact Busybeaver.one_state
      }
      IO.println s!"Busybeaver(1, {s+1}) = 1"
    else
      IO.println "Starting verified computation"
      -- Run inside the progress-bar block (so it ticks live) and defer the result
      -- lines until after the bar closes — writing to stdout mid-bar desyncs the
      -- shared-terminal cursor from the bar manager's bookkeeping.
      let resultLines ← Tqdm.withProgressBar (cfg := {}) fun pb => do
        pb.setDescription s!"BB({l + 1}, {s + 1})"
        -- `tickDecider pb dec` is the identity `dec` to the kernel (proof unaffected) but
        -- advances `pb` once per visited machine when compiled.
        let comp := compute l s (tickDecider pb dec)
        if hcomp: comp.undec = ∅ then
          have _: comp.val = Busybeaver l s := by {
            simp [comp] at *
            simp [compute]
            exact Eq.symm (Busybeaver.BBCompute.correct_complete hl hcomp)
          }
          return #[s!"Busybeaver({l + 1}, {s + 1}) = {comp.val + 1}"]
        else
          if let some path := p.flag? "output" then
            save_to_file (path.as! String) comp.undec
          return #[s!"#Undec: {Multiset.card comp.undec}",
                   s!"Busybeaver({l + 1}, {s + 1}) ≥ {comp.val + 1}"]
      for line in resultLines do
        IO.println line
  else
    -- Default: generate the witness with a SINGLE parallel walk — deciders run
    -- once across all cores — then cache the aggregate so `--trusted` is instant.
    -- Unverified; use `--verify` for the certified value.
    if l = 0 then
      IO.println s!"Busybeaver(1, {s+1}) = 1"
    else
      IO.println "Generating witness (parallel)…"
      let store ← Witness.Store.openAt witnessPath
      -- One writer task owns the SQLite connection and drains a channel; the
      -- parallel walk's threads only `send` records, so writes overlap the
      -- deciders instead of serializing them.
      let chan : Std.CloseableChannel Witness.Record ← Std.CloseableChannel.new
      let writer ← IO.asTask (store.drainChannel chan)
      -- Close the channel and drain/await the writer even if the walk raises, so the
      -- writer task can't be left blocked on `recv` with an open transaction.
      let res ← do
        try
          Witness.walkRootsPar (l := l) (s := s) (fun M => emitClassifyChan chan cfg M)
        finally
          let _ ← (chan.close).toBaseIO
          let _ ← IO.ofExcept writer.get
      store.putResult l s res.bbValue res.holdouts
      printResult "" res.bbValue res.holdouts
      -- Only (re)write the holdout file when there ARE holdouts, matching `--verify`;
      -- otherwise a fully-decided run would truncate an existing --output file to empty.
      unless res.holdouts.isEmpty do
        if let some path := p.flag? "output" then
          IO.FS.writeFile (path.as! String) (String.intercalate "\n" res.holdouts.toList)
      IO.println s!"witness: {← store.count} machines → {witnessPath}"
  IO.println s!"In: {(← IO.monoMsNow) - start}ms"
  return 0

unsafe def mainCmd := `[Cli|
  beaver VIA computeCmd;
  "Runs the computation of a given BB value."

  FLAGS:
    c, config: String; "Configuration of the deciders to run"
    o, output: String; "Where to store the holdout list after execution"
    q, quiet; "Disable logging of holdouts during resolution"
    nt, "no-time"; "Don't print resolution time after execution"
    w, witness: String; "Path to the witness SQLite database (default: witness.db)"
    t, trusted; "Read the cached result from the witness DB (unverified, instant)"
    v, verify; "Run the pure verified computation (certified value, no witness emission)"

  ARGS:
    nlabs: ℕ; "Number of labels for the machines"
    nsyms: ℕ; "Number of symbols for the machines"

  SUBCOMMANDS:
    decideCmd;
    auditCmd;
    exploreCmd;
    exportCmd
]

unsafe def main (args: List String): IO UInt32 := do
  mainCmd.validate args
