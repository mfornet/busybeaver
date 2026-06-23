import Busybeaver
import Witness
import Mathlib.Data.Nat.Notation
import Init.Data.String

import Lean.Data.Json

import Cli

open TM TM.Table

instance: ToString (HaltM M α) where
  toString := λ
  | .unknown _ => s!"unknown"
  | .loops_prf _ => "loops"
  | .halts_prf n _ _ => s!"halts in {n + 1}"

instance {M : Type _} [TM.Model M] {m : M} : ToString (TM.Model.HaltM m α) where
  toString := λ
  | .unknown _ => s!"unknown"
  | .loops_prf _ => "loops"
  | .halts_prf n _ _ => s!"halts in {n + 1}"

private lemma modelStepBase_to_tableStep
    {l s : ℕ} {M : Machine l s}
    {n : ℕ} {A B : TM.Model.Config (Machine l s)}
    (h : TM.Model.StepBase M n A B) :
    n = 1 ∧ (⟨A.state, A.tape⟩ : Config l s) -[M]-> (⟨B.state, B.tape⟩ : Config l s) := by
  unfold TM.Model.StepBase at h
  cases hget : M.get A.state A.tape.head with
  | halt =>
      simp [TM.Model.step, hget] at h
  | next sym dir state =>
      simp [TM.Model.step, hget] at h
      rcases h with ⟨rfl, rfl⟩
      constructor
      · rfl
      · simp [Machine.step, hget]

private lemma modelLastState_to_tableLastState
    {l s : ℕ} {M : Machine l s}
    {C : TM.Model.Config (Machine l s)}
    (h : TM.Model.LastState M C) :
    M.LastState (⟨C.state, C.tape⟩ : Config l s) := by
  cases hget : M.get C.state C.tape.head with
  | halt =>
      simp [Machine.LastState, Machine.step, hget]
  | next sym dir state =>
      simp [TM.Model.LastState, TM.Model.step, hget] at h

private lemma tableLastState_to_modelLastState
    {l s : ℕ} {M : Machine l s}
    {C : Config l s}
    (h : M.LastState C) :
    TM.Model.LastState M ({ state := C.state, tape := C.tape } : TM.Model.Config (Machine l s)) := by
  cases hget : M.get C.state C.tape.head with
  | halt =>
      simp [Machine.LastState, Machine.step, hget] at h
      simp [TM.Model.LastState, TM.Model.step, hget]
  | next sym dir state =>
      simp [Machine.LastState, Machine.step, hget] at h

private lemma tableStep_to_modelStep
    {l s : ℕ} {M : Machine l s}
    {A B : Config l s}
    (h : A -[M]-> B) :
    ({ state := A.state, tape := A.tape } : TM.Model.Config (Machine l s))
      -[M]->'
    ({ state := B.state, tape := B.tape } : TM.Model.Config (Machine l s)) := by
  cases hget : M.get A.state A.tape.head with
  | halt =>
      simp [Machine.step, hget] at h
  | next sym dir state =>
      simp [Machine.step, hget] at h
      rcases h with rfl
      simp [TM.Model.Step, TM.Model.step, hget]

private lemma tableMultistep_to_modelMultistep
    {l s : ℕ} {M : Machine l s}
    {n : ℕ} {A B : Config l s}
    (h : A -[M]{n}-> B) :
    ({ state := A.state, tape := A.tape } : TM.Model.Config (Machine l s))
      -[M]{n}->'
    ({ state := B.state, tape := B.tape } : TM.Model.Config (Machine l s)) := by
  induction h with
  | refl =>
      exact .refl
  | succ hAB hBC IH =>
      exact .step (tableStep_to_modelStep hAB) IH

private lemma tableHalts_to_modelHalts
    {l s : ℕ} {M : Machine l s}
    (h : M.halts (init : Config l s)) :
    TM.Model.halts M (default : TM.Model.Config (Machine l s)) := by
  rcases h with ⟨n, C, hLast, hReach⟩
  exact ⟨n, ({ state := C.state, tape := C.tape } : TM.Model.Config (Machine l s)),
    tableLastState_to_modelLastState hLast, by
    exact tableMultistep_to_modelMultistep hReach⟩

private lemma modelMultistepBase_to_tableMultistep
    {l s : ℕ} {M : Machine l s}
    {n : ℕ} {A B : TM.Model.Config (Machine l s)}
    (h : A -[M]{n}->>' B) :
    (⟨A.state, A.tape⟩ : Config l s) -[M]{n}-> (⟨B.state, B.tape⟩ : Config l s) := by
  induction h with
  | refl =>
      exact .refl
  | step hAB hBC IH =>
      obtain ⟨hn, hAB'⟩ := modelStepBase_to_tableStep hAB
      cases hn
      simpa [Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using Machine.Multistep.succ hAB' IH

-- TODO: Move this proof and its dependencies to TM.Table.Model, it is about explaining how
--       a tabular machine is actually a model, and all its relevant API.
private def modelHaltMToTableHaltM
    {l s : ℕ} {M : Machine l s} :
    TM.Model.HaltM M Unit → HaltM M Unit
  | .unknown _ => .unknown ()
  | .halts_prf n C h =>
      .halts_prf n ⟨C.state, C.tape⟩ <| by
        rcases h with ⟨hLast, hReach⟩
        constructor
        · exact modelLastState_to_tableLastState hLast
        · exact modelMultistepBase_to_tableMultistep hReach
  | .loops_prf h =>
      .loops_prf (by
        intro hhalts
        exact h (tableHalts_to_modelHalts hhalts))

def compute (l s: ℕ) (dec: (M: Machine l s) → HaltM M Unit): Busybeaver.BBResult l s :=
  let res0 := Busybeaver.BBCompute dec (Busybeaver.BBCompute.m0RB l s)
  let res1 := Busybeaver.BBCompute dec (Busybeaver.BBCompute.m1RB l s)
  Busybeaver.BBResult.join res0 res1

section DeciderCombinator

open Lean

deriving instance FromJson, ToJson for NGramCPSConfig
deriving instance FromJson, ToJson for NGramCPSHistoryConfig
deriving instance FromJson, ToJson for NGramCPSLRUConfig
deriving instance FromJson, ToJson for RepWLConfig

inductive DeciderConfig where
| translatedCycler : ℕ → DeciderConfig
| cycler : ℕ → DeciderConfig
| explore : ℕ → DeciderConfig
| loop1 : ℕ → DeciderConfig
| backwardsReasoning : ℕ → DeciderConfig
| nGramCPS : NGramCPSConfig → DeciderConfig
| nGramCPSHistory : NGramCPSHistoryConfig → DeciderConfig
| nGramCPSLRU : NGramCPSLRUConfig → DeciderConfig
| repWL : RepWLConfig → DeciderConfig
| bb5TableExecutable : DeciderConfig
| bb5TableAll : DeciderConfig
deriving FromJson, ToJson

instance: ToString DeciderConfig where
  toString := λ
  | .translatedCycler n => s!"Translated cycler {n}"
  | .cycler n => s!"Cycler {n}"
  | .explore n => s!"Explore {n}"
  | .loop1 n => s!"Loop1 {n}"
  | .backwardsReasoning n => s!"Backwards Reasoning {n}"
  | .nGramCPS cfg => s!"NGram CPS n={cfg.n} bound={cfg.bound}"
  | .nGramCPSHistory cfg =>
      s!"NGram CPS history={cfg.history} left={cfg.left} right={cfg.right} bound={cfg.bound}"
  | .nGramCPSLRU cfg =>
      s!"NGram CPS LRU left={cfg.left} right={cfg.right} bound={cfg.bound}"
  | .repWL cfg =>
      s!"RepWL len={cfg.len} threshold={cfg.threshold} maxT={cfg.maxT} bound={cfg.bound}"
  | .bb5TableExecutable => "BB5 executable hardcoded table"
  | .bb5TableAll => "BB5 full hardcoded table"

def DeciderConfig.deciderModel {M : Type _} [TM.Model M] (cfg: DeciderConfig) (m : M) :
    TM.Model.HaltM m Unit := match cfg with
| .translatedCycler n => do
    let _ ← Deciders.TranslatedCyclers.translatedCyclerDecider n m
| .explore n => do
    let _ ← Deciders.BoundExplore.boundedExplore n m
| .cycler n => Deciders.Cyclers.looperDecider n m
| _ => .unknown ()

def runBB5Table (table : Deciders.BB5Table.Table) (M : Machine l s) : HaltM M Unit :=
  match l, s with
  | 4, 1 => Deciders.BB5Table.tableDecider table M
  | _, _ => .unknown ()

def DeciderConfig.deciderTable (cfg: DeciderConfig) (M: Machine l s) : HaltM M Unit := match cfg with
| .backwardsReasoning n => backwardsReasoningDecider n M
| .nGramCPS cfg => nGramCPSDecider cfg M
| .nGramCPSHistory cfg => nGramCPSHistoryDecider cfg M
| .nGramCPSLRU cfg => nGramCPSLRUDecider cfg M
| .repWL cfg => Deciders.RepWL.decider cfg M
| .loop1 n => Deciders.Loop1.decider n M
| .bb5TableExecutable => runBB5Table Deciders.BB5Table.Generated.executableTable M
| .bb5TableAll => runBB5Table Deciders.BB5Table.Generated.allTable M
| _ => modelHaltMToTableHaltM (cfg.deciderModel M)

@[inline]
def toDecider (cfg: List DeciderConfig) (M: Machine l s): TM.Model.HaltM M Unit := do
  for d in cfg do
    d.deciderModel M

@[inline]
def toTableDecider (cfg: List DeciderConfig) (M: Machine l s): HaltM M Unit := do
  for d in cfg do
    d.deciderTable M

def toLogDecider (cfg: List DeciderConfig) (quiet: Bool) (M: Machine l s): HaltM M Unit := do
  let res := toTableDecider cfg M
  if !quiet && !HaltM.decided res then
    dbg_trace s!"{repr M} {res}"
  res

def firstDecision?: List DeciderConfig → (M: Machine l s) → Option (String × String)
| [], _ => none
| d :: ds, M =>
    let res := d.deciderTable M
    if HaltM.decided res then
      some (toString d, toString res)
    else
      firstDecision? ds M

/-- Like `firstDecision?` but keeps the proof-carrying `HaltM` alongside the name
of the decider that settled it (or `.unknown`/`none` if none did). Used to emit
witness records with provenance. -/
def decideWithProvenance: List DeciderConfig → (M: Machine l s) → (HaltM M Unit × Option String)
| [], _ => (.unknown (), none)
| d :: ds, M =>
    let res := d.deciderTable M
    if HaltM.decided res then (res, some (toString d))
    else decideWithProvenance ds M

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
  let _ ← chan.send rec
  return outcome

/-- Trusted-mode classifier: read `M`'s outcome from the store. On a miss, fall
back to `fallback` (typically `emitClassify`, which also self-heals the DB). -/
def trustedClassify (store: Witness.Store) (fallback: Machine l s → IO Witness.Outcome)
    (M: Machine l s): IO Witness.Outcome := do
  match ← store.get? (reprStr M) with
  | some rec =>
      match rec.kind with
      | .halt => return .halt (rec.haltState.getD 0) (rec.haltSymbol.getD 0) (rec.haltSteps.getD 0)
      | .nonhalt => return .nonhalt
      | .unknown => return .unknown
  | none => fallback M

def configFromFile (path: String): IO (Option <| List DeciderConfig) := do
  let content ← IO.FS.readFile path
  let Except.ok parsed := Json.parse content | throw <| IO.userError "Invalid JSON"
  let .ok done := fromJson? parsed | throw <| IO.userError "Invalid configuration"
  return done

def lightDefaultConfig: List DeciderConfig := [
  .explore 130,
  .translatedCycler 300,
  .cycler 300,
  .nGramCPS { n := 1, bound := 100 },
  .nGramCPS { n := 2, bound := 200 },
  .nGramCPS { n := 3, bound := 400 }
]

def bb3DefaultConfig: List DeciderConfig :=
  lightDefaultConfig ++ [
    .nGramCPSHistory { history := 2, left := 2, right := 2, bound := 1600 }
  ]

def bb4DefaultConfig: List DeciderConfig := [
  .cycler 107,
  .nGramCPS { n := 1, bound := 100 },
  .nGramCPS { n := 2, bound := 200 },
  .nGramCPS { n := 3, bound := 400 },
  .nGramCPSHistory { history := 2, left := 3, right := 3, bound := 1600 },
  .nGramCPSHistory { history := 4, left := 3, right := 3, bound := 1600 },
  .nGramCPSHistory { history := 6, left := 3, right := 3, bound := 3200 },
  .nGramCPSHistory { history := 8, left := 3, right := 3, bound := 1600 },
  .nGramCPSHistory { history := 10, left := 4, right := 4, bound := 10000 },
  .repWL { len := 2, threshold := 3, maxT := 320, bound := 2000 },
  .repWL { len := 4, threshold := 3, maxT := 320, bound := 2000 }
]

def bb5DefaultConfig: List DeciderConfig := [
  .explore 130,
  .loop1 107,
  .nGramCPS { n := 1, bound := 400 },
  .nGramCPS { n := 2, bound := 800 },
  .nGramCPS { n := 3, bound := 400 },
  .nGramCPS { n := 4, bound := 800 },
  .explore 4100,
  .loop1 4100,
  .bb5TableExecutable,
  .repWL { len := 2, threshold := 3, maxT := 320, bound := 400 },
  .nGramCPSLRU { left := 2, right := 2, bound := 1000 },
  .nGramCPSHistory { history := 2, left := 2, right := 2, bound := 3000 },
  .nGramCPSHistory { history := 2, left := 3, right := 3, bound := 1600 },
  .nGramCPSHistory { history := 4, left := 2, right := 2, bound := 600 },
  .nGramCPSHistory { history := 4, left := 3, right := 3, bound := 1600 },
  .nGramCPSHistory { history := 6, left := 2, right := 2, bound := 3200 },
  .nGramCPSHistory { history := 6, left := 3, right := 3, bound := 3200 },
  .nGramCPSHistory { history := 8, left := 3, right := 3, bound := 1600 },
  .nGramCPSLRU { left := 3, right := 3, bound := 20000 },
  .repWL { len := 4, threshold := 2, maxT := 320, bound := 2000 },
  .repWL { len := 6, threshold := 2, maxT := 320, bound := 2000 },
  .nGramCPS { n := 4, bound := 20000 }
]

def defaultConfigFor (l s : ℕ) : List DeciderConfig :=
  if l = 2 && s = 1 then
    bb3DefaultConfig
  else if l = 3 && s = 1 then
    bb4DefaultConfig
  else if l = 4 && s = 1 then
    bb5DefaultConfig
  else
    lightDefaultConfig

def determineConfig (l s : ℕ): (Option String) → IO (List DeciderConfig)
| none => pure (defaultConfigFor l s)
| some path => do
    return match (← configFromFile path) with
    | none => defaultConfigFor l s
    | some cfg => cfg

end DeciderCombinator

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

unsafe def computeCmd (p: Parsed): IO UInt32 := do
  let start ← IO.monoMsNow
  let l := (p.positionalArg! "nlabs" |>.as! ℕ) - 1
  let s := (p.positionalArg! "nsyms" |>.as! ℕ) - 1

  let cfg ← determineConfig l s ((p.flag? "config").map (Parsed.Flag.as! · String))
  let witnessPath := (p.flag? "witness").map (Parsed.Flag.as! · String) |>.getD "witness.db"

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
          IO.println "[trusted] no cached result; walking witness (self-healing misses)…"
          let res ← store.runTransaction
            (Witness.walkRootsPar (l := l) (s := s)
              (fun M => trustedClassify store (emitClassify store cfg) M))
          store.putResult l s res.bbValue res.holdouts
          printResult "[trusted] " res.bbValue res.holdouts
  else if p.hasFlag "verify" then
    -- Certified path: the pure verified `compute`. The printed value carries the
    -- `correct_complete` certificate. No emission.
    let dec := toLogDecider cfg (p.hasFlag "quiet")
    if hl: l = 0 then
      have _: Busybeaver l s = 0 := by {
        rw [hl]
        exact Busybeaver.one_state
      }
      IO.println s!"Busybeaver(1, {s+1}) = 1"
    else
      IO.println "Starting verified computation"
      let comp := compute l s dec
      if hcomp: comp.undec = ∅ then
        have _: comp.val = Busybeaver l s := by {
          simp [comp] at *
          simp [compute]
          exact Eq.symm (Busybeaver.BBCompute.correct_complete hl hcomp)
        }
        IO.println s!"Busybeaver({l + 1}, {s + 1}) = {comp.val + 1}"
      else
        IO.println s!"#Undec: {Multiset.card comp.undec}"
        IO.println s!"Busybeaver({l + 1}, {s + 1}) ≥ {comp.val + 1}"
        if let some path := p.flag? "output" then
          save_to_file (path.as! String) comp.undec
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
      let res ← Witness.walkRootsPar (l := l) (s := s) (fun M => emitClassifyChan chan cfg M)
      let _ ← (chan.close).toBaseIO
      let _ ← IO.ofExcept writer.get
      store.putResult l s res.bbValue res.holdouts
      printResult "" res.bbValue res.holdouts
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
    exploreCmd
]

unsafe def main (args: List String): IO UInt32 := do
  mainCmd.validate args
