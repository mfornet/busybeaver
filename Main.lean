-- TODO: Simplify this import (don't use everything)
import Busybeaver
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
    simpa using tableMultistep_to_modelMultistep hReach⟩

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
-- a tabular machine is actually a model, and all its relevant API.
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

def compute (l s: ℕ) (dec: (M: Machine l s) → TM.Model.HaltM M Unit): Busybeaver.BBResult l s :=
  let tableDec := fun M => modelHaltMToTableHaltM (dec M)
  let res0 := Busybeaver.BBCompute tableDec (Busybeaver.BBCompute.m0RB l s)
  let res1 := Busybeaver.BBCompute tableDec (Busybeaver.BBCompute.m1RB l s)
  Busybeaver.BBResult.join res0 res1

section DeciderCombinator

open Lean

deriving instance FromJson, ToJson for NGramCPSConfig

inductive DeciderConfig where
| translatedCycler : ℕ → DeciderConfig
| cycler : ℕ → DeciderConfig
| explore : ℕ → DeciderConfig
| backwardsReasoning : ℕ → DeciderConfig
| nGramCPS : NGramCPSConfig → DeciderConfig
deriving FromJson, ToJson

instance: ToString DeciderConfig where
  toString := λ
  | .translatedCycler n => s!"Translated cycler {n}"
  | .cycler n => s!"Cycler {n}"
  | .explore n => s!"Explore {n}"
  | .backwardsReasoning n => s!"Backwards Reasoning {n}"
  | .nGramCPS cfg => s!"NGram CPS n={cfg.n} bound={cfg.bound}"

def DeciderConfig.deciderModel {M : Type _} [TM.Model M] (cfg: DeciderConfig) (m : M) :
    TM.Model.HaltM m Unit := match cfg with
| .translatedCycler n => do
    let _ ← Deciders.TranslatedCyclers.translatedCyclerDecider n m
| .explore n => do
    let _ ← Deciders.BoundExplore.boundedExplore n m
| .cycler n => Deciders.Cyclers.looperDecider n m
| _ => .unknown ()

@[inline]
def toDecider (cfg: List DeciderConfig) (M: Machine l s): TM.Model.HaltM M Unit := do
  for d in cfg do
    d.deciderModel M

def toLogDecider (cfg: List DeciderConfig) (quiet: Bool) (M: Machine l s): TM.Model.HaltM M Unit := do
  let res := toDecider cfg M
  if !quiet && !TM.Model.HaltM.decided res then
    dbg_trace s!"{repr M} {res}"
  res

def configFromFile (path: String): IO (Option <| List DeciderConfig) := do
  let content ← IO.FS.readFile path
  let Except.ok parsed := Json.parse content | throw <| IO.userError "Invalid JSON"
  let .ok done := fromJson? parsed | throw <| IO.userError "Invalid configuration"
  return done

def defaultConfig: List DeciderConfig := [
  .explore 100,
  .translatedCycler 300,
  .cycler 300,
  .backwardsReasoning 30,
  .nGramCPS { n := 1, bound := 10000 }
]

def determineConfig: (Option String) → IO (List DeciderConfig)
| none => pure defaultConfig
| some path => do
    return match (← configFromFile path) with
    | none => defaultConfig
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

def runCheckCmd (p: Parsed): IO UInt32 := do
  let ⟨l, s, M⟩ := p.positionalArg! "machine" |>.as! MParseRes

  IO.println s!"Parsed machine with {l + 1} labels and {s + 1} symbols: {repr M}"

  let cfg ← determineConfig ((p.flag? "config").map (Parsed.Flag.as! · String))

  for d in cfg do
    let res := d.deciderModel M
    IO.println s!"{d}: {res}"

  return 0

unsafe def checkCmd := `[Cli|
  decide VIA runCheckCmd;
  "Runs the deciders on the provided machine."

  FLAGS:
    c, config: String; "Configuration of the deciders to run"

  ARGS:
    machine: String; "The machine code"
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

  let cfg ← determineConfig ((p.flag? "config").map (Parsed.Flag.as! · String))
  let dec := toLogDecider cfg (p.hasFlag "quiet")

  if hl: l = 0 then
    have _: Busybeaver l s = 0 := by {
      rw [hl]
      exact Busybeaver.one_state
    }
    IO.println s!"Busybeaver(1, {s+1}) = 1"
  else
    IO.println "Starting computation"
    let comp := compute l s dec
    if hcomp: comp.undec = ∅ then
      have _: comp.val = Busybeaver l s := by {
        simp [comp] at *
        simp [compute]
        exact Eq.symm (Busybeaver.BBCompute.correct_complete hl hcomp)
      }
      IO.println s!"Busybeaver({l + 1}, {s + 1}) = {comp.val + 1}"
    else
      -- TODO: check BB(l,s) ≥ n
      IO.println s!"#Undec: {Multiset.card comp.undec}"
      IO.println s!"Busybeaver({l + 1}, {s + 1}) ≥ {comp.val + 1}"
      if let some path := p.flag? "output" then
        save_to_file (path.as! String) comp.undec
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

  ARGS:
    nlabs: ℕ; "Number of labels for the machines"
    nsyms: ℕ; "Number of symbols for the machines"

  SUBCOMMANDS:
    checkCmd;
    exploreCmd
]

unsafe def main (args: List String): IO UInt32 := do
  mainCmd.validate args
