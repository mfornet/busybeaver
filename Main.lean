import Busybeaver

import Lean.Data.Json

import Cli

open TM

instance: ToString (HaltM M α) where
  toString := λ
  | .unknown _ => s!"unknown"
  | .loops_prf _ => "loops"
  | .halts_prf n _ _ => s!"halts in {n + 1}"

def compute (l s: ℕ) (dec: (M: Machine l s) → HaltM M Unit): Busybeaver.BBResult l s :=
  let res0 := Busybeaver.BBCompute dec (Busybeaver.BBCompute.m0RB l s)
  let res1 := Busybeaver.BBCompute dec (Busybeaver.BBCompute.m1RB l s)
  Busybeaver.BBResult.join res0 res1

section DeciderCombinator

open Lean

inductive DeciderConfig where
| translatedCycler : ℕ → DeciderConfig
| cycler : ℕ → DeciderConfig
| explore : ℕ → DeciderConfig
deriving FromJson, ToJson

instance: ToString DeciderConfig where
  toString := λ
  | .translatedCycler n => s!"Translated cycler {n}"
  | .cycler n => s!"Cycler {n}"
  | .explore n => s!"Explore {n}"

def DeciderConfig.decider (cfg: DeciderConfig) (M: Machine l s): HaltM M Unit := match cfg with
| .translatedCycler n => do let _ ← translatedCyclerDecider n M
| .cycler n => looperDecider n M
| .explore n => boundedExplore n M

@[inline]
def toDecider (cfg: List DeciderConfig) (M: Machine l s): HaltM M Unit := do
  for d in cfg do
    d.decider M

def toLogDecider (cfg: List DeciderConfig) (quiet: Bool) (M: Machine l s): HaltM M Unit := do
  let res := toDecider cfg M
  if !quiet && !res.decided then
    dbg_trace s!"{repr M} {res}"
  res

def configFromFile (path: String): IO (Option <| List DeciderConfig) := do
  let content ← IO.FS.readFile path
  let Except.ok parsed := Json.parse content | throw <| IO.userError "Invalid JSON"
  let .ok done := fromJson? parsed | throw <| IO.userError "Invalid configuration"
  return done

def defaultConfig: List DeciderConfig := [
  .translatedCycler 200,
  .cycler 100
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
  parse? str := match TM.Parse.pmachine str.iter with
    | .success _ M => some M
    | .error _ _ => none

def runCheckCmd (p: Parsed): IO UInt32 := do
  let ⟨l, s, M⟩ := p.positionalArg! "machine" |>.as! MParseRes

  IO.println s!"Parsed machine with {l + 1} labels and {s + 1} symbols: {repr M}"

  let cfg ← determineConfig ((p.flag? "config").map (Parsed.Flag.as! · String))

  for d in cfg do
    let res := d.decider M
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
