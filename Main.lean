import Busybeaver
import Busybeaver.Basic
import Busybeaver.Problem
import Busybeaver.Deciders.Cyclers
import Busybeaver.Deciders.BoundExplore
import Busybeaver.Deciders.NoHaltState
import Busybeaver.Deciders.TranslatedCyclers
import Busybeaver.Enumerate.Alg
import Busybeaver.Parse

import Lean.Data.Json

import Cli

open TM
abbrev TM22 := Machine 1 1

instance: ToString (HaltM M α) where
  toString := λ
  | .unknown _ => s!"unknown"
  | .loops_prf _ => "loops"
  | .halts_prf n _ _ => s!"halts in {n + 1}"

def allDecs: (M: Machine l s) → HaltM M Unit := λ M ↦ do
  let _ ← (translatedCyclerDecider 200 M)
  (looperDecider 100 M)

def defaultDec (quiet: Bool) (M: Machine l s): HaltM M Unit := do
  let res := allDecs M;
  if ¬res.decided && ¬quiet then
    dbg_trace s!"{repr M} {res}"
  res

def compute (l s: ℕ) (dec: (M: Machine l s) → HaltM M Unit): Busybeaver.BBResult l s :=
  let res0 := Task.spawn (λ _ ↦ (Busybeaver.BBCompute dec (Busybeaver.BBCompute.m0RB l s)))
  let res1 := Task.spawn (λ _ ↦ (Busybeaver.BBCompute dec (Busybeaver.BBCompute.m1RB l s)))
  Busybeaver.BBResult.join res0.get res1.get

axiom task_correct {α: Type} {f: Unit → α}: (Task.spawn f |>.get) = f ()

section DeciderCombinator

open Lean

inductive DeciderConfig where
| translatedCycler : ℕ → DeciderConfig
| cycler : ℕ → DeciderConfig
deriving FromJson, ToJson

def DeciderConfig.decider (cfg: DeciderConfig) (M: Machine l s): HaltM M Unit := match cfg with
| .translatedCycler n => do let _ ← translatedCyclerDecider n M
| .cycler n => looperDecider n M

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

end DeciderCombinator

section Cli

open Cli

unsafe def save_to_file (path: String) (set: Multiset (Machine l s)): IO Unit :=
  IO.FS.withFile path IO.FS.Mode.write (λ file ↦ do
    for M in Quot.unquot set do
      file.putStrLn s!"{repr M}")

instance: ParseableType (Machine l s) where
  name := s!"Machine {l + 1} {s + 1}"
  parse? str := match TM.Parse.pmachine l s str.iter with
    | .success _ M => some M
    | .error _ _ => none

def runCheckCmd (p: Parsed): IO UInt32 := do
  let l := (p.positionalArg! "nlabs" |>.as! ℕ) - 1
  let s := (p.positionalArg! "nsyms" |>.as! ℕ) - 1
  let M : Machine l s := p.positionalArg! "machine" |>.as! (Machine l s)

  if let some n := p.flag? "translated-cycler" then
    let n := n.as! ℕ
    IO.println s!"Translated cycler {n}: {(translatedCyclerDecider n M)}"

  if let some n := p.flag? "cycler" then
    let n := n.as! ℕ
    IO.println s!"Cycler {n}: {(translatedCyclerDecider n M)}"
  return 0

unsafe def checkCmd := `[Cli|
  decide VIA runCheckCmd;
  "Runs the deciders on the provided machine."

  FLAGS:
    tc, "translated-cycler": ℕ; "Run the translated cycler decider with this parameter"
    c, "cycler": ℕ; "Run the cycler decider with this parameter"

  ARGS:
    nlabs: ℕ; "Number of labels for the machines"
    nsyms: ℕ; "Number of symbols for the machines"
    machine: String; "The machine code"
]

unsafe def computeCmd (p: Parsed): IO UInt32 := do
  let start ← IO.monoMsNow
  let l := (p.positionalArg! "nlabs" |>.as! ℕ) - 1
  let s := (p.positionalArg! "nsyms" |>.as! ℕ) - 1

  let dec ← if let some path := p.flag? "config" then
    match (← configFromFile (path.as! String)) with
    | some dec => pure <| toLogDecider dec
    | none => pure <| defaultDec
  else
    pure <| defaultDec

  if hl: l = 0 then
    have _: Busybeaver l s = 0 := by {
      rw [hl]
      exact Busybeaver.one_state
    }
    IO.println s!"Busybeaver(1, {s+1}) = 1"
  else
    IO.println "Starting computation"
    let comp := compute l s (dec <| p.hasFlag "quiet")
    if hcomp: comp.undec = ∅ then
      have _: comp.val = Busybeaver l s := by {
        simp [comp] at *
        simp [compute, task_correct]
        exact Eq.symm (Busybeaver.BBCompute.correct_complete hcomp)
      }
      IO.println s!"Busybeaver({l + 1}, {s + 1}) = {comp.val + 1}"
    else
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
    checkCmd
]

unsafe def main (args: List String): IO UInt32 := do
  mainCmd.validate args
