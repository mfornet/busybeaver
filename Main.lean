import Busybeaver
import Busybeaver.Basic
import Busybeaver.Problem
import Busybeaver.Deciders.Cyclers
import Busybeaver.Deciders.BoundExplore
import Busybeaver.Deciders.NoHaltState
import Busybeaver.Deciders.TranslatedCyclers
import Busybeaver.Enumerate.Alg

open TM
abbrev TM22 := Machine 1 1

def allDecs: (M: Machine l s) → HaltM M Unit := λ M ↦ do
  let _ ← (translatedCyclerDecider 200 M)
  (looperDecider 100 M)

instance [ToString α]: ToString (HaltM M α) where
  toString := λ r ↦ s!"{repr M} " ++ match r with
  | .unknown a => s!"unknown {a}"
  | .loops_prf _ => "loops"
  | .halts_prf n _ _ => s!"halts in {n + 1}"

def log_decs (M: Machine l s): HaltM M Unit := do
  let res := allDecs M;
  if ¬res.decided then
    dbg_trace res
  res

def compute (l s: ℕ): Busybeaver.BBResult l s :=
  let res0 := Task.spawn (λ _ ↦ (Busybeaver.BBCompute log_decs (Busybeaver.BBCompute.m0RB l s)))
  let res1 := Task.spawn (λ _ ↦ (Busybeaver.BBCompute log_decs (Busybeaver.BBCompute.m1RB l s)))
  Busybeaver.BBResult.join res0.get res1.get

axiom task_correct {α: Type} {f: Unit → α}: (Task.spawn f |>.get) = f ()

unsafe def save_to_file (path: String) (set: Multiset (Machine l s)): IO Unit :=
  IO.FS.withFile path IO.FS.Mode.write (λ file ↦ do
    for M in Quot.unquot set do
      file.putStrLn s!"{repr M}")

set_option compiler.extract_closed false
unsafe def main (args: List String): IO Unit := do
  match args with
  | nlabs :: nsyms :: rest => {
    match nlabs.trim.toNat?, nsyms.trim.toNat? with
    | some nl, some ns => 
      let start ← IO.monoMsNow
      let l := nl - 1
      let s := ns - 1
      if hl: l = 0 then
        have _: Busybeaver l s = 0 := by {
          rw [hl]
          exact Busybeaver.one_state
        }
        IO.println s!"Busybeaver(1, {s+1}) = 1"
      else
        IO.println "Starting computation"
        let comp := compute l s
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
          if hr: rest ≠ [] then
            save_to_file (rest.head hr) comp.undec
      IO.println s!"In: {(← IO.monoMsNow) - start}ms"
    | _, _ => IO.println "Invalid arguments, expected integers"
  }
  | _ => IO.println "Not enough arguments: beaver {nlabs} {nsyms}"
