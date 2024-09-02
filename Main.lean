import Busybeaver
import Busybeaver.Basic
import Busybeaver.Problem
import Busybeaver.Deciders.LooperDec
import Busybeaver.Deciders.BoundExplore
import Busybeaver.Deciders.NoHaltState
import Busybeaver.Enumerate.Alg

open TM
abbrev TM22 := Machine 1 1

def allDecs: (M: Machine l s) → HaltM M Unit := λ M ↦ do
  (looperDec 100 M)

instance [ToString α]: ToString (HaltM M α) where
  toString := λ r ↦ s!"{repr M} " ++ match r with
  | .unknown a => s!"unknown {a}"
  | .loops_prf _ => "loops"
  | .halts_prf n _ _ => s!"halts in {n + 1}"

def log_decs (M: Machine l s): HaltM M Unit := do
  let res := allDecs M;
  dbg_trace res;
  res

def compute (l s: ℕ): Busybeaver.BBResult l s :=
  let res0 := Task.spawn (λ _ ↦ (Busybeaver.BBCompute log_decs (Busybeaver.BBCompute.m0RB l s)))
  let res1 := Task.spawn (λ _ ↦ (Busybeaver.BBCompute log_decs (Busybeaver.BBCompute.m1RB l s)))
  Busybeaver.BBResult.join res0.get res1.get

axiom task_correct {α: Type} {f: Unit → α}: (Task.spawn f |>.get) = f ()

set_option compiler.extract_closed false
def main (args: List String): IO Unit := do
  match args with
  | [nlabs, nsyms] => {
    match nlabs.trim.toNat?, nsyms.trim.toNat? with
    | some nl, some ns => 
      IO.println "Starting computation"
      let l := nl - 1
      let s := ns - 1
      if hl: l = 0 then
        have _: Busybeaver l s = 0 := by {
          rw [hl]
          exact Busybeaver.one_state
        }
        IO.println s!"Busybeaver(1, {s+1}) = 1"
      else
        let comp := compute l s
        if hcomp: comp.undec = ∅ then
          have _: comp.val = Busybeaver l s := by {
            simp [comp] at *
            simp [compute, task_correct]
            exact Eq.symm (Busybeaver.BBCompute.correct_complete hcomp)
          }
          IO.println s!"Busybeaver({l + 1}, {s + 1}) = {comp.val + 1}"
        else
          IO.println s!"#Undecided: {comp.undec.card}"
          IO.println s!"Busybeaver({l + 1}, {s + 1}) ≥ {comp.val + 1}"
    | _, _ => IO.println "Invalid arguments, expected integers"
  }
  | _ => IO.println "Not enough arguments: beaver {nlabs} {nsyms}"
