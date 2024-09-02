import Busybeaver
import Busybeaver.Basic
import Busybeaver.Problem
import Busybeaver.Deciders.LooperDec
import Busybeaver.Deciders.BoundExplore
import Busybeaver.Deciders.NoHaltState

open TM
abbrev TM22 := Machine 1 1

def allDecs: (M: Machine l s) → HaltM M Unit := λ M ↦ do
  noHaltDec M
  (looperDec 20 M)

/- #eval .undec -/

def compute (l s: ℕ): Busybeaver.BBResult l s :=
  let res0 := Task.spawn (λ _ ↦ (Busybeaver.BBCompute allDecs (Busybeaver.BBCompute.m0RB l s)))
  let res1 := Task.spawn (λ _ ↦ (Busybeaver.BBCompute allDecs (Busybeaver.BBCompute.m1RB l s)))
  Busybeaver.BBResult.join res0.get res1.get
/- def all22 := (Finset.univ (α:=TM22)).filter (λ M ↦ M default default = .next 1 .right 1) -/

axiom task_correct {α: Type} {f: Unit → α}: (Task.spawn f |>.get) = f ()

set_option compiler.extract_closed false
def main: IO Unit := do
  IO.println "Starting computation"
  let comp := compute 1 3
  if hcomp: comp.undec = ∅ then
    have _: comp.val = Busybeaver 1 3 := by {
      simp [comp] at *
      simp [compute, task_correct]
      exact Eq.symm (Busybeaver.BBCompute.correct_complete hcomp)
    }
    IO.println s!"Busybeaver = {comp.val}"
  else
    IO.println s!"#Undecided: {comp.undec.card}"

/- def main : IO Unit := do -/
/-   IO.println "Compute initial set"; -/
/-   let init := all22; -/
/-   IO.println "Done"; -/
/-   IO.println s!"N elems: {init.card}" -/
/-   IO.println "Filter"; -/
/-   let res := (BBcompute init allDecs); -/
/-   IO.println s!"Max: {res.val}"; -/
/-   IO.println s!"Undec: {res.undec.card}" -/
