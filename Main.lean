import Busybeaver
import Busybeaver.Basic
import Busybeaver.Deciders.LooperDec
import Busybeaver.Deciders.BoundExplore
import Busybeaver.Deciders.NoHaltState

open TM
abbrev TM22 := Machine 1 1

def allDecs: (M: TM22) → HaltM M Unit := λ M ↦ do
  noHaltDec M
  (looperDec 20 M)

def all22 := (Finset.univ (α:=TM22)).filter (λ M ↦ M default default = .next 1 .right 1)

set_option compiler.extract_closed false
def main : IO Unit := do
  IO.println "Compute initial set";
  let init := all22;
  IO.println "Done";
  IO.println s!"N elems: {init.card}"
  IO.println "Filter";
  let res := (BBcompute init allDecs);
  IO.println s!"Max: {res.val}";
  IO.println s!"Undec: {res.undec.card}"
