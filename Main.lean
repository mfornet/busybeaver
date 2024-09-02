import Busybeaver
import Busybeaver.Basic
import Busybeaver.Deciders.LooperDec
import Busybeaver.Deciders.BoundExplore
import Busybeaver.Deciders.NoHaltState

#print List.toArray

open TM
abbrev TM22 := Machine 2 1

def allDecs: (M: TM22) → HaltM M Unit := λ M ↦ do
  noHaltDec M
  (looperDec 20 M)

def all22 := (Finset.univ (α:=TM22)).filter (λ M ↦ M default default = .next 1 .right 1)

def main: IO Unit := do
  IO.println "Compute initial set"
  let init := all22
  IO.println "Filter"
  let res := (Busybeaver init allDecs)
  IO.println s!"Max: {res.1}"
  IO.println s!"Undecided: {res.2.card}"
