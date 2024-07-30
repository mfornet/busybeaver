import Busybeaver.Basic
import Busybeaver.Deciders.LooperDec
import Busybeaver.Deciders.BoundExplore

def main (args: List String): IO UInt32 := do
  for M in (Finset.univ (α:=TM.Machine 2 2)) do
    IO.println s!"{repr M}"
  return 0
