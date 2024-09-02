import Busybeaver
import Busybeaver.Basic
import Busybeaver.Deciders.LooperDec
import Busybeaver.Deciders.BoundExplore
import Busybeaver.Deciders.NoHaltState

def main (_args: List String): IO UInt32 := do
  IO.println "Hewo"
  return 0

open TM

abbrev TM22 := Machine 1 1

def all22 := Finset.univ (α:=TM22)
#eval all22.card

def withHalt := filterWith all22 noHaltDec
#eval withHalt.card

def long22 := filterWith withHalt (looperDec 100)
#eval long22.card
