import Busybeaver.Basic
import Busybeaver.Reachability

open TM

def nGramCPSDecider (_bound : ℕ) (M : Machine l s) : HaltM M Unit :=
  .unknown ()
