import Busybeaver.Basic
import Busybeaver.Enumerate.Basic

namespace TM.Machine

def halting_states (M: Machine l s) := (Finset.univ (α:=Label l × Symbol s)).filter (λ pair ↦ M pair.1 pair.2 = .halt)
