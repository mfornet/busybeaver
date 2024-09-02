-- This module serves as the root of the `Busybeaver` library.
-- Import modules here that should be built as part of the library.
import Busybeaver.Basic
import Busybeaver.Reachability

open TM

variable {l s: ℕ}

def filterWith (S: Finset (Machine l s)) (filter: (M: Machine l s) → HaltM M Unit): Finset (Machine l s) :=
  S.filter $ λ m ↦ ¬(filter m |>.decided)
