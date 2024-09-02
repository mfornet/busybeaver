-- This module serves as the root of the `Busybeaver` library.
-- Import modules here that should be built as part of the library.
import Busybeaver.Basic
import Busybeaver.Reachability
import Busybeaver.ClosedSet
import Busybeaver.Enumerate.Symmetry

open TM

variable {l s: ℕ}

/- def filterWith (S: Finset (Machine l s)) (filter: (M: Machine l s) → HaltM M Unit): Finset (Machine l s) := -/
/-   S.filter $ λ m ↦ ¬(filter m |>.decided) -/
/- def BBcompute (S: Finset (Machine l s)) (filter: (M: Machine l s) → HaltM M α): BBResult l s := -/
/-   S.fold BBResult.join { val := 0, undec := {}} (λ M ↦ BBResult.from_haltm (filter M)) -/
