import Busybeaver.Basic
import Busybeaver.Reachability
import Busybeaver.Enumerate.ZVisits
import Busybeaver.Enumerate.Symmetry

namespace TM

/--
In the end, this will become: if we have a TNF decider, then it decides all machines
-/
theorem reduce {M: Machine l s} (decider: ∀ (M': Machine l s) (q': Label l), (∃sym nlab, M' q' default = .next sym .right nlab ∧ sym ≠ default) → M'.halts ⟨q', default⟩ ∨ ¬M'.halts ⟨q', default⟩): M.halts ⟨q, default⟩ ∨ ¬M.halts ⟨q, default⟩ :=
by {
  apply Machine.ZVisits.only_nz
  intro M' ⟨sym, dir, nlab, hM'⟩

  refine Machine.only_right ?_ hM'.1 hM'.2
  exact decider
}
