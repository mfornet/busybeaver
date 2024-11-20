import Busybeaver.Basic
import Busybeaver.Reachability
import Busybeaver.Enumerate.Basic

namespace TM.Machine

variable {M: Machine l s}

def perm (M: Machine l s) (q q': Label l): Machine l s :=
  M.map' <| λ lab sym _ ↦ match M.get (swap q q' lab) sym with
    | .halt => .halt
    | .next sym dir nlab => .next sym dir (swap q q' nlab)

namespace perm

@[simp]
lemma refl: (M.perm q q').perm q q' = M :=
by {
  ext lab sym
  simp [perm]
  · split
    · rename_i heq
      split at heq <;> simp_all
    · rename_i heq
      split at heq <;> {
        cases heq
        try simp_all
      }
}

lemma involutive: Function.Involutive (α:=Machine l s) (Machine.perm · q q') :=
by {
  intro M
  simp
}

lemma single (h: A -[M]-> B): ⟨swap q q' A.state, A.tape⟩ -[M.perm q q']-> ⟨swap q q' B.state, B.tape⟩ :=
by {
  obtain ⟨sym, dir, hsymdirB, hsymdirC⟩ := Machine.step.some_rev h
  refine Machine.step.some' (sym:=A.tape.head) (dir:=dir) (q':=swap q q' B.state) (sym':=sym) ?_ (by rfl) hsymdirC
  simp [perm]
  split <;> simp_all
}

instance isTransformation: @Transformation l s (λ C ↦ ⟨swap q q' C.state, C.tape⟩) (Machine.perm · q q') where
  fCinv := by {
    intro C
    simp
  }
  fMinv := involutive

  simulate := single

/-
Swapping to states makes an equivalent machine
-/
theorem equiv: (M, ⟨C, T⟩) =H (M.perm q q', ⟨swap q q' C, T⟩) := isTransformation.equi_halts

/-
If the states are non-zero, then the two machines are H-equivalent on the default state
-/
theorem nz_equi (hq: q ≠ default) (hq': q' ≠ default): (M, default) =H (M.perm q q', default) :=
by {
  conv =>
    pattern (occs:=2) (default (α:=Config l s))
    rw [show default = ⟨swap q q' default, default⟩ by {
      rw [swap.ne hq.symm hq'.symm]
      rfl
    }]
  exact equiv
}
