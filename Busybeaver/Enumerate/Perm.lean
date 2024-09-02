import Busybeaver.Basic
import Busybeaver.Reachability
import Busybeaver.Enumerate.Basic

namespace TM.Machine

variable {M: Machine l s}

def swap [DecidableEq α] (q q': α) (lab: α): α :=
  if lab = q then q' else if lab = q' then q else lab

namespace swap

variable [DecidableEq α] {q q' lab: α}

@[simp]
lemma id: swap q q q' = q' :=
by {
  simp [swap]
  split <;> simp_all
}

@[simp]
lemma left: swap q q' q = q' :=
by simp [swap]

@[simp]
lemma right: swap q q' q' = q :=
by simp [swap]

@[simp]
lemma swap_swap: swap q q' (swap q q' lab) = lab :=
  by {
    by_cases hq: q = q' <;> {
      simp [swap]
      repeat split <;> simp_all
    }
  }

lemma involutive: Function.Involutive (swap q q') :=
by {
  intro x
  exact swap_swap
}

@[simp]
lemma left_eq: swap q q' lab = q ↔ lab = q' :=
by {
  simp [swap]
  split
  · simp_all
    exact eq_comm
  split
  · simp_all
  · simp_all
}

@[simp]
lemma right_eq: swap q q' lab = q' ↔ lab = q :=
by {
  by_cases hqq: q = q'
  · simp_all
  simp [swap]
  split <;> simp_all
}

@[simp]
lemma ne (hq: lab ≠ q) (hq': lab ≠ q'): swap q q' lab = lab :=
by {
  simp [swap]
  repeat split <;> simp_all
}

end swap

def perm (M: Machine l s) (q q': Label l): Machine l s := λ lab sym ↦ match M (swap q q' lab) sym with
| .halt => .halt
| .next sym dir nlab => .next sym dir (swap q q' nlab)

namespace perm

@[simp]
lemma refl: (M.perm q q').perm q q' = M :=
by {
  apply funext
  intro lab
  apply funext
  intro sym
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
