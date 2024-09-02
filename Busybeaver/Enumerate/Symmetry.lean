/-
Symmetries are the swap of left and right in the TM

M and M.symm are obviously equi-halting.
-/
import Busybeaver.Basic
import Busybeaver.Reachability
import Busybeaver.Enumerate.Basic

def Turing.Tape.reverse [Inhabited Γ] (T: Turing.Tape Γ): Turing.Tape Γ := {T with left := T.right, right := T.left}

namespace Turing.Tape.reverse

variable [Inhabited Γ] {T: Turing.Tape Γ}

@[simp]
lemma symm: T.reverse.reverse = T :=
by simp [reverse]

@[simp]
lemma move: T.reverse.move dir = (T.move dir.other).reverse :=
by cases dir <;> simp [Tape.move, Turing.Dir.other, reverse]

@[simp]
lemma move' (h: dir' = dir.other): T.reverse.move dir = (T.move dir').reverse :=
by {
  rw [h]
  simp
}

@[simp]
lemma write: T.reverse.write sym = (T.write sym).reverse :=
by simp [Tape.write, reverse]

@[simp]
lemma head: T.reverse.head = T.head :=
by simp [reverse]

@[simp]
lemma eqv: T.reverse = T'.reverse ↔ T = T' :=
by {
  constructor
  · intro h
    simp [reverse] at h
    obtain ⟨Th, Tl, Tr⟩ := T
    obtain ⟨Th', Tl', Tr'⟩ := T'
    simp_all
  · intro h
    simp [h]
}

@[simp]
lemma default: Turing.Tape.reverse (Γ:=Γ) default = default :=
  by rfl

end Turing.Tape.reverse

namespace TM.Machine

variable {M: Machine l s}

def symm (M: Machine l s): Machine l s := λ lab sym ↦ match M lab sym with
| .halt => .halt
| .next sym dir nlab => .next sym dir.other nlab

namespace symm

@[simp]
lemma involutive: Function.Involutive (α:=Machine l s) Machine.symm :=
by {
  intro x
  apply funext
  intro lab
  apply funext
  intro sym
  simp [symm]
  split
  · rename_i heq
    split at heq <;> simp_all
  · rename_i heq
    split at heq
    · simp_all
    · cases heq
      simp_all
}


def config_reverse (C: Config l s): Config l s := ⟨C.state, C.tape.reverse⟩

lemma config_rev.inv: Function.Involutive (α:=Config l s) config_reverse :=
by {
  intro x
  simp [config_reverse]
}

lemma config_reverse.default: config_reverse (l:=l) (s:=s) default = default :=
by rfl

lemma single (h: A -[M]-> B): config_reverse A -[M.symm]-> config_reverse B :=
by {
  obtain ⟨sym, dir, hAB, hBtape⟩ := Machine.step.some_rev h
  apply Machine.step.some' (sym:=A.tape.head) (sym':=sym) (dir:=dir.other)
  · simp [symm, hAB]
  · simp
  · simp
    exact hBtape
}

instance transformation: @Transformation l s config_reverse symm where
  fCinv := config_rev.inv
  fMinv := symm.involutive

  simulate := single

lemma equiv: (M, ⟨q, default⟩) =H (M.symm, ⟨q, default⟩) :=
by {
  suffices config_reverse ⟨q, default⟩ = ⟨q, default⟩ by {
    conv =>
      pattern (occs:=2) Config.mk q default
      rw [← this]
    exact Transformation.equi_halts
  }
  simp [config_reverse, default]
  rfl
}

lemma same_runtime (hM: M.halts_in n C): M.symm.halts_in n (config_reverse C) :=
  Transformation.same_halt_time hM

noncomputable def GoingTo (l s : ℕ) (dir: Turing.Dir) :=
  Finset.univ (α:=Terminating l s) |>.filter (λ M ↦ ∃ sym nlab, M.M default default = .next sym dir nlab)

noncomputable def DirectHalts (l s: ℕ) :=
  Finset.univ (α:=Terminating l s) |>.filter (λ M ↦ M.M default default = .halt)

lemma right_eq_left: Busybeaver' l s (GoingTo l s .right) = Busybeaver' l s (GoingTo l s .left) :=
by {
  apply symm.transformation.same_busybeaver' symm.config_reverse.default
  apply Finset.ext
  intro M
  unfold GoingTo Transformation.lift_terminating
  simp
  constructor
  · intro ⟨sym, nlab, h⟩
    exists (symm.transformation.lift_terminating symm.config_reverse.default) M
    simp [Transformation.lift_terminating, symm.involutive M.M]
    exists sym
    exists nlab
    simp [Machine.symm, h, Turing.Dir.other]
  · intro ⟨M', ⟨sym, nlab, hsym⟩, hM'⟩
    exists sym
    exists nlab
    rw [show M.M = M'.M.symm by rw [← hM']]
    simp [Machine.symm, hsym, Turing.Dir.other]
}

theorem univ_eq_union: Finset.univ = (GoingTo l s .right) ∪ (GoingTo l s .left) ∪ (DirectHalts l s) :=
by {
  apply Finset.ext
  intro M
  simp [GoingTo, DirectHalts]
  cases M.M default default <;> simp_all [Turing.Dir.eq_left_or_eq_right.symm]
}

/-
To compute the busy beaver, it is enough to only consider machine going to the right
-/
theorem only_right: Busybeaver l s = Busybeaver' l s (GoingTo l s .right) :=
by {
  unfold Busybeaver
  conv =>
    lhs
    pattern Finset.univ
    rw [univ_eq_union]
  simp [right_eq_left]
  suffices Busybeaver' l s (DirectHalts l s) = 0 by {
    simp [this]
  }
  apply Nat.eq_zero_of_le_zero
  apply Busybeaver'.upper_bound
  intro ⟨M, n, term⟩ hHalts
  simp_all [DirectHalts]
  have hMh: M.halts_in 0 default := by {
    exists default
    constructor
    · unfold LastState
      simp [default]
      exact hHalts
    · exact Multistep.refl
  }
  exact term.deterministic hMh
}

end Machine.symm
