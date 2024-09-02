/-
Symmetries are the swap of left and right in the TM

M and M.symm are obviously equi-halting.
-/
import Busybeaver.Basic
import Busybeaver.Reachability
import Busybeaver.Enumerate.Basic

-- For the theorem at the end of the file
import Busybeaver.Enumerate.ZVisits

def Turing.Dir.other: Turing.Dir → Turing.Dir
| .left => .right
| .right => .left

lemma Turing.Dir.eq_left_or_eq_right {d: Turing.Dir}: d = .left ∨ d = .right :=
by cases d <;> trivial

@[simp]
lemma Turing.Dir.other.symmetric {d: Turing.Dir}: d.other.other = d :=
by cases d <;> simp [other]

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

end symm

/--
It is sufficient to only consider machines where the first transition is non-zero write to the right

This is another big theorem to reduce the size of the set of machines to consider
-/
theorem only_right (decider: ∀ (M': Machine l s) (q': Label l), (∃sym nlab, M' q' default = .next sym .right nlab ∧ sym ≠ default) → M'.halts ⟨q', default⟩ ∨ ¬M'.halts ⟨q', default⟩) (symnxt: M q default = .next sym dir nlab) (symne: sym ≠ default): M.halts ⟨q, default⟩ ∨ ¬M.halts ⟨q, default⟩ :=
by cases dir with
| right => {
  apply decider
  exists sym
  exists nlab
}
| left => {
  rw [equi_halts.decider symm.equiv]
  apply decider
  exists sym
  exists nlab
  constructor
  · simp [default] at symnxt
    simp [symm, symnxt, Turing.Dir.other]
  · exact symne
}

end Machine
