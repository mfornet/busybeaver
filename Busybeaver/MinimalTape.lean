/-
The "minimal tape" theorem is a tool that allows to extract, from the partial step relation, the
_finite_ subtape from the orinal configuration that is enough to emulate the sequence of steps.
-/

import Busybeaver.Basic
import Busybeaver.Partial

namespace TM

variable {Γ} [Inhabited Γ] [DecidableEq Γ]

namespace PartialHTape

private def listBlankPrefix (L: List Γ) (Lb: Turing.ListBlank Γ): Prop :=
match L with
| [] => true
| head :: tail => head == Lb.head ∧ listBlankPrefix tail Lb.tail

def is_preffix (T T': PartialHTape Γ): Prop := match T, T' with
| .finite L, .finite L' => L <+: L'
| .finite L, .infinite L' => listBlankPrefix L L'
| .infinite _, .finite _ => False
| .infinite L, .infinite L' => L == L'

variable {T T': PartialHTape Γ} (h: T.is_preffix T')

include h

lemma is_preffix_nonempty (hT: T.nonempty): T'.nonempty :=
by {
  cases T'
  swap
  · simp [nonempty]

  cases T
  swap
  · simp [is_preffix] at h

  rename_i L' L
  simp [nonempty] at*
  simp [is_preffix] at h
  exact List.IsPrefix.ne_nil h hT
}

lemma is_preffix_head (hg: T.head? = some g): T'.head? = some g :=
by match T, T' with 
| .infinite _, .finite _ => simp [is_preffix] at h
| .infinite _, .infinite _ => {
  simp [head?] at *
  simp [is_preffix] at h
  rw [← h]
  exact hg
}
| .finite L, .infinite _ => {
  simp [head?] at *
  simp [is_preffix] at h
  cases L with simp [PartialHTape.listBlankPrefix] at h
  | nil => simp at hg
  | cons head tail => {
    simp at hg
    cases hg
    exact h.1.symm
  }
}
| .finite L, .finite L' => {
  simp [head?] at *
  simp [is_preffix] at h
  match L, L' with
  | [], _ => simp at hg
  | head :: tail, [] => simp at h
  | head :: tail, head' :: tail' => {
    simp at *
    cases hg
    exact h.1.symm
  }
}

end PartialHTape

namespace PartialTape

def isSubtape (T T': PartialTape Γ): Prop :=
  T.dir == T'.dir ∧ T.left.is_preffix T'.left ∧ T.right.is_preffix T'.right

instance: HasSubset (PartialTape Γ) := ⟨isSubtape⟩

lemma sub_well_formed {T T': PartialTape Γ} (h: T ⊆ T') (hT: T.well_formed): T'.well_formed :=
by {
  simp [instHasSubset, isSubtape] at h
  simp [well_formed, pointed] at *
  split at hT <;> {
    rename_i heq
    rw [heq] at h
    rw [← h.1]
    simp
    first
    | exact PartialHTape.is_preffix_nonempty h.2.1 hT
    | exact PartialHTape.is_preffix_nonempty h.2.2 hT
  }
}

end PartialTape

namespace PartialConfig

def isSubConfig (C C': PartialConfig l s): Prop :=
  C.state = C'.state ∧ C.tape ⊆ C'.tape

instance: HasSubset (PartialConfig l s) := ⟨isSubConfig⟩

variable {A B: PartialConfig l s} {M: Machine l s}

lemma subconfig_step_mono (hA: A ⊆ A') (hwf: A.tape.well_formed) (hwf': A'.tape.well_formed)
  (h: M.pstep A hwe = .some B) (h': M.pstep A' hwf' = .some B): B ⊆ B':=
by {
  sorry
}
