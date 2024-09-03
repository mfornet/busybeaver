/-
The "minimal tape" theorem is a tool that allows to extract, from the partial step relation, the
_finite_ subtape from the orinal configuration that is enough to emulate the sequence of steps.
-/

import Busybeaver.Basic
import Busybeaver.Partial

namespace TM

variable {Γ}

namespace PartialHTape

private lemma prefix_append {A B C: List Γ} (hAB: A <+: B): A <+: B ++ C :=
by {
  rw [List.prefix_iff_eq_append] at hAB
  rw [← hAB]
  simp
}

variable [Inhabited Γ]

private def listBlankPrefix (L: List Γ) (Lb: Turing.ListBlank Γ): Prop :=
  Turing.ListBlank.liftOn Lb (λ L' ↦ ∃n, L <+: L' ++ List.replicate n default) (by {
    intro A B hAB
    simp
    obtain ⟨n, hn⟩ := hAB
    cases hn
    constructor
    · intro hA
      obtain ⟨n', hn'⟩ := hA
      by_cases h: n > n'
      · use 0
        simp
        conv =>
          rhs
          rhs
          rw [
            show List.replicate n default = List.replicate n' default ++ List.replicate (n - n') default by {
            simp
            symm
            exact Nat.add_sub_of_le (Nat.le_of_lt h)
          }]
        rw [← List.append_assoc]
        exact prefix_append hn'
      · simp at h
        use n' - n
        conv =>
          rhs
          rw [List.append_assoc]
          rhs
          rw [
            show List.replicate n default ++ List.replicate (n' - n) default = List.replicate n' default by {
            simp
            exact Nat.add_sub_of_le h
          }]
        exact hn'
    · intro hA
      obtain ⟨n', hn'⟩ := hA
      use n + n'
      simp at hn'
      exact hn'
  })

infix:40 " <+:b " => listBlankPrefix

@[simp]
lemma listBlankPrefix.def {L L': List Γ}: L <+:b (Turing.ListBlank.mk L') ↔ (∃n, L <+: L' ++ List.replicate n default) :=
  by rfl

lemma listBlankPrefix.head {g: Γ} {L: List Γ} {Lb: Turing.ListBlank Γ}
  (h: (g :: L) <+:b Lb): Lb.head = g :=
by induction Lb using Turing.ListBlank.induction_on with
| h L' => {
  simp at h
  obtain ⟨n, hn⟩ := h
  rw [Turing.ListBlank.head_mk]
  rw [List.prefix_iff_eq_append] at hn
  cases L' with
  | nil => {
    simp at *
    cases n with
    | zero => simp at hn
    | succ n => {
      simp [List.replicate_succ] at hn
      exact hn.1.symm
    }
  }
  | cons head tail => {
    simp at *
    exact hn.1.symm
  }
}

@[simp]
lemma listBlankPrefix.empty {Lb: Turing.ListBlank Γ}: [] <+:b Lb :=
  Turing.ListBlank.induction_on Lb (by simp)

@[simp]
lemma listBlankPrefix.cons {head: Γ} {tail: List Γ} {Lb: Turing.ListBlank Γ}:
  head :: tail <+:b Lb ↔ head = Lb.head ∧ tail <+:b Lb.tail :=
by induction Lb using Turing.ListBlank.induction_on with
| h Lb => {
  simp
  cases Lb with
  | nil => {
    simp
    constructor
    · intro ⟨n, hn⟩
      cases n with
      | zero => simp at hn
      | succ n => {
        simp [List.replicate_succ] at hn
        use hn.1, n
        exact hn.2
      }
    · intro ⟨hdef, n, hn⟩
      use n + 1
      simp [List.replicate_succ]
      exact ⟨hdef, hn⟩
  }
  | cons headb tailb => simp
}

lemma listBlankPrefix.append {L L': List Γ} {Lb: Turing.ListBlank Γ}
  (h: (L ++ L') <+:b Lb): L <+:b Lb :=
by induction L generalizing Lb with
| nil => simp
| cons head tail IH => {
  simp at h
  simp
  use h.1
  apply IH
  exact h.2
}

def is_preffix (T T': PartialHTape Γ): Prop := match T, T' with
| .finite L, .finite L' => L <+: L'
| .finite L, .infinite L' => L <+:b L'
| .infinite _, .finite _ => False
| .infinite L, .infinite L' => L = L'

instance: PartialOrder (PartialHTape Γ) where
  le := is_preffix
  le_refl T := by {
    cases T with
    | finite L => simp [is_preffix]
    | infinite L => simp [is_preffix]
  }
  le_trans A B C hA hB := by {
    match A, B, C with
    | .infinite _, .finite _, _ | _, .infinite _, .finite _ => simp [is_preffix] at hA hB
    | .finite _, .finite _, .finite _ => {
      simp [is_preffix] at *
      exact List.IsPrefix.trans hA hB
    }
    | .finite La, .finite Lb, .infinite Lc => {
      simp [is_preffix] at *
      rw [List.prefix_iff_eq_append] at hA
      symm at hA
      rw [hA] at *
      exact listBlankPrefix.append hB
    }
    | .infinite _, .infinite _, .infinite _ => {
      simp [is_preffix] at *
      rw [hA, hB]
    }
    | .finite La, .infinite Lb, .infinite Lc => {
      simp [is_preffix] at *
      rw [hB] at hA
      exact hA
    }
  }
  le_antisymm A B hAB hBA := by {
    match A, B with
    | .finite _, .infinite _ | .infinite _, .finite _ => simp [is_preffix] at hAB hBA
    | .infinite La, .infinite Lb => {
      simp [is_preffix] at hAB hBA
      rw [hAB]
    }
    | .finite La, .finite Lb => {
      simp [is_preffix] at hAB hBA
      simp
      have hls: La.length = Lb.length := by {
        apply Nat.le_antisymm
        · exact List.IsPrefix.length_le hAB
        · exact List.IsPrefix.length_le hBA
      }
      rw [List.prefix_iff_eq_append] at hAB
      simp [hls] at hAB
      exact hAB
    }
  }

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
  (h: M.pstep A hwe = .some B) (h': M.pstep A' hwf' = .some B'): B ⊆ B':=
by {
  sorry
}
