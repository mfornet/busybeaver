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

@[simp]
lemma listBlankPrefix.cons_cons {L: List Γ} {g g': Γ} {Lb: Turing.ListBlank Γ}:
  g :: L <+:b Turing.ListBlank.cons g' Lb ↔ g = g' ∧ L <+:b Lb :=
  by induction Lb using Turing.ListBlank.induction_on; simp

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

instance {L: List Γ} {Lb: Turing.ListBlank Γ} [DecidableEq Γ]: Decidable (L <+:b Lb) :=
by induction L generalizing Lb with
| nil => {
  simp
  exact instDecidableTrue
}
| cons head tail IH => {
  simp
  apply inferInstance
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

section Meets

variable [DecidableEq Γ]

def ListBlank.meetList (Lb: Turing.ListBlank Γ): (L: List Γ) → List Γ
| [] => []
| head :: tail =>
  if head = Lb.head then
    head :: ListBlank.meetList Lb.tail tail
  else
    []

def ListBlank.meet.correct {Lb: Turing.ListBlank Γ} {L: List Γ}: ListBlank.meetList Lb L <+: L ∧ ListBlank.meetList Lb L <+:b Lb :=
  by induction Lb, L using ListBlank.meetList.induct <;> simp_all [ListBlank.meetList]

def List.meet: (L L': List Γ) → List Γ
| [], [] | [], _ :: _ | _ :: _, [] => []
| head :: tail, head' :: tail' =>
  if head = head' then
    head :: List.meet tail tail'
  else
    []

def List.meet.prefix_left {L L': List Γ}: List.meet L L' <+: L :=
  by induction L, L' using List.meet.induct <;> simp_all [meet]

def List.meet.commutative {L L': List Γ}: List.meet L L' = List.meet L' L :=
by induction L, L' using List.meet.induct with simp_all [meet]
| case5 _ _ _ _ h => {
  split
  · simp_all
  · rfl
}

def List.meet.prefix_right {L L': List Γ}: List.meet L L' <+: L' :=
by {
  rw [List.meet.commutative]
  exact List.meet.prefix_left
}

end Meets

lemma listBlankPrefix.exists_trailing {L: List Γ} {Lb: Turing.ListBlank Γ}:
  L <+:b Lb ↔ ∃(L': Turing.ListBlank Γ), Lb = L ++ L' :=
by induction L generalizing Lb with
| nil => simp
| cons head tail IH => {
  simp
  constructor
  · intro h
    obtain ⟨L', hL'⟩ := IH.mp h.2
    use L'
    rw [← Turing.ListBlank.cons_head_tail Lb, hL', h.1]
  · intro ⟨L', hL'⟩
    rw [← Turing.ListBlank.cons_head_tail Lb, Turing.ListBlank.cons_injective] at hL'
    use hL'.1.symm
    exact IH.mpr ⟨L', hL'.2⟩
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

@[simp]
lemma le_finite {L': List Γ}: PartialHTape.finite L ≤ PartialHTape.finite L' ↔ L <+: L' :=
  by rfl

@[simp]
lemma le_infinite {Lb Lb': Turing.ListBlank Γ}: PartialHTape.infinite Lb ≤ PartialHTape.infinite Lb' ↔ Lb = Lb' :=
  by rfl

@[simp]
lemma le_infinite_left {Lb: Turing.ListBlank Γ}: ¬(PartialHTape.infinite Lb ≤ .finite L) :=
by {
  simp [instPartialOrder, is_preffix]
}

@[simp]
lemma le_infinite_right {Lb: Turing.ListBlank Γ}: .finite L ≤ PartialHTape.infinite Lb ↔ L <+:b Lb :=
  by rfl


def meet [DecidableEq Γ]: PartialHTape Γ → PartialHTape Γ → PartialHTape Γ
| .finite L, .finite L' => List.meet L L'
| .finite L, .infinite Lb | .infinite Lb, .finite L => ListBlank.meetList Lb L
| .infinite Lb, .infinite Lb' =>
  if Lb = Lb' then
    Lb
  else
    .finite []

variable {T T': PartialHTape Γ} (h: T ≤ T')

@[simp]
lemma le_empty: .finite [] ≤ T :=
  by cases T <;> simp [instPartialOrder, is_preffix]

lemma meet.commutative [DecidableEq Γ]: T.meet T' = T'.meet T :=
by {
  cases T <;> cases T'
  · simp [meet]
    exact List.meet.commutative
  · simp [meet]
  · simp [meet]
  · rename_i Lb Lb'
    simp [meet]
    split
    · simp_all
    rename_i heq
    split
    · rename_i heq
      cases heq
      contradiction
    rfl
}

lemma meet.le_left [DecidableEq Γ]: T.meet T' ≤ T :=
by {
  cases T <;> cases T'
  · simp [meet]
    exact List.meet.prefix_left
  · simp [meet]
    exact ListBlank.meet.correct.1
  · simp [meet]
    exact ListBlank.meet.correct.2
  · simp [meet]
    split <;> simp
}

lemma meet.le_right [DecidableEq Γ]: T.meet T' ≤ T' :=
by {
  rw [commutative]
  exact le_left
}

/-!
We have enough to define the SemiLattice structure of partial half tapes
-/

instance [DecidableEq Γ]: SemilatticeInf (PartialHTape Γ) where
  inf := meet
  inf_le_left T T' := by {
    simp
    exact meet.le_left
  }
  inf_le_right T T' := by {
    simp
    exact meet.le_right
  }
  le_inf A B C hAB hAC := by {
    simp at *
    cases A with
    | infinite La => {
      cases B <;> simp at hAB
      cases C <;> simp at hAC
      simp [meet]
      simp_all
    }
    | finite La => {
      cases B <;> cases C <;> simp_all [meet]
      · sorry
      · sorry
      · sorry
      · split
        · simp_all
        · simp_all
    }
  }

include h

lemma is_preffix_nonempty (hT: T.nonempty): T'.nonempty :=
by {
  cases T'
  swap
  · simp [nonempty]

  cases T
  swap
  · simp [instPartialOrder, is_preffix] at h

  rename_i L' L
  simp [nonempty] at*
  exact List.IsPrefix.ne_nil h hT
}

lemma le_head? (hg: T.head? = some g): T'.head? = some g :=
by match T, T' with 
| .infinite _, .finite _ => simp [instPartialOrder, is_preffix] at h
| .infinite _, .infinite _ => {
  simp [head?] at *
  simp [instPartialOrder, is_preffix] at h
  rw [← h]
  exact hg
}
| .finite L, .infinite _ => {
  simp [head?] at *
  simp [instPartialOrder, is_preffix] at h
  cases L with
  | nil => simp at hg
  | cons head tail => {
    simp at hg
    simp at h
    cases hg
    exact h.1.symm
  }
}
| .finite L, .finite L' => {
  simp [head?] at *
  match L, L' with
  | [], _ => simp at hg
  | head :: tail, [] => simp at h
  | head :: tail, head' :: tail' => {
    simp at *
    cases hg
    exact h.1.symm
  }
}

lemma le_head (hT: T.nonempty) (hT': T'.nonempty): T.head hT = T'.head hT' :=
by {
  have hTh := PartialHTape.nonempty.head?_eq_some_head hT
  have hTh' := PartialHTape.nonempty.head?_eq_some_head hT'
  rw [le_head? h hTh] at hTh'
  simp at hTh'
  exact hTh'
}

end PartialHTape

namespace PartialTape

variable [Inhabited Γ]

def isSubtape (T T': PartialTape Γ): Prop :=
  T.dir = T'.dir ∧ T.left ≤ T'.left ∧ T.right ≤  T'.right

instance: PartialOrder (PartialTape Γ) where
  le := isSubtape
  le_refl A := by simp [isSubtape]
  le_trans A B C hA hB := by {
    simp [isSubtape] at *
    constructor
    · rw [hA.1, hB.1]
    constructor
    · exact le_trans hA.2.1 hB.2.1
    · exact le_trans hA.2.2 hB.2.2
  }
  le_antisymm A B hAB hBA := by {
    simp [isSubtape] at *
    obtain ⟨Ad, Al, Ar⟩ := A
    obtain ⟨Bd, Bl, Br⟩ := B
    simp at *
    constructor
    · rw [hAB.1]
    constructor
    · exact le_antisymm hAB.2.1 hBA.2.1
    · exact le_antisymm hAB.2.2 hBA.2.2
  }

lemma le_well_formed {T T': PartialTape Γ} (h: T ≤ T') (hT: T.well_formed): T'.well_formed :=
by {
  simp [instPartialOrder, isSubtape] at h
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

lemma le_head_eq {T T': PartialTape Γ} (h: T ≤ T') (hT: T.well_formed) (hT': T'.well_formed):
  T.head hT = T'.head hT' :=
by {
  obtain ⟨hd, hl, hr⟩ := h
  cases hTd: T.dir <;> {
    simp [hTd, head, pointed, ← hd]
    first
    | exact PartialHTape.le_head hl _ _
    | exact PartialHTape.le_head hr _ _
  }
}

end PartialTape

namespace PartialConfig

def isSubConfig (C C': PartialConfig l s): Prop :=
  C.state = C'.state ∧ C.tape ≤ C'.tape

instance: PartialOrder (PartialConfig l s) where
  le := isSubConfig
  le_refl A := by simp [isSubConfig]
  le_trans A B C hA hB := by {
    simp [isSubConfig] at *
    constructor
    · rw [hA.1, hB.1]
    · exact le_trans hA.2 hB.2
  }
  le_antisymm A B hAB hBA := by {
    simp [isSubConfig] at *
    obtain ⟨Aq, At⟩ := A
    obtain ⟨Ba, Bt⟩ := B
    simp at *
    constructor
    · rw [hAB.1]
    · exact le_antisymm hAB.2 hBA.2
  }

variable {A B: PartialConfig l s} {M: Machine l s}

open Machine.pstep?

lemma pstep?_of_le_pstep? (hA: A ≤ A') (hAB: A p-[M]-> B): ∃B', B ≤ B' ∧ A' p-[M]-> B' :=
by {
  have hAwf := (well_formed hAB)
  obtain ⟨hAq, hAt⟩ := hA
  have hAwf' := PartialTape.le_well_formed hAt hAwf
  simp [to_pstep' hAwf] at hAB
  simp [to_pstep' hAwf']
  simp [Machine.pstep] at *
  rw [← PartialTape.le_head_eq hAt hAwf, ← hAq]
  split
  · rename_i heq
    rw [heq] at hAB
    simp at hAB
  rename_i heq
  rw [heq] at hAB
  simp at hAB
  simp
  rw [← hAB]
  simp [instPartialOrder, isSubConfig]
  sorry
}
