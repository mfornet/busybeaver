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

def ListBlank.meetList.correct {Lb: Turing.ListBlank Γ} {L: List Γ}:
  ListBlank.meetList Lb L <+: L ∧ ListBlank.meetList Lb L <+:b Lb :=
  by induction Lb, L using ListBlank.meetList.induct <;> simp_all [ListBlank.meetList]

/--
A (very private) version of list meet, meant to be used to define the meet of ListBlanks.
-/
private def meet_part: List Γ → List Γ → PartialHTape Γ
| [], [] => .infinite {}
| [], head :: tail | head :: tail, [] =>
  if head = default then
    PartialHTape.cons head (meet_part tail [])
  else
    .finite []
| head :: tail, head' :: tail' =>
  if head = head' then
    PartialHTape.cons head (meet_part tail tail')
  else
    .finite []
termination_by L L' => L.length + L'.length

lemma meet_part.commutative {L L': List Γ}: meet_part L L' = meet_part L' L :=
by induction L, L' using meet_part.induct with simp_all [meet_part]
| case7 head tail head' tail' hne => {
  push_neg at hne
  symm at hne
  simp [hne]
}

@[simp]
lemma meet_part.self {L: List Γ}: meet_part L L = .infinite (Turing.ListBlank.mk L) :=
by induction L with simp [meet_part]
| nil => simp [infty, Turing.ListBlank.hasEmptyc, default]
| cons head tail IH => {
  rw [IH]
  simp [PartialHTape.cons_append]
}

@[simp]
lemma meet_part.replicate_default_right: meet_part [] (List.replicate n default) = .infinite ({}: Turing.ListBlank Γ) :=
by induction n with
| zero => simp [infty, default, Turing.ListBlank.hasEmptyc]
| succ n IH => {
  simp [List.replicate_succ, meet_part]
  rw [commutative, IH]
  simp
}

@[simp]
lemma meet_part.replicate_default_left: meet_part (List.replicate n default) [] = .infinite ({}: Turing.ListBlank Γ) :=
by {
  rw [commutative]
  simp
}

@[simp]
lemma meet_part.append_replicate_default {L: List Γ} {n: ℕ}: (meet_part L (L ++ List.replicate n default)) = Turing.ListBlank.mk L :=
by induction L with
| nil => {
  simp [infty]
  rfl
}
| cons head tail IH => {
  simp [meet_part, PartialHTape.cons_append ]
  congr
  simp at IH
  exact IH
}

lemma meet_part.nil_finite_eq_replicate_left {L: List Γ} (h: meet_part L [] = .finite L'): ∃n, L' = List.replicate n default :=
by induction L generalizing L' with
| nil => simp [infty] at h
| cons head tail IH => {
  simp [meet_part] at h
  split at h
  swap
  · simp at h
    cases h
    use 0
    simp
  · rename_i heq
    cases heq
    cases L'
    · use 0
      simp
    · rw [← PartialHTape.cons_list, PartialHTape.cons.injective] at h
      cases h.1
      simp at h
      obtain ⟨n, hn⟩ := IH h
      cases hn
      use n + 1
      simp [List.replicate_succ]
}

lemma meet_part.nil_finite_eq_replicate_right {L: List Γ} (h: meet_part [] L = .finite L'): ∃n, L' = List.replicate n default :=
by {
  rw [commutative] at h
  exact nil_finite_eq_replicate_left h
}

lemma meet_part.blank_ext {L L': List Γ} (h: Turing.BlankExtends L L'): meet_part L L' = Turing.ListBlank.mk L :=
by {
  simp [Turing.BlankExtends] at h
  obtain ⟨n, hn⟩ := h
  cases hn
  simp
}

@[simp]
lemma meet_part.stable_replicate {L: List Γ}: meet_part L (List.replicate n default) = meet_part L [] :=
by induction L generalizing n with
| nil => {
  simp
  rfl
}
| cons head tail IH => {
  cases n with
  | zero => simp
  | succ n => {
    simp [List.replicate_succ, meet_part]
    split
    · congr 1
      exact IH
    · rfl
  }
}

/--
The main correctness theorem, which allows lifting meet_part to ListBlank
-/
@[simp]
lemma meet_part.stable_append_replicate_right {L L': List Γ}:  meet_part L (L' ++ List.replicate n default) = meet_part L L' :=
by induction L' generalizing L with
| nil => simp
| cons head tail IH => {
  cases L with
  | nil => {
    simp [meet_part]
    split
    · congr 1
      conv_lhs => rw [commutative]
      conv_rhs => rw [commutative]
      exact IH
    · rfl
  }
  | cons head' tail' => {
    simp [meet_part]
    split
    · congr 1
      exact IH
    · rfl
  }
}

@[simp]
lemma meet_part.stable_append_replicate_left {L L': List Γ}: meet_part (L ++ List.replicate n default) L' = meet_part L L' :=
by {
  conv_lhs => rw [commutative]
  conv_rhs => rw [commutative]
  simp
}

@[simp]
lemma meet_part.eq_infty_of_replicate_left {L: List Γ}: meet_part L [] = infty ↔ ∃n, L = List.replicate n default :=
by induction L with
| nil => {
  simp
  use 0
  simp
}
| cons head tail IH => {
  constructor
  · intro h
    simp [meet_part] at h
    split at h
    swap
    · simp [infty] at h
    rename_i heq
    cases heq
    simp [IH] at h
    obtain ⟨n, hn⟩ := h
    cases hn
    use n + 1
    simp [List.replicate_succ]
  · intro ⟨n, hn⟩
    cases n
    · simp at hn
    rename_i n
    simp [List.replicate_succ] at hn
    cases hn.1
    simp [meet_part]
    rw [IH]
    use n, hn.2
}

@[simp]
lemma meet_part.eq_infty_of_replicate_right {L: List Γ}: meet_part [] L = infty ↔ ∃n, L = List.replicate n default :=
by {
  rw [commutative]
  exact eq_infty_of_replicate_left
}

private def meet_part_lb (Lb: Turing.ListBlank Γ) (L: List Γ): PartialHTape Γ :=
  Lb.liftOn (meet_part L) (by {
    intro A B hAB
    simp [Turing.BlankExtends] at hAB
    obtain ⟨n, hn⟩ := hAB
    cases hn
    simp
  })

@[simp]
lemma meet_part_lb.append_replicate {Lb: Turing.ListBlank Γ} {L: List Γ}: meet_part_lb Lb (L ++ List.replicate n default) = meet_part_lb Lb L :=
by induction Lb using Turing.ListBlank.induction_on with
| h Lb => simp [meet_part_lb]

def ListBlank.meet (Lb Lb': Turing.ListBlank Γ): PartialHTape Γ :=
  Lb.liftOn (meet_part_lb Lb') (by {
    intro A B hAB
    simp [Turing.BlankExtends] at hAB
    obtain ⟨n, hn⟩ := hAB
    cases hn
    simp
  })

lemma ListBlank.meet.commutative {Lb Lb': Turing.ListBlank Γ}: ListBlank.meet Lb Lb' = ListBlank.meet Lb' Lb :=
by {
  induction Lb using Turing.ListBlank.induction_on
  induction Lb' using Turing.ListBlank.induction_on
  simp [meet, meet_part_lb]
  exact meet_part.commutative
}

@[simp]
lemma ListBlank.meet.self {Lb: Turing.ListBlank Γ}: ListBlank.meet Lb Lb = Lb :=
by {
  induction Lb using Turing.ListBlank.induction_on
  simp [meet, meet_part_lb]
}

@[simp]
lemma ListBlank.meet.eq_of_eq_left {Lb Lb': Turing.ListBlank Γ} (h: ListBlank.meet Lb Lb' = Lb): Lb = Lb' :=
by {
  induction Lb using Turing.ListBlank.induction_on
  induction Lb' using Turing.ListBlank.induction_on
  simp [meet, meet_part_lb] at h
  simp
  rename_i Lb Lb'
  induction Lb, Lb' using meet_part.induct with try simp_all [meet_part]
  | case1 => {
    left
    use 0
    simp
  }
  | case2 tail IH => {
    obtain ⟨n, hn⟩ := h
    cases hn
    simp at IH
    rw [← List.replicate_succ]
    left
    use n + 1
    simp
  }
  | case3 head tail hne => simp [infty] at h
  | case4 tail IH => {
    rw [PartialHTape.cons_append, PartialHTape.cons.injective] at h
    right
    simp at h
    specialize IH h
    simp [Turing.BlankRel] at IH
    rcases IH with ⟨n, hn⟩ | ⟨n, hn⟩
    · cases tail
      swap
      · cases hn
      use 1
      simp
    · use n + 1
      simp at hn
      cases hn
      simp [List.replicate_succ]
  }
  | case5 => cases h
  | case6 tail head' tail' IH => {
    rw [PartialHTape.cons_append] at h
    rw [PartialHTape.cons.injective] at h
    cases h.1
    simp at h
    specialize IH h
    rcases IH with ⟨n, hn⟩ | ⟨n, hn⟩
    · cases hn
      left
      use n
      simp
    · cases hn
      right
      use n
      simp
  }
  | case7 head tail head' tail' hne => cases h
}

@[simp]
lemma ListBlank.meet.eq_of_eq_right {Lb Lb': Turing.ListBlank Γ} (h: ListBlank.meet Lb Lb' = Lb'): Lb = Lb' :=
by {
  rw [commutative] at h
  symm
  exact eq_of_eq_left h
}

lemma ListBlank.meet.eq_finite_of_ne {Lb Lb': Turing.ListBlank Γ} (h: Lb ≠ Lb'): ∃L, meet Lb Lb' = .finite L :=
by {
  induction Lb using Turing.ListBlank.induction_on
  induction Lb' using Turing.ListBlank.induction_on
  simp [meet, meet_part_lb]
  simp at h
  rename_i Lb Lb'
  induction Lb, Lb' using meet_part.induct with try simp_all [meet_part]
  | case1 => {
    simp [Turing.BlankRel, Turing.BlankExtends] at h
    specialize h 0
    simp at h
  }
  | case4 tail IH | case2 tail IH => {
    simp [Turing.BlankRel, Turing.BlankExtends] at h
    specialize IH (by {
      intro h'
      simp [Turing.BlankRel, Turing.BlankExtends] at h'
      rcases h' with h' | ⟨n, hn⟩
      · cases h'.1
        specialize h 1
        simp at h
      · cases hn
        specialize h (n + 1)
        simp [List.replicate_succ] at h
    })
    obtain ⟨L, hL⟩ := IH
    rw [hL]
    simp
  }
  | case6 tail head tail' IH => {
    simp [Turing.BlankRel, Turing.BlankExtends] at h
    obtain ⟨htt', ht't⟩ := h
    specialize IH (by {
      intro hrel
      rcases hrel with ⟨n, hn⟩ | ⟨n, hn⟩ <;> {
        specialize htt' n
        specialize ht't n
        contradiction
      }
    })
    obtain ⟨L, hL⟩ := IH
    rw [hL]
    simp
  }
}

@[simp]
lemma ListBlank.meet.finite_prefix_left {Lb Lb': Turing.ListBlank Γ} (h: ListBlank.meet Lb Lb' = .finite L): L <+:b Lb :=
by {
  induction Lb using Turing.ListBlank.induction_on
  induction Lb' using Turing.ListBlank.induction_on
  simp [meet, meet_part_lb] at h
  simp [listBlankPrefix]
  rename_i Lb Lb'
  induction Lb, Lb' using meet_part.induct generalizing L with simp_all [meet_part]
  | case1 => simp [infty] at h
  | case2 tail _ => {
    cases L
    · simp
    rw [← PartialHTape.cons_list, PartialHTape.cons.injective] at h
    cases h.1
    simp at h
    rename_i tailL
    obtain ⟨n, hn⟩ := meet_part.nil_finite_eq_replicate_left h
    cases hn
    use n + 1
    simp [List.replicate_succ]
  }
  | case4 tail IH => {
    cases L
    · simp
    rw [← PartialHTape.cons_list, PartialHTape.cons.injective] at h
    cases h.1
    simp at h
    simp
    rename_i head' tail'
    exact IH h
  }
  | case5 | case7 => {
    cases h
    simp
  }
  | case6 tail head' tail' IH => {
    cases L
    · simp
    rename_i headL tailL
    rw [← PartialHTape.cons_list, PartialHTape.cons.injective] at h
    cases h.1
    simp at h
    simp
    exact IH h
  }
}

@[simp]
lemma ListBlank.meet.finite_prefix_right {Lb Lb': Turing.ListBlank Γ} (h: ListBlank.meet Lb Lb' = .finite L): L <+:b Lb' :=
by {
  rw [commutative] at h
  exact finite_prefix_left h
}

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
lemma le_infty {Lb: PartialHTape Γ}: Lb ≤ infty ↔ (Lb = infty ∨ ∃n, Lb = .finite (List.replicate n default)) :=
by {
  constructor
  swap
  · intro h
    rcases h with h | ⟨n, hn⟩
    · rw [h]
    · cases hn
      simp [infty, instPartialOrder, is_preffix]
      induction n with
      | zero => simp
      | succ n IH => {
        simp [List.replicate_succ]
        constructor
        · rfl
        · rw [show (default: Turing.ListBlank Γ).tail = default by rfl]
          exact IH
      }
  intro h
  simp [instPartialOrder, is_preffix, infty] at h
  cases Lb with
  | finite L => {
    simp at h
    simp [infty]
    induction L with
    | nil => {
      use 0
      simp
    }
    | cons head tail IH => {
      simp at h
      obtain ⟨n, hn⟩ := IH h.2
      use n + 1
      simp [List.replicate_succ]
      constructor
      · rw [h.1]
        rfl
      · exact hn
    }
  }
  | infinite Lb => {
    simp at h
    left
    simp [infty]
    exact h
  }
}

@[simp]
lemma le_infinite_right {Lb: Turing.ListBlank Γ}: .finite L ≤ PartialHTape.infinite Lb ↔ L <+:b Lb :=
  by rfl


def meet [DecidableEq Γ]: PartialHTape Γ → PartialHTape Γ → PartialHTape Γ
| .finite L, .finite L' => List.meet L L'
| .finite L, .infinite Lb | .infinite Lb, .finite L => ListBlank.meetList Lb L
| .infinite Lb, .infinite Lb' => ListBlank.meet Lb Lb'

variable {T T': PartialHTape Γ} (h: T ≤ T')

@[simp]
lemma le_empty: .finite [] ≤ T :=
  by cases T <;> simp [instPartialOrder, is_preffix]

lemma meet.commutative [DecidableEq Γ]: T.meet T' = T'.meet T :=
by {
  cases T <;> cases T' <;> simp [meet]
  · exact List.meet.commutative
  · exact ListBlank.meet.commutative
}

lemma meet.le_left [DecidableEq Γ]: T.meet T' ≤ T :=
by {
  cases T <;> cases T'
  · simp [meet]
    exact List.meet.prefix_left
  · simp [meet]
    exact ListBlank.meetList.correct.1
  · simp [meet]
    exact ListBlank.meetList.correct.2
  · simp [meet]
    rename_i Lb Lb'
    -- TODO: move this proof outside of here
    by_cases h: Lb = Lb'
    · cases h
      simp
    obtain ⟨L, hL⟩ := ListBlank.meet.eq_finite_of_ne h
    rw [hL]
    simp
    exact ListBlank.meet.finite_prefix_left hL
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
      sorry
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
  rw [← h]
  exact hg
}
| .finite L, .infinite _ => {
  simp [head?] at *
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
