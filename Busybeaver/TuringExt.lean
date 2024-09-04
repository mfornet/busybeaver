import Mathlib.Computability.TuringMachine

instance: Fintype Turing.Dir := by {
  refine @Fintype.ofEquiv Turing.Dir Bool _ ?_
  exact {
    toFun := λ b ↦ if b then .left else .right
    invFun := λ t ↦ match t with | .left => true | .right => false
    left_inv := by {
      unfold Function.LeftInverse
      intro b
      cases b <;> simp
    }
    right_inv := by {
      simp only [Function.RightInverse, Function.LeftInverse]
      intro t
      cases t <;> simp
    }
  }
}

instance Turing.BlankExtends.instDecidableRel {Γ} [Inhabited Γ] [DecidableEq Γ] : DecidableRel (@Turing.BlankExtends Γ _)
  | [], ys => decidable_of_iff (∀ y ∈ ys, y = default) (by {
    simp [Turing.BlankExtends]
    constructor
    · intro hy
      exists ys.length
      exact List.eq_replicate_of_mem hy
    · intro ⟨n, hn⟩
      intro y hy
      apply List.eq_of_mem_replicate
      rw [hn] at hy
      exact hy
  })
  | x :: xs, [] => .isFalse (by simp [Turing.BlankExtends])
  | x :: xs, y :: ys =>
    letI := instDecidableRel xs ys
    decidable_of_iff (x = y ∧ Turing.BlankExtends xs ys) (by {
      simp [Turing.BlankExtends]
      intro n _
      constructor <;> {
        intro h
        exact h.symm
      }
    })

instance Turing.BlankRel.instDecidableRel {Γ} [Inhabited Γ] [DecidableEq Γ]: DecidableRel (@Turing.BlankRel Γ _) := by {
  simp [Turing.BlankRel, DecidableRel]
  intro a b
  apply instDecidableOr
}


namespace Turing.ListBlank

variable {Γ} [Inhabited Γ]

instance instHAppend: HAppend (List Γ) (ListBlank Γ) (ListBlank Γ) where
  hAppend := append

lemma append_assoc' {L₁ L₂: List Γ} {L: ListBlank Γ}: L₁ ++ L₂ ++ L = L₁ ++ (L₂ ++ L) :=
  Turing.ListBlank.append_assoc L₁ L₂ L

instance instDecidableEq [DecidableEq Γ]: DecidableEq (Turing.ListBlank Γ) := by {
  simp [Turing.ListBlank, Turing.BlankRel.setoid]
  refine @instDecidableEqQuotientOfDecidableEquiv _ _ ?_
  intro a b
  simp [instHasEquivOfSetoid, Setoid.r]
  apply inferInstance
}

lemma cons_nth_zero {T: Turing.ListBlank Γ}: (cons A T).nth 0 = A :=
by induction T using Turing.ListBlank.induction_on; simp

lemma cons_nth_succ {T: Turing.ListBlank Γ}: (cons A T).nth (i + 1) = T.nth i :=
by induction T using Turing.ListBlank.induction_on; simp

@[simp]
lemma cons_injective {T T': Turing.ListBlank Γ} {g g': Γ}: cons g T = cons g' T' ↔ g = g' ∧ T = T' :=
by {
  constructor
  swap
  · intro ⟨hg, hT⟩
    rw [hg, hT]
  intro hg
  constructor
  · rw [
      show g = (cons g T).head by simp,
      show g' = (cons g' T').head by simp,
      hg
    ]
  · rw [
      show T = (cons g T).tail by simp,
      show T' = (cons g' T').tail by simp,
      hg
    ]
}

@[simp]
lemma append_mk_nth {L: List Γ} {T: Turing.ListBlank Γ}:
  (L ++ T).nth i = if _ : i < L.length then L[i] else T.nth (i - L.length) :=
by induction i generalizing L T with
| zero => cases L <;> simp [instHAppend]
| succ n IH => {
  cases L with
  | nil => simp [instHAppend]
  | cons head tail => {
    simp [instHAppend]
    simp [instHAppend] at IH
    apply IH
  }
}

@[simp]
lemma default_nth: (default: Turing.ListBlank Γ).nth i = default :=
  by rfl

@[simp]
lemma append_empty {T: Turing.ListBlank Γ}: ([]: List Γ) ++ T = T :=
  by rfl

@[simp]
lemma append_cons {T: Turing.ListBlank Γ} {L: List Γ} {g: Γ}: g :: L ++ T = Turing.ListBlank.cons g (L ++ T) :=
  by rfl

@[simp]
lemma append_nth {T: Turing.ListBlank Γ} {L: List Γ}: (L ++ T).nth n = if h: n < L.length then L[n]'h else T.nth (n - L.length) :=
by induction n generalizing L with
| zero => {
  simp
  split
  · rename_i heq
    cases L <;> simp at heq
    simp
  · rename_i heq
    simp at heq
    cases heq
    simp
}
| succ n _ => cases L <;> simp

/--
If two list blanks are different, then by [Classical.choice] they differ at some point.
-/
lemma ne_exists_different {Lb Lb': Turing.ListBlank Γ}: Lb ≠ Lb' ↔ ∃n, Lb.nth n ≠ Lb'.nth n :=
by {
  constructor
  · intro hn
    simp at hn
    rw [Turing.ListBlank.ext_iff] at hn
    push_neg at hn
    exact hn
  · intro ⟨n, hn⟩ hL
    rw [Turing.ListBlank.ext_iff] at hL
    specialize hL n
    contradiction
}

partial def meet [DecidableEq Γ] (Lb Lb': Turing.ListBlank Γ) (h: Lb ≠ Lb'): List Γ :=
  if Lb.head = Lb'.head then
    Lb.head :: (meet Lb.tail Lb'.tail (by sorry))
  else
    []

@[simp]
def take (Lb: Turing.ListBlank Γ): ℕ → List Γ
| 0 => []
| n + 1 => Lb.head :: Lb.tail.take n

@[simp]
lemma take.length {Lb: Turing.ListBlank Γ}: (Lb.take n).length = n :=
  by induction n generalizing Lb <;> simp_all

@[simp]
def take_nth {Lb: Turing.ListBlank Γ} {n i: ℕ} (h: i < n): (Lb.take n)[i]'(by simp [h]) = Lb.nth i :=
by induction i generalizing n Lb with
| zero => {
  simp
  cases n <;> simp at h
  simp
}
| succ i IH => {
  simp
  cases n <;> simp at h
  simp
  exact IH h
}

@[simp]
def drop (Lb: Turing.ListBlank Γ): ℕ → ListBlank Γ
| 0 => Lb
| n + 1 => Lb.tail.drop n

@[simp]
lemma drop_nth {Lb: Turing.ListBlank Γ}: (Lb.drop n).nth n' = Lb.nth (n + n') :=
by induction n generalizing Lb with
| zero => simp
| succ n IH => {
  simp
  rw [IH, ← Turing.ListBlank.nth_succ]
  congr 1
  exact Nat.add_right_comm n n' 1
}

lemma append_take_drop {Lb: Turing.ListBlank Γ}: (Lb.take n) ++ (Lb.drop n) = Lb :=
by {
  ext i
  simp
  split
  · rename_i h
    simp [take_nth h]
  · rename_i heq
    congr 1
    push_neg at heq
    exact Nat.add_sub_of_le heq
}

end Turing.ListBlank

instance Turing.Tape.instDecidableEq {Γ} [Inhabited Γ] [DecidableEq Γ]: DecidableEq (Turing.Tape Γ) := by {
  unfold DecidableEq
  intro ⟨ha, La, Ra⟩ ⟨hb, Lb, Rb⟩
  simp
  repeat apply instDecidableAnd
}

namespace Turing.Dir
instance: Repr Turing.Dir where
  reprPrec := λ d _ ↦ match d with
    | .left => "L"
    | .right => "R"

def other: Turing.Dir → Turing.Dir
| .left => .right
| .right => .left

lemma eq_left_or_eq_right {d: Turing.Dir}: d = .left ∨ d = .right :=
by cases d <;> trivial

@[simp]
lemma move.other [Inhabited α] {Γ: Turing.Tape α}: (Γ.move d).move d.other = Γ :=
by cases d <;> simp [Turing.Tape.move, Turing.Dir.other]

@[simp]
lemma other.symmetric {d: Turing.Dir}: d.other.other = d :=
by cases d <;> simp [other]

end Turing.Dir
