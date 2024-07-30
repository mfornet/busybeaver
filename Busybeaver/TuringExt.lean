import Mathlib.Tactic
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

instance Turing.ListBlank.instDecidableEq {Γ} [Inhabited Γ] [DecidableEq Γ]: DecidableEq (Turing.ListBlank Γ) := by {
  simp [Turing.ListBlank, Turing.BlankRel.setoid]
  refine @instDecidableEqQuotientOfDecidableEquiv _ _ ?_
  intro a b
  simp [instHasEquivOfSetoid, Setoid.r]
  apply inferInstance
}

instance Turing.Tape.instDecidableEq {Γ} [Inhabited Γ] [DecidableEq Γ]: DecidableEq (Turing.Tape Γ) := by {
  unfold DecidableEq
  intro ⟨ha, La, Ra⟩ ⟨hb, Lb, Rb⟩
  simp
  repeat apply instDecidableAnd
}
