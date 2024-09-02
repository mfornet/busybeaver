/-
We define here the quotient type of turing machines modulo non-zero permutation of
states and symbols.

This one of the main building blocks of the proof of the enumeration algorithm.
The next step is to show that EqTM ≃ TNF
-/

import Busybeaver.Basic
import Busybeaver.Enumerate.Basic
import Busybeaver.Enumerate.Perm
import Busybeaver.Enumerate.Translate

namespace TM.Machine

variable {l s: ℕ}

/--
We use a similar approach as lean's batteries definition for list permutations here.

This will allow to simpler definitions
-/
inductive Isomorph: Machine l s → Machine l s → Prop
| refl M : Isomorph M M
| states L L' M M' : L ≠ default → L' ≠ default → M' = M.perm L L' → Isomorph M M'
| symbols S S' M M' : S ≠ default → S' ≠ default → M' = M.translated S S' → Isomorph M M'
| trans M₁ M₂ M₃ : Isomorph M₁ M₂ → Isomorph M₂ M₃ → Isomorph M₁ M₃

notation M " ~m " M' => Isomorph M M'

namespace Isomorph

lemma symm (h: M ~m M'): M' ~m M :=
by induction h with
| refl => exact refl _
| states L L' M M' hL hL' hM => {
  apply states L L' M' M hL hL'
  rw [hM]
  simp
}
| symbols S S' M M' hS hS' hM => {
  apply symbols S S' M' M hS hS'
  rw [hM]
  simp
}
| trans M₁ M₂ M₃ _ _ IH₁ IH₂ => {
  exact trans M₃ M₂ M₁ IH₂ IH₁
}

lemma equi_halts (h: M ~m M'): (M, default) =H (M', default) :=
by induction h with
| refl => exact equi_halts.refl
| states L L' M M' hL hL' hM => {
  rw [hM]
  exact perm.nz_equi hL hL'
}
| symbols S S' M M' hS hS' hM => {
  rw [hM]
  exact translated.equi_halts' hS.symm hS'.symm
}
| trans M₁ M₂ M₃ _ _ IH₁ Ih₂ => exact equi_halts.trans IH₁ Ih₂

instance setoid: Setoid (Machine l s) where
  r := Isomorph
  iseqv := {
    refl := refl
    symm := symm
    trans := by {
      intro x y z hx hy
      exact trans x y z hx hy
    }
  }

def EqTM (l s: ℕ) := Quotient (α:=Machine l s) setoid

def EqTM.halts (M: EqTM l s): Prop := Quotient.liftOn M (Machine.halts · default) (by {
  intro A B h
  beta_reduce
  simp [instHasEquivOfSetoid, Setoid.r] at h
  have hMe := equi_halts h
  exact propext hMe
})

/--
It is sufficient to consider one TM per isomorphism class to prove that all TMs are decided.
-/
theorem decide {M: Machine l s} (decider: ∀(M': EqTM l s), EqTM.halts M' ∨ ¬(EqTM.halts M')): M.halts default ∨ ¬M.halts default :=
  decider (Quotient.mk setoid M)

end Isomorph
