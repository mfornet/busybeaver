/-
We define here the quotient type of turing machines modulo non-zero permutation of
states and symbols.

Following this, there exists a "normal form" for turing machines, where the states and symbols are visited in order.
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
  exact propext (equi_halts h)
})

/--
It is sufficient to consider one TM per isomorphism class to prove that all TMs are decided.
-/
theorem decide {M: Machine l s} (decider: ∀(M': EqTM l s), EqTM.halts M' ∨ ¬(EqTM.halts M')): M.halts default ∨ ¬M.halts default :=
  decider (Quotient.mk setoid M)

end Isomorph

def StateOrderedBetween (M: Machine l s) (A B: Config l s) := ∀ C n k, (A -[M]{n}-> C) ∧ (C -[M]{k}-> B) → A.state ≤ C.state ∧ C.state ≤ B.state

def StateOrdered (M: Machine l s) := ∀B, M.StateOrderedBetween default B

lemma StateOrdered.default_ordered: Machine.StateOrdered (l:=l) (s:=s) default :=
by {
  intro B C n k ⟨hdC, hCB⟩
  have hDef : Machine.LastState (l:=l) (s:=s) default default := by rfl
  unfold Machine.LastState at hDef
  cases hdC <;>
  cases hCB
  <;> {
    try contradiction
    try simp
  }
}

inductive Visits (M: Machine l s): Config l s → Config l s → ℕ → Finset (Label l) → Prop where
| refl C : M.Visits C C 0 {C.state}
| succ A B C n S : (A -[M]-> B) → M.Visits B C n S → M.Visits A C (.succ n) (insert A.state S)

notation A " -[" M "]{" n "}(" S ")-> " B => Machine.Visits M A B n S

namespace Visits

lemma to_multistep (h: A -[M]{n}(S)-> B): A -[M]{n}-> B :=
by induction h with
| refl => exact .refl
| succ A B C n _ hAB _ IH => exact .succ hAB IH

lemma from_multistep (h: A -[M]{n}-> B): ∃S, A -[M]{n}(S)-> B :=
by induction h with
| @refl C => {
  exists {C.state}
  exact refl _
}
| @succ A B C n hAB _ IH => {
  obtain ⟨S, hS⟩ := IH
  exists (insert A.state S)
  apply succ _ _ _ _ _ hAB hS
}

lemma nonempty (h: A -[M]{n}(S)-> B): S.Nonempty :=
by induction h <;> simp

def lifted (M: Machine l s) (hl': l ≤ l'): Machine l' s :=
  λ lab sym ↦ if hl: lab.val < l + 1 then match
    M ⟨lab.val, by {
      obtain ⟨lab, labh⟩ := lab
      simp_all
    }⟩ sym with
  | .halt => .halt
  | .next sym dir lab' => .next sym dir ⟨lab', by {
    obtain ⟨lab', h'⟩ := lab'
    simp
    calc lab'
      _ < l + 1 := h'
      _ ≤ l' + 1 := Nat.add_le_add_right hl' 1
  }⟩
  else
    .halt

/- theorem smaller_not_halts {l s: ℕ} {M: Machine l s} {A B: Config l s} {S: Finset (Label l)} (h: default -[M]{n}(S)-> B) (hn: Busybeaver S.card s < n): ¬(M.halts default) := -/
/- by induction l using Nat.caseStrongInductionOn with -/
/- | zero => { -/
/-   have hn' : 1 ≤ n := Nat.one_le_of_lt hn -/
/-   rw [show n = .succ (n - 1) by simp [*]] at h -/
/-   cases h -/
/-   rename_i B' S hdB' hB'B -/
/--/
/- } -/
/-   by_cases hSC : S.card = l -/
/-   · rw [hSC] at hn -/
/-     exact Busybeaver.not_halts h.to_multistep hn -/
/--/
/- } -/

end Visits
/--/
/- inductive VisitsInOrder (M: Machine l s): Config l s → Finset (Label l) → Prop where -/
/- | init : M.VisitsInOrder default {default} -/
/- | nextOld A B S: (A -[M]-> B) → M.VisitsInOrder A S → B.state ∈ S → M.VisitsInOrder B S -/
/- | nextNew A B S: (A -[M]-> B) → M.VisitsInOrder A S → B.state = A.state + 1 → M.VisitsInOrder B (insert B.state S) -/
/--/
/- namespace VisitsInOrder -/
/--/
/- lemma is_in {M: Machine l s} (h: M.VisitsInOrder C S): C.state ∈ S := -/
/- by induction h with -/
/- | init => simp [default] -/
/- | nextOld => trivial -/
/- | nextNew => simp -/
/--/
/- theorem normalize {M: Machine l s} (hM: ∃nlab, M default default = .next sym .right nlab) (hsym: sym ≠ -/
/-   default): ∃M' S, M'.VisitsInOrder default S ∧ (M, default) =H (M', default) := -/
/- by induction l with -/
/- | zero => { -/
/-   obtain ⟨nlab, hnlab⟩ := hM -/
/-   have hnlab : nlab = default := Fin.fin_one_eq_zero nlab -/
/-   exists M -/
/-   exists {default} -/
/-   constructor -/
/-   · exact init -/
/-   · exact equi_halts.refl -/
/- } -/
/- | succ n IH => { -/
/--/
/- } -/
/--/
/- end VisitsInOrder -/
