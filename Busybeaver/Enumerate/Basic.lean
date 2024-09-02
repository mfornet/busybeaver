import Mathlib.Tactic
import Busybeaver.Basic
import Busybeaver.Reachability

namespace TM.Machine

variable {M: Machine l s}

def equi_halts (M M': Machine l s) (c₁ c₂: Config l s): Prop := M.halts c₁ ↔ M'.halts c₂

namespace equi_halts

lemma refl: equi_halts M M c c :=
  by {
    unfold equi_halts
    rfl
  }

lemma trans (h₁: equi_halts M₁ M₂ c₁ c₂) (h₂: equi_halts M₂ M₃ c₂ c₃): equi_halts M₁ M₃ c₁ c₃ :=
  by {
    unfold equi_halts at *
    exact Iff.trans h₁ h₂
  }

lemma comm (h: equi_halts M₁ M₂ c₁ c₂): equi_halts M₂ M₁ c₂ c₁ :=
  by {
    unfold equi_halts at *
    exact h.symm
  }

lemma mono (hM: A -[M]{n}-> B) (hE: equi_halts M M' B C): equi_halts M M' A C :=
  by {
    obtain ⟨hEqMM', hEqM'M⟩ := hE
    constructor
    · intro hMA
      apply hEqMM'
      exact halts.tail hM hMA
    · intro hM'C
      have hMB := hEqM'M hM'C
      exact halts.mono hM hMB
  }

lemma tail (hM: A -[M]{n}-> B) (hE: equi_halts M M' A C): equi_halts M M' B C :=
  by {
    obtain ⟨hEqMM', hEqM'M⟩ := hE
    constructor
    · intro hMB
      apply hEqMM'
      exact halts.mono hM hMB
    · intro hM'C
      exact halts.tail hM  (hEqM'M hM'C)
  }

end equi_halts
