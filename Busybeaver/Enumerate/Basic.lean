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

lemma decider (hMM': equi_halts M M' C C'): (M.halts C ∨ ¬M.halts C) ↔ (M'.halts C' ∨ ¬M'.halts C') :=
by {
  simp [equi_halts] at hMM'
  simp_all
}

end equi_halts

class Transformation (fC: Config l s → Config l s) (fM: Machine l s → Machine l s) where
  fCinv : Function.Involutive fC
  fMinv : Function.Involutive fM

  simulate {M A B} : (A -[M]-> B) → (fC A -[fM M]-> fC B)

namespace Transformation

lemma rev [inst: Transformation fC fM] (h: fC A -[fM M]-> fC B): A -[M]-> B :=
by {
  rw [← inst.fCinv A, ← inst.fCinv B, ← inst.fMinv M]
  exact inst.simulate h
}

lemma lift [inst: Transformation fC fM] (hn: A -[M]{n}-> B): ((fC A) -[fM M]{n}-> (fC B)) :=
by induction n generalizing B with
| zero => {
  cases hn
  exact .refl
}
| succ n IH => {
  have ⟨C, hAC, hCB⟩ := hn.split
  obtain hqp := IH hAC
  have hMCB := hCB.single'

  calc fC A
    _ -[fM M]{n}-> fC C := hqp
    _ -[fM M]{1}-> fC B := by {
      apply Multistep.single
      exact inst.simulate hMCB
  }
}

lemma bisimu [inst: Transformation fC fM]: (A -[M]{n}-> B) ↔ ((fC A) -[fM M]{n}-> (fC B)) :=
by {
  constructor
  · intro hM
    exact lift hM
  · intro h'
    rw [← inst.fCinv A, ← inst.fCinv B, ← inst.fMinv M]
    apply lift h'
}

lemma last [inst: Transformation fC fM] (h: M.LastState C): (fM M).LastState (fC C) :=
by {
  by_contra
  simp_all [LastState, -Machine.step.none]
  cases hM: (fM M).step (fC C) with
  | none => {
    simp_all
  }
  | some C' => {
    suffices M.step C = .some (fC C') by {
      simp_all
    }
    rw [← inst.fCinv C'] at hM
    exact rev hM
  }
}

lemma equi_halts [inst: Transformation fC fM]: equi_halts M (fM M) q (fC q) :=
by {
  unfold equi_halts
  constructor
  · intro h
    obtain ⟨n, C, hC, hn⟩ := h
    exists n
    exists fC C
    constructor
    · exact last hC
    · rw [← bisimu]
      exact hn
  · intro h
    obtain ⟨n, C, hC, hn⟩ := h
    exists n
    exists fC C
    constructor
    · rw [← inst.fMinv M]
      exact last hC
    · rw [← inst.fMinv M, ← inst.fCinv q, ← bisimu]
      exact hn
}

end Transformation
-- namespace simu

-- variable {f: Config l s → Config l s} {g: Machine l s → Machine l s}

-- private lemma zstep (h: A -[M]{0}-> B): A = B := by {
--   cases h
--   rfl
-- }


-- lemma equi_halts (hf: Function.Involutive f) (hg: Function.Involutive g)
--   (h: ∀{M A B}, (A -[M]-> B) → ((f A) -[g M]-> (f B))):
--   equi_halts M (g M) q (f q) :=
-- by {

-- }
