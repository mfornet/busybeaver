import Busybeaver.Basic
import Busybeaver.Reachability

namespace TM.Machine

variable {M: Machine l s}

-- def equi_halts (M M': Machine l s) (c₁ c₂: Config l s): Prop := M.halts c₁ ↔ M'.halts c₂

def equi_halts (α β: (Machine l s × Config l s)): Prop := α.1.halts α.2 ↔ β.1.halts β.2
notation α " =H " β => equi_halts α β

namespace equi_halts

lemma refl: A =H A :=
  by {
    unfold equi_halts
    rfl
  }

lemma trans (h₁: A =H B) (h₂: B =H C): A =H C :=
  by {
    unfold equi_halts at *
    exact Iff.trans h₁ h₂
  }

instance: IsTrans (Machine l s × Config l s) (· =H ·) where
  trans := by {
    intro A B C hA hB
    exact trans hA hB
  }

lemma comm (h: A =H B): B =H A :=
  by {
    unfold equi_halts at *
    exact h.symm
  }

lemma mono (hM: A -[M]{n}-> B): (M, A) =H (M, B) :=
by {
  constructor
  · intro hMA
    exact halts.tail hM hMA
  · intro hMB
    exact halts.mono hM hMB
}

lemma decider (hMM': (M, C) =H (M', C')): (M.halts C ∨ ¬M.halts C) ↔ (M'.halts C' ∨ ¬M'.halts C') :=
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

lemma same_halt_time [inst: Transformation fC fM] (h: M.halts_in n A): (fM M).halts_in n (fC A) :=
by {
  obtain ⟨C, CLast, Creach⟩ := h
  exists fC C
  constructor
  · exact last CLast
  · rw [← bisimu]
    exact Creach
}

lemma equi_halts [inst: Transformation fC fM]: (M, q) =H (fM M, fC q) :=
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
    obtain ⟨n, C', hC, hn⟩ := h
    exists n
    exists fC C'
    constructor
    · rw [← inst.fMinv M]
      exact last hC
    · rw [← inst.fMinv M, ← inst.fCinv q, ← bisimu]
      exact hn
}

end Transformation
