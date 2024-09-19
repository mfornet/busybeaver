import Busybeaver.Basic
import Busybeaver.Reachability
import Busybeaver.Problem

namespace TM.Machine

variable {M: Machine l s}

def swap [DecidableEq α] (q q': α) (lab: α): α :=
  if lab = q then q' else if lab = q' then q else lab

namespace swap

variable [DecidableEq α] {q q' lab: α}

@[simp]
lemma id: swap q q q' = q' :=
by {
  simp [swap]
  split <;> simp_all
}

@[simp]
lemma left: swap q q' q = q' :=
by simp [swap]

@[simp]
lemma right: swap q q' q' = q :=
by simp [swap]

@[simp]
lemma swap_swap: swap q q' (swap q q' lab) = lab :=
  by {
    by_cases hq: q = q' <;> {
      simp [swap]
      repeat split <;> simp_all
    }
  }

lemma involutive: Function.Involutive (swap q q') :=
by {
  intro x
  exact swap_swap
}

@[simp]
lemma left_eq: swap q q' lab = q ↔ lab = q' :=
by {
  simp [swap]
  split
  · simp_all
    exact eq_comm
  split
  · simp_all
  · simp_all
}

@[simp]
lemma right_eq: swap q q' lab = q' ↔ lab = q :=
by {
  by_cases hqq: q = q'
  · simp_all
  simp [swap]
  split <;> simp_all
}

@[simp]
lemma ne (hq: lab ≠ q) (hq': lab ≠ q'): swap q q' lab = lab :=
by {
  simp [swap]
  repeat split <;> simp_all
}

end swap

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

lemma same_halt_time₁ [inst: Transformation fC fM] (h: M.halts_in n A) (hC: C = fC A): (fM M).halts_in n C :=
by {
  rw [hC]
  exact same_halt_time h
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


def lift_terminating (inst: Transformation (l:=l) (s:=s) fC fM) (hfC: fC default = default): Terminating l s → Terminating l s :=
  λ M ↦ {
    M := fM M.M,
    n := M.n,
    terminates := by {
      rw [← hfC]
      exact same_halt_time M.terminates
    }
  }

@[simp]
lemma lift_terminating.halt_steps [inst: Transformation (l:=l) (s:=s) fC fM] {M: Terminating l s}:
(inst.lift_terminating hfC M).n = M.n :=
by simp [lift_terminating]

theorem same_busybeaver [inst: Transformation fC fM] {S: Finset (Terminating l s)} (hfC: fC default = default): Busybeaver' l s
S = Busybeaver' l s (S.image (inst.lift_terminating hfC)) :=
by induction S using Finset.induction with
| empty => simp
| @insert A S _ IH => simp [IH]

lemma same_busybeaver' [inst: Transformation fC fM] {S: Finset (Terminating l s)}
(hfC: fC default = default) (hS': S' = (S.image (inst.lift_terminating hfC))): Busybeaver' l s S = Busybeaver' l s S' :=
by {
  rw [hS']
  exact same_busybeaver hfC
}

end Transformation
