import Mathlib.Tactic
import Busybeaver.Basic
import Busybeaver.Reachability
import Busybeaver.Enumerate.Basic

namespace TM.Machine

variable {M: Machine l s}

def swap (q q': Label l) (lab: Label l): Label l :=
  if lab = q then q' else if lab = q' then q else lab

@[simp]
lemma swap_id: swap q q q' = q' :=
by {
  simp [swap]
  split <;> simp_all
}

@[simp]
lemma swap_left: swap q q' q = q' :=
by simp [swap]

@[simp]
lemma swap_right: swap q q' q' = q :=
by simp [swap]

@[simp]
lemma swap_swap: swap q q' (swap q' q lab) = lab :=
  by {
    by_cases hq: q = q' <;> {
      simp [swap]
      repeat split <;> simp_all
    }
  }

@[simp]
lemma swap_left_eq: swap q q' lab = q ↔ lab = q' :=
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
lemma swap_right_eq: swap q q' lab = q' ↔ lab = q :=
by {
  by_cases hqq: q = q'
  · simp_all
  simp [swap]
  split <;> simp_all
}

@[simp]
lemma swap_ne (hq: lab ≠ q) (hq': lab ≠ q'): swap q q' lab = lab :=
by {
  simp [swap]
  repeat split <;> simp_all
}

def stmt_perm (S: Stmt l s) (q q': Label l): Stmt l s := match S with
| .halt => .halt
| .next sym dir nlab => .next sym dir (swap q q' nlab)

def perm (M: Machine l s) (q q': Label l): Machine l s :=
  λ lab sym ↦ stmt_perm (if lab = q then M q' sym else if lab = q' then M q sym else M lab sym) q q'

lemma perm.single (h: A -[M]-> B): ⟨swap q q' A.state, A.tape⟩ -[M.perm q q']-> ⟨swap q q' B.state, B.tape⟩ :=
by {
  obtain ⟨sym, dir, hsymdirB, hsymdirC⟩ := Machine.step.some_rev h
  refine Machine.step.some' (sym:=A.tape.head) (dir:=dir) (q':=swap q q' B.state) (sym':=sym) ?_ (by rfl) hsymdirC
  simp [perm, stmt_perm]
  split <;> {
    rename_i heq
    repeat split at heq <;> simp_all
  }
}

lemma perm.single_rev (h: A -[M.perm q q']-> B): ⟨swap q' q A.state, A.tape⟩ -[M]-> ⟨swap q' q B.state, B.tape⟩ :=
by {
  obtain ⟨sym, dir, hsymdirA, hsymdirB⟩ := Machine.step.some_rev h
  refine Machine.step.some' (sym:=A.tape.head) (dir:=dir) (q':=swap q' q B.state) (sym':=sym) ?_ (by rfl) hsymdirB
  simp [perm, stmt_perm] at hsymdirA

  split at hsymdirA
  · cases hsymdirA
  · simp_all
    rename_i heq
    split at heq
    · simp_all [← hsymdirA.2.2]
    split at heq
    · simp_all [← hsymdirA.2.2]
    · simp_all [← hsymdirA.2.2]
}

lemma perm.simu (h: A -[M]{n}-> B): ⟨swap q q' A.state, A.tape⟩ -[M.perm q q']{n}-> ⟨swap q q' B.state, B.tape⟩ :=
by induction n generalizing B with
| zero => {
  cases h
  exact .refl
}
| succ n IH => {
  obtain ⟨C, hAC, hCB⟩ := h.split
  obtain hqp := IH hAC
  have hMCB := hCB.single'

  calc ⟨swap q q' A.state, A.tape⟩
    _ -[M.perm q q']{n}-> ⟨_, C.tape⟩ := hqp
    _ -[M.perm q q']{1}-> ⟨_, B.tape⟩ := by {
      apply Multistep.single
      exact perm.single hMCB
  }
}

lemma perm.simu' (h: A-[M.perm q q']{n}-> B): ⟨swap q' q A.state, A.tape⟩ -[M]{n}-> ⟨swap q' q B.state, B.tape⟩ :=
by induction n generalizing B with
| zero => {
  cases h
  exact .refl
}
| succ n IH => {
  obtain ⟨C, hAC, hCB⟩ := h.split

  obtain hqp := IH hAC
  have hMCB := hCB.single'

  calc ⟨swap q' q A.state, A.tape⟩
    _ -[M]{n}-> ⟨_, C.tape⟩ := hqp
    _ -[M]{1}-> ⟨_, B.tape⟩ := by {
      apply Multistep.single
      exact perm.single_rev hMCB
  }
}

lemma perm.last (h: M.LastState C): (M.perm q q').LastState ⟨swap q q' C.state, C.tape⟩ :=
by {
  simp_all [Machine.LastState]
  simp [perm, stmt_perm]
  split <;> {
    rename_i heq
    repeat split at heq <;> simp_all
  }
}

lemma perm.last' (h: (M.perm q q').LastState C): M.LastState ⟨swap q' q C.state, C.tape⟩ :=
by {
  simp_all [Machine.LastState]
  simp [perm, stmt_perm] at h
  split at h <;> {
    rename_i heq
    repeat split at heq <;> simp_all
  }
}

lemma perm.equiv: equi_halts M (M.perm q q') ⟨q, T⟩ ⟨q', T⟩ :=
by {
  constructor
  · intro ⟨n, C, hCf, hCr⟩
    exists n
    exists ⟨swap q q' C.state, C.tape⟩
    constructor
    · exact perm.last hCf
    · conv =>
        pattern Config.mk q' T
        rw [← show swap q q' q = q' by simp]
      exact perm.simu hCr
  · intro ⟨n, C, hCf, hCr⟩
    exists n
    exists ⟨swap q' q C.state, C.tape⟩
    constructor
    · exact perm.last' hCf
    · conv =>
        pattern Config.mk q T
        rw [← show swap q' q q' = q by simp]
      exact perm.simu' hCr
}
