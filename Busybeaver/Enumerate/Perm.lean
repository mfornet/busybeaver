import Mathlib.Tactic
import Busybeaver.Basic
import Busybeaver.Reachability
import Busybeaver.Enumerate.Basic

namespace TM.Machine

variable {M: Machine l s}

@[simp]
def swap (q q': Label l) (lab: Label l): Label l :=
  if lab = q then q' else if lab = q' then q else lab

@[simp]
lemma swap_swap: swap q q' (swap q' q lab) = lab :=
  by {
    by_cases hq: q = q' <;> {
      simp
      repeat split <;> simp_all
    }
  }

@[simp]
lemma swap_left: swap q q' q = q' := by simp

def stmt_perm (S: Stmt l s) (q q': Label l): Stmt l s := match S with
| .halt => .halt
| .next sym dir nlab => .next sym dir (swap q q' nlab)

def perm (M: Machine l s) (q q': Label l): Machine l s :=
  λ lab sym ↦ stmt_perm (if lab = q then M q' sym else if lab = q' then M q sym else M lab sym) q q'

lemma perm.single (h: A -[M]-> B): ⟨q', A.tape⟩ -[M.perm A.state q']-> ⟨swap A.state q' B.state, B.tape⟩ :=
  by {
    unfold Machine.step at h
    split at h
    · contradiction
    rename_i sym dir lab' hlab
    cases h
    simp
    simp [Machine.step, perm, stmt_perm]
    split
    · rename_i heq
      split at heq
      · rename_i heq'
        split at heq'
        · rename_i hAq'
          simp [hAq', hlab] at heq'
        · simp [hlab] at heq'
      · rename_i heq'
        split at heq' <;> contradiction
    · rename_i heq'
      split at heq'
      · contradiction
      cases heq'
      rename_i heq'
      split at heq'
      · rename_i hAq'
        simp only [hAq', hlab] at heq'
        cases heq'
        simp
      · simp only [hlab] at heq'
        cases heq'
        simp
  }

lemma perm.simu (h: A -[M]{n}-> B): ⟨swap q q' A.state, A.tape⟩ -[M.perm q q']{n}-> ⟨swap q q' B.state, B.tape⟩ :=
  by induction n generalizing B with
  | zero => {
    cases h
    simp
    exact .refl
  }
  | succ n IH => {
    obtain ⟨C, hAC, hCB⟩ := h.split
    obtain hqp := IH hAC
    have hMCB := hCB.single'

    have hMCBs : M C.state C.tape.head ≠ .halt := by {
      intro h
      simp [Machine.step, h] at hMCB
    }

    calc ⟨swap q q' A.state, A.tape⟩
      _ -[M.perm q q']{n}-> ⟨_, C.tape⟩ := hqp
      _ -[M.perm q q']{1}-> ⟨_, B.tape⟩ := by {
        apply Multistep.single
        simp [Machine.step, perm, stmt_perm]
        split
        · rename_i heq
          split at heq <;> {
            rename_i heq'
            repeat split at heq' <;> simp_all
          }
        · simp [Machine.step] at hMCB
          rename_i heq
          split at hMCB
          · contradiction
          cases hMCB
          split at heq <;> {
            rename_i heq'
            repeat split at heq' <;> simp_all
          }
    }
  }

lemma perm.simu' (h: A-[M.perm q q']{n}-> B): ⟨swap q' q A.state, A.tape⟩ -[M]{n}-> ⟨swap q' q B.state, B.tape⟩ :=
  by induction n generalizing B with
  | zero => {
    cases h
    simp
    exact .refl
  }
  | succ n IH => {
    obtain ⟨C, hAC, hCB⟩ := h.split

    obtain hqp := IH hAC
    have hMCB := hCB.single'

    have hMCBs : (M.perm q q') C.state C.tape.head ≠ .halt := by {
      intro h
      simp [Machine.step, h] at hMCB
    }

    calc ⟨swap q' q A.state, A.tape⟩
      _ -[M]{n}-> ⟨_, C.tape⟩ := hqp
      _ -[M]{1}-> ⟨_, B.tape⟩ := by {
        apply Multistep.single
        simp [Machine.step] at hMCB
        split at hMCB
        · contradiction
        cases hMCB
        rename_i hMCB
        simp [perm, stmt_perm] at hMCB
        split at hMCB
        · contradiction
        cases hMCB

        rename_i heq
        split at heq
        · simp [Machine.step]
          split
          · rename_i heq'
            simp_all
          · rename_i heq'
            split at heq' <;> repeat split <;> simp_all
        · simp [Machine.step]
          split
          · rename_i heq'
            split at heq' <;> simp_all
          · rename_i heq'
            split at heq
            · simp_all [perm, stmt_perm]
              repeat split <;> simp_all
            · simp_all [perm, stmt_perm]
              repeat split <;> simp_all
              · by_cases hqq': q = q'
                · simp_all
                · split <;> simp_all
              · split <;> simp_all
    }
  }

lemma perm.last (h: M.LastState C): (M.perm q q').LastState ⟨swap q q' C.state, C.tape⟩ :=
  by {
    simp_all [Machine.LastState]
    apply Machine.step.none at h
    simp [Machine.step, perm, stmt_perm]
    split
    · rename_i heq
      split at heq
      · cases heq
        rename_i heq
        repeat split at heq <;> simp_all
      · cases heq
    · rename_i heq
      split at heq
      · cases heq
      · cases heq
        rename_i heq
        repeat split at heq <;> simp_all
  }

lemma perm.last' (h: (M.perm q q').LastState C): M.LastState ⟨swap q' q C.state, C.tape⟩ :=
  by {
    simp_all [Machine.LastState]
    apply Machine.step.none at h
    simp_all [Machine.step, perm, stmt_perm]
    split at h
    · rename_i heq
      split at heq <;> split <;> {
        rename_i heq'
        split at heq' <;> simp_all
      }
    · cases h
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
