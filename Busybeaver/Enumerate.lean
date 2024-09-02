/-
How to enumerate turing machines.

Note that we take heavy inspiration of busycoq here.
-/

import Mathlib.Tactic
import Busybeaver.Basic
import Busybeaver.Reachability

namespace TM

variable {M: Machine l s}

namespace Machine

inductive ZVisits (M: Machine l s): Label l → List (Label l) → Prop
| halts : M q default = .halt → M.ZVisits q []
| symNZ : ∀ q sym dir labh, M q default = .next sym dir labh → sym ≠ default → M.ZVisits q []
| symZ : ∀ q dir nlab labt, M q default = .next default dir nlab → M.ZVisits nlab labt → M.ZVisits q (nlab :: labt)

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

section Perm

@[simp]
private def swap (q q': Label l) (lab: Label l): Label l :=
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

private def stmt_perm (S: Stmt l s) (q q': Label l): Stmt l s := match S with
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

end Perm

namespace ZVisits

lemma deterministic (h₁: M.ZVisits q L₁) (h₂: M.ZVisits q L₂): L₁ = L₂ :=
  by induction h₁ generalizing L₂ with
  | halts | symNZ => {
    cases h₂ <;> simp_all
  }
  | symZ q dir nlab labt hqn _ IH₁ => {
    induction h₂ with simp_all
    | symZ q₂ dir₂ nlab₂ labt₂ _ v₂ => {
      apply IH₁
      exact v₂
    }
  }

lemma in_split (h: M.ZVisits q L) (h': q' ∈ L): ∃n, M.ZVisits q' (L.drop (n + 1)) :=
  by induction h with simp_all
  | symZ q dir nlab labt qn v IH => {
    rcases h' with h' | h'
    swap
    · obtain ⟨n, hn⟩ := IH h'
      exists (n + 1)
    by_contra hn
    simp_all
    specialize hn 0
    simp_all
  }

lemma not_in (h: M.ZVisits q L): ¬(q ∈ L) :=
  by {
    intro hq
    obtain ⟨n, hn⟩ := in_split h hq
    have hLe := deterministic h hn
    have hLl : L.length = (L.drop (n + 1)).length := by congr
    rw [List.length_drop] at hLl
    cases L with
    | nil => contradiction
    | cons he ta => {
      suffices (he :: ta).length < (he :: ta).length by {
        simp at this
      }
      calc (he :: ta).length
      _ ≤ (he :: ta).length - (n + 1) := Nat.le_of_eq hLl
      _ < (he :: ta).length := by {
        apply Nat.sub_lt <;> simp
      }
    }
  }

lemma nodup (h: M.ZVisits q L): L.Nodup :=
  by induction h with
  | halts | symNZ => exact List.nodup_nil
  | symZ _ _ nlab labt _ v IH => {
    refine List.Nodup.cons ?symNZ.ha IH
    exact not_in v
  }

lemma bound (h: M.ZVisits q L): L.length < Fintype.card (Label l) :=
  by {
    suffices L.toFinset.card < Fintype.card (Label l) by {
      rw [Eq.symm (List.toFinset_card_of_nodup (nodup h))]
      exact this
    }
    rw [← Finset.card_univ]
    apply Finset.card_lt_card
    constructor
    · exact Finset.subset_univ L.toFinset
    rw [Finset.not_subset]
    exists q
    constructor
    · exact Finset.mem_univ q
    · simp
      exact not_in h
  }

section ZeroTape
/-
Lemmas about the default tape, writing to it, and moving it
-/

@[simp]
lemma default_write_default: (Turing.Tape.write (Γ:=Symbol s) default default) = default :=
  by {
    suffices hCons: Turing.ListBlank.cons (Γ:=Symbol s) default default = default by {
      simp_all [Turing.Tape.write, hCons, default]
    }

    apply Turing.ListBlank.ext
    intro i
    induction i <;> {
      simp
      rfl
    }
  }

@[simp]
lemma default_move: (Turing.Tape.move (Γ:=Symbol s) dir default) = default :=
  by {
    suffices hCons: Turing.ListBlank.cons (Γ:=Symbol s) default default = default by {
      cases dir <;> {
        simp_all [Turing.Tape.move, hCons, default]
        trivial
      }
    }

    apply Turing.ListBlank.ext
    intro i
    induction i <;> {
      simp
      rfl
    }
  }

end ZeroTape

lemma from_halts (hM: M.halts { state := q, tape := default }): ∃L, M.ZVisits q L :=
  by {
    let ⟨n, cfin, hcFin, hcR⟩ := hM
    generalize h : Config.mk (s:=s) q default = C
    simp_all
    induction hcR generalizing q with
    | refl => {
      simp [Machine.LastState] at hcFin
      apply Machine.step.none at hcFin
      simp_all [default, ← h]
      exists []
      constructor
      trivial
    }
    | @succ q' nxt C n step hn IH => {
      simp_all [← h, -h]
      simp [Machine.step] at step
      split at step; simp at *
      rename_i sym dir nlab hnlab

      by_cases h_sym: sym = default
      swap
      · exists []
        apply symNZ
        · exact hnlab
        · exact h_sym

      suffices hL: ∃L, M.ZVisits nlab L by {
        obtain ⟨L, hL⟩ := hL
        exists nlab :: L
        constructor
        · simp_all
          trivial
        · exact hL
      }

      apply IH
      · have hq : ⟨q, default⟩ -[M]-> nxt := by simp_all [Machine.step]
        exact Machine.halts.tail (.single hq) hM

      rw [h_sym, default_write_default, default_move] at step
      simp_all
    }
  }

/--
If a machine visits a certain list of states without writing non-zero, then we can build another TM such that:
- It directly writes non-zero
- It is equi-halting with the original TM
-/
lemma equi (hM: M.ZVisits q L): ∃ (M': Machine l s), M'.ZVisits q [] ∧ equi_halts M M' ⟨q, default⟩ ⟨q, default⟩ :=
  by induction hM with
  /-
  The first two cases are not interesting

  M directly writes non-zero, so it is already in the good form
  -/
  | @halts q' hq' => {
    exists M
    constructor
    · exact halts hq'
    · exact equi_halts.refl
  }
  | symNZ q sym dir labh hlab v => {
    exists M
    constructor
    · exact symNZ _ _ _ _ hlab v
    · exact equi_halts.refl
  }
  | symZ q dir nlab labt hq v IH => {
    obtain ⟨M', hV, hEq⟩ := IH
    by_cases hql: q = nlab
    /-
      First case: the original machine trivially loops forever, writing 0s
    -/
    · simp_all
      exists M'

    /-
      Second case: q and nlab are different states

      We know (by induction):

      {q, default} -[M]{1}-> {nlab, default} -[M]->  ...
                                                      ^
                                                      | equi_halts
                                                      v
                             {nlab, default} -[M']-> ...

      The idea is then relatively simple: _swap_ states q and nlab in M' (call this TM Mtrans).
      We thus get:
      {q, default} -[M]{1}-> {nlab, default} -[M]->  ...
                                                      ^
                                                      | equi_halts
                                                      v
      {q, default} -[Mtrans]->                       ...
    -/
    exists M'.perm nlab q

    /-
    Equi halting is actually pretty simple,
    We just have to "allign" M and M' first, and then M' and Mtrans are equihalting by
    construction (see [perm.equiv])
    -/
    have hMq : ⟨q, default⟩ -[M]-> ⟨nlab, default⟩ := by {
      simp [Machine.step]
      split
      · rename_i heq
        simp [default] at heq hq
        rw [hq] at heq
        cases heq
      · rename_i heq
        simp [default] at heq hq
        rw [hq] at heq
        cases heq
        simp
        apply default_move
    }

    have hMEqM'q : equi_halts M M' ⟨q, default⟩ ⟨nlab, default⟩ := by {
      apply equi_halts.mono
      · exact Multistep.single hMq
      · exact hEq
    }

    constructor
    swap
    · apply equi_halts.trans hMEqM'q
      exact perm.equiv

    /-
    Now we need to prove that Mtrans does not write any 0 on the first state
    This is a consequence of the construction of Mtrans with regard to M'
    -/
    cases hV with
    | halts hV => {
      /-
      M' halts directly: Mtrans halts directly too
      -/
      apply ZVisits.halts
      simp [perm, stmt_perm] at *
      split <;> {
        rename_i heq
        split at heq <;> simp_all
      }
    }
    | symNZ _ sym dir labh symnxt symne => {
      /-
      M' writes a non-zero symbol

      Here we have to be a little smarter because Mtrans and M' will have
      different output states the new state of Mtrans being the translated state of M'
      -/
      apply ZVisits.symNZ _ sym dir (swap nlab q labh)
      · simp [perm, stmt_perm] at *
        split
        · rename_i heq
          split at heq <;> simp_all
        · rename_i heq
          split at heq
          simp_all
          rw [symnxt] at heq
          cases heq
          simp_all
      · exact symne
    }
  }

lemma decide (M: Machine l s) (q: Label l): ∃L, M.ZVisits q L := sorry

/--
It is sufficient to only consider machines with empty ZVisits.

_The_ theorem of interest.

This is formalized as: assume there is an algorithm that decides if a TM
with empty ZVisits, then we can use this algorithm to decide for all TMs
-/
theorem only_nz (decider: ∀(M': Machine l s), (M'.ZVisits q []) → M'.halts ⟨q, default⟩ ∨ ¬(M'.halts ⟨q, default⟩)): M.halts ⟨q, default⟩ ∨ ¬(M.halts ⟨q, default⟩) := by {
  obtain ⟨L, hL⟩ := (decide M q)
  obtain ⟨M', hM'z, hM'h⟩ := hL.equi
  cases decider M' hM'z with
  | inl hM' => {
    left
    unfold equi_halts at hM'h
    rw [hM'h]
    exact hM'
  }
  | inr hM'n => {
    right
    unfold equi_halts at hM'h
    rw [hM'h]
    exact hM'n
    }
  }

end ZVisits

end Machine
