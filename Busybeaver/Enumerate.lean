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

end equi_halts

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

      suffices hD: (Turing.Tape.write (Γ:=Symbol s) default default |>.move dir) = default by {
        simp only [h_sym, hD] at step
        cases step
        rfl
      }

      suffices hCons: Turing.ListBlank.cons (Γ:=Symbol s) default default = default by {
        cases dir <;> {
          simp_all [Turing.Tape.move, Turing.Tape.write, hCons, default]
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
    -- cases hcR with
    -- | refl => {
    -- }
    -- | @succ _ nxt _ n stp hn => {
    --   simp [Machine.step] at stp
    --   simp [default] at hnlab
    --   simp at *
    --   by_cases h_sym: sym = default
    --   swap
    --   · exists []
    --     apply Machine.ZVisits.symNZ
    --     · exact hnlab
    --     · exact h_sym

    --   suffices hL: ∃ L, M.ZVisits nlab L by {
    --     obtain ⟨L, hL⟩ := hL
    --     exists nlab :: L
    --     constructor
    --     · simp_all
    --       trivial
    --     · exact hL
    --   }

    --   apply from_halts
    --   apply halts.tail


    --     -- apply from_halts
    --     -- apply halts.tail
    --     -- · apply Machine.Multistep.single (A:=?A) (by {
    --     --     simp [Machine.step]
    --     --   })
    --     --   simp [Machine.step]
    --     --   have hD:  := by {
    --     --     unfold Turing.Tape.write
    --     --     unfold Turing.Tape.move
    --     --     intro L
    --     --     sorry
    --     --   }
    --     -- · exact hM
    --   }
    -- }
  }

/--
If a machine visits a certain list of states without writing non-zero, then we can build another TM such that:
- It directly writes non-zero
- It is equi-halting with the original TM
-/
lemma equi (hM: M.ZVisits q L): ∃ (M': Machine l s), ∃ q', M'.ZVisits q' [] ∧ equi_halts M M' ⟨q, default⟩ ⟨q', default⟩ :=
  by induction hM with
  | @halts q' hq' => {
    exists M
    exists q'
    constructor
    · exact halts hq'
    · exact equi_halts.refl
  }
  | symNZ q sym dir labh hlab v => {
    exists M
    exists q
    constructor
    · exact symNZ _ _ _ _ hlab v
    · exact equi_halts.refl
  }
  | symZ q dir nlab labt hq v IH => {
    obtain ⟨M', q', hV, hEq⟩ := IH
    by_cases hql: q = nlab
    /-
      First case: the original machine trivially loops forever, writing 0s
    -/
    · simp_all
      exists M'
      exists q'

    /-
      Second case: q and nlab are different states

      The new machine is the _swap_ of states nlab and q' in M'
    -/
    let Mtrans: Machine l s := λ lab ↦ if lab = nlab then M' q else if lab = q then M' nlab else M' lab

    have hMtrans : equi_halts M' Mtrans ⟨q', default⟩ ⟨nlab, default⟩ := by {
      constructor
      · intro ⟨n, C, hCf, hCr⟩
        exists n
        exists C
        cases hCr with
        | refl => {
          constructor
          · simp [Machine.LastState] at *
            apply Machine.step.none at hCf
            simp at hCf
            simp [Machine.step, Mtrans, hql]
            split
            · rfl
            simp_all

        }

    }
    exists Mtrans
    obtain ⟨hEqMM', hEqM'M⟩ := hEq
    cases hV with
    | halts hnlab' => {
      constructor
      · apply ZVisits.halts
        simp [hql]
        trivial
      constructor
      · intro ⟨n, C, hC⟩
    }
    -- constructor
    -- · cases hV with
    --   | halts => {
    --     apply ZVisits.halts
    --     simp [hql]
    --     trivial
    --   }
    --   | symNZ _ sym' dir' labh' hM' sym'ne => {
    --     apply ZVisits.symNZ
    --     · simp [hql]
    --       exact hM'
    --     · exact sym'ne
    --   }
    --   constructor
    --   · intro hMh

    --     -- specialize hEqMM' hMh
  }

end ZVisits


-- def ZVisits (M: Machine l s) (q: Label l): List (Label l) := match M q default with
-- | .halt => []
-- | .next sym dir q' => if sym = default then [] else q' :: (M.ZVisits q')
-- termination_by M.ZVisitsP q
-- decreasing_by {
-- }

end Machine
