/-
This file is concerned with the starting "0 states" of a machine, i.e. those that write zeros on the initial tape.

Definitions are inspired by busycoq.
-/

import Mathlib.Tactic
import Busybeaver.Basic
import Busybeaver.Reachability
import Busybeaver.Enumerate.Basic
import Busybeaver.Enumerate.Perm

-- Used when build the set of ZVisit states
import Busybeaver.ClosedSet

namespace TM

variable {M: Machine l s}

namespace Machine

inductive ZVisits (M: Machine l s): Label l → List (Label l) → Prop
| halts : M q default = .halt → M.ZVisits q []
| symNZ : ∀ q sym dir labh, M q default = .next sym dir labh → sym ≠ default → M.ZVisits q []
| symZ : ∀ q dir nlab labt, M q default = .next default dir nlab → M.ZVisits nlab labt → M.ZVisits q (nlab :: labt)

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

lemma bound (h: M.ZVisits q L): L.length ≤ l :=
  by {
    suffices L.toFinset.card < Fintype.card (Label l) by {
      rw [Eq.symm (List.toFinset_card_of_nodup (nodup h))]
      apply Nat.le_of_lt_succ
      calc L.toFinset.card
        _ < Fintype.card (Label l) := this
        _ ≤ l + 1 := by {
          conv =>
            lhs
            simp
        }
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

@[simp]
lemma default_write_move: (Turing.Tape.move (Γ:=Symbol s) dir (Turing.Tape.write 0 default)) = default := by {
  have hD: Turing.Tape.write (Γ:=Symbol s) default default = default := default_write_default
  simp at hD
  simp [*]
}

end ZeroTape

instance decidable: Decidable (M.ZVisits q L) := by {
  induction L generalizing q with
  | nil => {
    cases hM: M q default with
    | halt => {
      apply isTrue
      exact halts hM
    }
    | next sym dir nlab => {
      by_cases hsym: sym ≠ default
      · apply isTrue
        exact symNZ q sym dir nlab hM hsym
      · apply isFalse
        intro hM'
        cases hM' <;> simp_all
    }
  }
  | cons he ta IH => {
    cases hM: M q default with
    | halt => {
      apply isFalse
      intro hM'
      cases hM'
      simp_all
    }
    | next sym dir nlab => {
      by_cases hhe : he ≠ nlab
      · apply isFalse
        intro hM'
        cases hM'
        simp_all
      simp_all
      by_cases hsym: sym ≠ default
      · apply isFalse
        intro hM'
        cases hM'
        simp_all
      simp_all
      cases @IH nlab with
      | isTrue hM' => {
        apply isTrue
        constructor
        · exact hM
        · exact hM'
      }
      | isFalse hM' => {
        apply isFalse
        intro hM''
        apply hM'
        cases hM''
        trivial
      }
    }
  }
}

lemma from_halts (hM: M.halts { state := q, tape := default }): ∃L, M.ZVisits q L :=
  by {
    let ⟨n, cfin, hcFin, hcR⟩ := hM
    generalize h : Config.mk (s:=s) q default = C
    simp_all
    induction hcR generalizing q with
    | refl => {
      simp [Machine.LastState] at hcFin
      simp_all [default, ← h]
      exists []
      constructor
      trivial
    }
    | @succ q' nxt C n step hn IH => {
      simp_all [← h, -h]
      have ⟨sym, dir, hdirnxt, hdirnxt'⟩ := Machine.step.some_rev step
      simp_all

      by_cases h_sym: sym = default
      swap
      · exists []
        apply symNZ
        · exact hdirnxt
        · exact h_sym

      suffices hL: ∃L, M.ZVisits nxt.state L by {
        obtain ⟨L, hL⟩ := hL
        exists nxt.state :: L
        constructor
        · simp_all
          trivial
        · exact hL
      }

      simp_all
      apply IH
      · exists n
        exists C

      rw [← hdirnxt']
    }
  }

/--
If a machine visits a certain list of states without writing non-zero, then we can build another TM such that:
- It directly writes non-zero
- It is equi-halting with the original TM
-/
lemma equi (hM: M.ZVisits q L): ∃ (M': Machine l s), M'.ZVisits q [] ∧ (M, ⟨q, default⟩) =H (M', ⟨q, default⟩) :=
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

    constructor
    swap
    · /-
      Equi halting is actually pretty simple,
      We just have to "allign" M and M' first, and then M' and Mtrans are equihalting by
      construction (see [perm.equiv])
      -/
      calc (M, ⟨q, default⟩)
        _ =H (M, ⟨nlab, default⟩) := by {
          apply equi_halts.mono (n:=1)
          apply Multistep.single
          apply Machine.step.some' hq
          · simp [default]
          · simp
        }
        _ =H (M', ⟨nlab, default⟩) := hEq
        _ =H (M'.perm nlab q, ⟨q, default⟩) := by {
          conv =>
            pattern (occs:=2) q
            rw [show q = swap nlab q nlab by simp]
          exact perm.equiv
        }
    · /-
      Now we need to prove that Mtrans does not write any 0 on the first state
      This is a consequence of the construction of Mtrans with regard to M'
      -/
      cases hV with
      | halts hV => {
        /-
        M' halts directly: Mtrans halts directly too
        -/
        apply ZVisits.halts
        simp [perm] at *
        split <;> simp_all
      }
      | symNZ _ sym dir labh symnxt symne => {
        /-
        M' writes a non-zero symbol

        Here we have to be a little smarter because Mtrans and M' will have
        different output states the new state of Mtrans being the translated state of M'
        -/
        apply ZVisits.symNZ _ sym dir (swap nlab q labh)
        · simp [perm] at *
          split <;> simp_all
        · exact symne
      }
  }

def decide (M: Machine l s) (q: Label l): (∃L, M.ZVisits q L) ∨ (¬M.halts ⟨q, default⟩) :=
  let rec decideInner (q': Label l) (cur: Finset (Label l)) (bound: ℕ)
    (hq': q' ∉ cur)
    (hcur: ∀ q'' ∈ cur, ∃dir nlab, M q'' default = .next default dir nlab ∧ (nlab ∈ cur ∨ nlab = q'))
    (_h: bound + cur.card = l + 1): (∃L, M.ZVisits q' L) ∨ (¬M.halts ⟨q', default⟩) := match bound with
  | .zero => by {
    simp_all
    right
    have hcur': cur ⊂ Finset.univ := by {
      refine Finset.ssubset_iff.mpr ?_
      exists q'
      constructor
      · exact hq'
      · exact Finset.subset_univ (insert q' cur)
    }
    have hcurcard: cur.card < l + 1 := by calc cur.card
      _ < (Finset.univ (α:=Label l)).card := Finset.card_lt_card hcur'
      _ = l + 1 := by simp
    apply absurd hcurcard
    simp
    exact Nat.le_of_eq _h.symm
  }
  | .succ n => match hM : M q' default with
  | .halt => by {
    left
    exists []
    exact halts hM
  }
  | .next sym dir nlab => by {
    by_cases hsym: sym ≠ default
    · left
      exists []
      exact symNZ q' sym dir nlab hM hsym
    by_cases hnlab: nlab ∈ cur
    · right
      suffices ClosedSet M (λ C ↦ C.state ∈ insert q' cur ∧ C.tape = default) ⟨q', default⟩ from this.nonHalting
      constructor
      · intro ⟨⟨Cstate, Ctape⟩, hCcur, hCdef⟩
        simp at hCcur
        simp [*]
        rcases hCcur with hCcur | hCcur
        · simp at *
          exists ⟨nlab, default⟩
          simp_all
          apply Progress.from_multistep (n:=0)
          simp
          apply Multistep.single
          apply Machine.step.some' hM
          · simp [default]
          · simp
        · obtain ⟨Cdir, Cnlab, hCnlab, hCnlabq'⟩ := hcur Cstate hCcur
          exists ⟨Cnlab, default⟩
          simp [*]
          constructor
          · exact hCnlabq'.symm
          apply Progress.from_multistep (n:=0)
          simp
          apply Multistep.single
          simp at hCdef
          apply Machine.step.some' hCnlab
          · simp [hCdef, default]
          · simp [hCdef]
      · simp_all
        exists ⟨q', default⟩
        simp [*]
        exact EvStep.refl
    by_cases hlabq' : nlab = q'
    · right
      simp [*] at *
      suffices ClosedSet M (λ C ↦ C.state = q' ∧ C.tape = default) ⟨q', default⟩ from this.nonHalting
      constructor
      · intro ⟨⟨Q's, Q't⟩, hQ's, hQ't⟩
        simp at hQ's hQ't
        cases hQ's
        cases hQ't
        simp
        exists ⟨q', default⟩
        simp
        apply Progress.from_multistep (n:=0)
        simp
        apply Multistep.single
        apply Machine.step.some' hM
        · simp [default]
        · simp [*]
      · simp
        exists ⟨q', default⟩
        simp
        exact EvStep.refl
    simp at hsym
    have res := decideInner nlab (insert q' cur) n (by {
      simp_all
    }) (by {
      intro q'' hq''
      simp at hq''
      rcases hq'' with hq'' | hq''
      · exists dir
        exists nlab
        simp_all
      · obtain ⟨dir'', nlab'', hqdirnlab'', hq''nxt⟩ := hcur q'' hq''
        exists dir''
        exists nlab''
        simp_all
        left
        exact hq''nxt.symm
    }) (by {
      simp_all
      linarith
    })

    rcases res with ⟨L, hL⟩ | term
    · left
      exists nlab :: L
      have hQ': M.ZVisits q' (nlab :: L) := by {
        simp_all
        exact symZ q' dir nlab L hM hL
      }
      exact hQ'
    · right
      refine halts.skip_next ?_ term
      simp [Machine.step]
      split
      · rename_i heq
        simp_all [default]
      rename_i heq
      simp [default] at hM heq
      rw [hM] at heq
      cases heq
      simp [hsym]
  }
  decideInner q ∅ (l + 1) (by {
    simp
  }) (by simp) (by simp)

/--
It is sufficient to only consider machines with empty ZVisits.

_The_ theorem of interest.

This is formalized as: assume there is an algorithm that decides for TMs
with empty ZVisits, then we can use this algorithm to decide for all TMs
-/
theorem only_nz (decider: ∀(M': Machine l s), (∃ sym dir nlab, M' q default = .next sym dir nlab ∧ sym ≠ default) → M'.halts ⟨q, default⟩ ∨ ¬(M'.halts ⟨q, default⟩)): M.halts ⟨q, default⟩ ∨ ¬(M.halts ⟨q, default⟩) := by {
  rcases decide M q with ⟨L, hL⟩ | term
  · obtain ⟨M', hM'z, hM'h⟩ := hL.equi
    rw [equi_halts.decider hM'h]
    cases hM'z with
    | halts hM' => {
      left
      exists 0
      apply halts_in.from_last
      simp [LastState]
      exact hM'
    }
    | symNZ _ sym dir nlab symnxt symne => {
      apply decider
      exists sym
      exists dir
      exists nlab
    }
  · right
    exact term
}

end ZVisits

end Machine
