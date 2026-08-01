/-
This file contains the [Closed Set](https://wiki.bbchallenge.org/wiki/Closed_Set) proof technique.

The main way to use it is through the `closed_set P` tactic, which replaces a goal of `¬M.halts C`
by two goals:
- proving that `P` is closed under "progressing" steps
- proving that `C` eventually reaches an element of the set `P`

-/
-- TODO: Rewrite in terms of TM.Model rather than TM.Machine
import Busybeaver.TM.Table
import Busybeaver.Basic
import Busybeaver.TM.Table.Reachability

variable {M: TM.Table.Machine L S}

structure ClosedSet (M: TM.Table.Machine L S) (base: TM.Table.Config L S → Prop) (I: TM.Table.Config L S) where
  closed : ∀ (A: {S // base S}), ∃ (B: {S // base S}), A -[M]->+ B
  enters : ∃ (N: {S // base S}), I -[M]->* N

namespace ClosedSet

theorem offset (closed: ClosedSet M p I) (hN: p N): ClosedSet M p N :=
  ⟨closed.closed, ⟨⟨N, hN⟩, .refl⟩⟩

lemma nonHalting (inst: ClosedSet M p I): ¬M.halts I := by
  rintro ⟨final, hFinal⟩
  induction final using Nat.caseStrongRecOn generalizing I with
  | zero =>
      obtain ⟨F, hFL, hFR⟩ := hFinal
      cases hFR
      obtain ⟨⟨N, pN⟩, hN⟩ := inst.enters
      have hIN := TM.Table.Machine.halts_in.evstep_same hFL hN
      simp at hIN
      cases hIN
      obtain ⟨_, hNN'⟩ := inst.closed ⟨I, pN⟩
      exact TM.Table.Machine.halts_in.no_progress hFL hNN'
  | ind n IH =>
      obtain ⟨⟨N, pN⟩, hN⟩ := inst.enters
      obtain ⟨⟨N', pN'⟩, hNN'⟩ := inst.closed ⟨N, pN⟩
      simp_all
      have hIN' := calc I
        _ -[M]->* N := hN
        _ -[M]->+ N' := hNN'
      obtain ⟨nfin, hnfin⟩ := hIN'.to_multistep
      have hnfinn := TM.Table.Machine.halts_in.within hFinal hnfin
      have hnfinHalts := TM.Table.Machine.halts_in.precedes hFinal hnfin hnfinn
      simp [*] at hnfinn hnfinHalts
      exact IH _ (Nat.sub_le n nfin) (inst.offset pN') hnfinHalts

/-- Proves non-termination using closed set reasonning. -/
macro "closed_set" p:term : tactic =>
  `(tactic| suffices ClosedSet _ $p _ from this.nonHalting <;> constructor)
