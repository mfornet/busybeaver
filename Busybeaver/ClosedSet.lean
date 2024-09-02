import Busybeaver.Basic
import Busybeaver.Reachability

open TM

variable {M: Machine L S}

structure ClosedSet (M: Machine L S) (base: Config L S → Prop) (I: Config L S) where
  closed : ∀ (A: { S // base S }), ∃ (B: {S // base S}), A -[M]->+ B
  enters : ∃ (N: {S // base S}), I -[M]->* N

namespace ClosedSet

lemma nonHalting (inst: ClosedSet M p I): ¬M.halts I := by {
  intro ⟨final, hFinal⟩
  induction final using Nat.caseStrongInductionOn generalizing I with
  | zero => {
    obtain ⟨F, hFL, hFR⟩ := hFinal
    cases hFR
    obtain ⟨⟨N, pN⟩, hN⟩ := inst.enters
    have hIN := Machine.halts_in.evstep_same hFL hN
    obtain ⟨⟨N', pN'⟩, hNN'⟩ := inst.closed ⟨N, pN⟩
    simp_all
    exact Machine.halts_in.no_progress hFL hNN'
  }
  | ind n IH => {
    obtain ⟨⟨N, pN⟩, hN⟩ := inst.enters
    obtain ⟨⟨N', pN'⟩, hNN'⟩ := inst.closed ⟨N, pN⟩
    simp_all
    have hIN' := calc I
      _ -[M]->* N := hN
      _ -[M]->+ N' := hNN'

    obtain ⟨nfin, hnfin⟩ := hIN'.to_multistep
    have hnfinn := Machine.halts_in.within hFinal hnfin
    have hnfinHalts := Machine.halts_in.preceeds hFinal hnfin hnfinn
    simp_all
    refine IH _ ?_ ?_ hnfinHalts
    · exact Nat.sub_le n nfin
    constructor
    · exact inst.closed
    exists ⟨N', pN'⟩
    simp_all
    exact .refl
  }
}

/-- Proves non-termination using closed position set reasonning. -/
macro "closed_set" p:term : tactic =>
  `(tactic| suffices ClosedSet _ $p _ from this.nonHalting <;> constructor)
