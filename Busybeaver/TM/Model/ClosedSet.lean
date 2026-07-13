import Busybeaver.Basic
import Busybeaver.TM.Model.Reachability

namespace TM.Model

variable {M : Type _} [TM.Model M]

structure ClosedSet (m : M) (base: Config M → Prop) (I: Config M) where
  closed : ∀ (a: {S // base S}), ∃ (b: {S // base S}), a -[m]->+' b
  enters : ∃ (N: {S // base S}), I -[m]->*' N

namespace ClosedSet

theorem offset {m : M} {p : Config M → Prop} {I N : Config M}
    (closed : ClosedSet m p I) (hN : p N) : ClosedSet m p N :=
  ⟨closed.closed, ⟨⟨N, hN⟩, .refl⟩⟩

lemma nonHalting {m : M} {p : Config M → Prop} {I : Config M}
    (inst : ClosedSet m p I) : ¬halts m I := by
  intro ⟨final, hFinal⟩
  induction final using Nat.caseStrongRecOn generalizing I with
  | zero =>
      obtain ⟨F, hFL, hFR⟩ := hFinal
      cases hFR
      obtain ⟨⟨N, pN⟩, hN⟩ := inst.enters
      have hIN := halts_in_base.evstep_same hFL hN
      cases hIN
      obtain ⟨_, hNN'⟩ := inst.closed ⟨N, pN⟩
      exact halts_in_base.no_progress hFL hNN'
  | ind n IH =>
      obtain ⟨⟨N, pN⟩, hN⟩ := inst.enters
      obtain ⟨⟨N', pN'⟩, hNN'⟩ := inst.closed ⟨N, pN⟩
      have hIN' : I -[m]->+' N' := Machine.EvStep.trans_progress hN hNN'
      obtain ⟨nfin, hnfin⟩ := Progress.to_multistep hIN'
      have hnfinn := halts_in_base.within hFinal hnfin
      have hnfinHalts := halts_in_base.preceeds hFinal hnfin hnfinn
      refine IH _ ?_ (inst.offset pN') hnfinHalts
      rw [Nat.succ_sub_succ_eq_sub]
      exact Nat.sub_le n nfin

end ClosedSet

end TM.Model
