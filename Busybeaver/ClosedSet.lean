/-
This file contains the [Closed Set](https://wiki.bbchallenge.org/wiki/Closed_Set) proof technique.

The main way to use it is through the `closed_set P` tactic, which replaces a goal of `¬M.halts C`
by two goals:
- proving that `P` is closed under "progressing" steps
- proving that `C` eventually reaches an element of the set `P`

-/
import Busybeaver.Basic
import Busybeaver.Reachability

open TM

variable {M: Machine L S}

structure ClosedSet (M: Machine L S) (base: Config L S → Prop) (I: Config L S) where
  closed : ∀ (A: {S // base S}), ∃ (B: {S // base S}), A -[M]->+ B
  enters : ∃ (N: {S // base S}), I -[M]->* N

namespace ClosedSet

def offset (closed: ClosedSet M p I) (hN: p N): ClosedSet M p N :=
by use closed.closed, ⟨N, hN⟩, .refl

lemma nonHalting (inst: ClosedSet M p I): ¬M.halts I := by {
  intro ⟨final, hFinal⟩
  induction final using Nat.caseStrongRecOn generalizing I with
  | zero => {
    /-
    Assume that I is the final state.

    Based on that, I itself is necessarily in the closed set (e.g. I is the state mentionned in
    .enters). This is a contradiction because that would mean we can step from I.
    -/
    obtain ⟨F, hFL, hFR⟩ := hFinal
    cases hFR
    obtain ⟨⟨N, pN⟩, hN⟩ := inst.enters
    have hIN := Machine.halts_in.evstep_same hFL hN
    simp at hIN
    cases hIN

    -- Here, we know that I is in the closed set, we use the closure of the set to get a
    -- contradiction

    obtain ⟨_, hNN'⟩ := inst.closed ⟨I, pN⟩
    exact Machine.halts_in.no_progress hFL hNN'
  }
  | ind n IH => {
    /-
    Now assume we need to take a non-zero number of steps to stop, say n+1 steps.

    We have:

    I -[M]->* N -[M]->+ N' ...
        ^ .enters
                  ^ .closed

    We can _offset_ the closed set instance to that N', we know we took at least one step too to get
    to N'. Thus, by property of progression, we know that we stop in _at most_ n steps (the +1
    cancels with the progression) to stop and the induction hypothesis applies.
    -/
    obtain ⟨⟨N, pN⟩, hN⟩ := inst.enters
    obtain ⟨⟨N', pN'⟩, hNN'⟩ := inst.closed ⟨N, pN⟩
    simp_all
    have hIN' := calc I
      _ -[M]->* N := hN
      _ -[M]->+ N' := hNN'

    obtain ⟨nfin, hnfin⟩ := hIN'.to_multistep
    have hnfinn := Machine.halts_in.within hFinal hnfin
    have hnfinHalts := Machine.halts_in.preceeds hFinal hnfin hnfinn
    simp [*] at hnfinn hnfinHalts

    -- hnfinHalts : M halts in at most n steps from N', we can apply the induction hypothesis

    refine IH _ ?_ (inst.offset pN') hnfinHalts
    · exact Nat.sub_le n nfin
  }
}

/-- Proves non-termination using closed set reasonning. -/
macro "closed_set" p:term : tactic =>
  `(tactic| suffices ClosedSet _ $p _ from this.nonHalting <;> constructor)
