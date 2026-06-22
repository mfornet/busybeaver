import Busybeaver.TM.Model.Reachability
import Busybeaver.TM.Table.Reachability

/-!
# Tabular machines as `TM.Model` instances

A tabular `Machine` is a `TM.Model` (the instance lives in `Busybeaver/TM/Table.lean`).
This module explains how that instance behaves: it bridges the model-level and
tabular reachability/halting APIs, showing that the model single-step, multistep,
last-state and halting predicates agree with their tabular counterparts.

The exported result is `modelHaltMToTableHaltM`, which transports a `TM.Model.HaltM`
certificate (produced by deciders written against the generic `TM.Model` interface)
to a tabular `HaltM` certificate.  The remaining lemmas are private bridging steps.
-/

open TM TM.Table

namespace TM.Table.Model

private lemma modelStepBase_to_tableStep
    {l s : ℕ} {M : Machine l s}
    {n : ℕ} {A B : TM.Model.Config (Machine l s)}
    (h : TM.Model.StepBase M n A B) :
    n = 1 ∧ (⟨A.state, A.tape⟩ : Config l s) -[M]-> (⟨B.state, B.tape⟩ : Config l s) := by
  unfold TM.Model.StepBase at h
  cases hget : M.get A.state A.tape.head with
  | halt =>
      simp [TM.Model.step, hget] at h
  | next sym dir state =>
      simp [TM.Model.step, hget] at h
      rcases h with ⟨rfl, rfl⟩
      constructor
      · rfl
      · simp [Machine.step, hget]

private lemma modelLastState_to_tableLastState
    {l s : ℕ} {M : Machine l s}
    {C : TM.Model.Config (Machine l s)}
    (h : TM.Model.LastState M C) :
    M.LastState (⟨C.state, C.tape⟩ : Config l s) := by
  cases hget : M.get C.state C.tape.head with
  | halt =>
      simp [Machine.LastState, Machine.step, hget]
  | next sym dir state =>
      simp [TM.Model.LastState, TM.Model.step, hget] at h

private lemma tableLastState_to_modelLastState
    {l s : ℕ} {M : Machine l s}
    {C : Config l s}
    (h : M.LastState C) :
    TM.Model.LastState M ({ state := C.state, tape := C.tape } : TM.Model.Config (Machine l s)) := by
  cases hget : M.get C.state C.tape.head with
  | halt =>
      simp [Machine.LastState, Machine.step, hget] at h
      simp [TM.Model.LastState, TM.Model.step, hget]
  | next sym dir state =>
      simp [Machine.LastState, Machine.step, hget] at h

private lemma tableStep_to_modelStep
    {l s : ℕ} {M : Machine l s}
    {A B : Config l s}
    (h : A -[M]-> B) :
    ({ state := A.state, tape := A.tape } : TM.Model.Config (Machine l s))
      -[M]->'
    ({ state := B.state, tape := B.tape } : TM.Model.Config (Machine l s)) := by
  cases hget : M.get A.state A.tape.head with
  | halt =>
      simp [Machine.step, hget] at h
  | next sym dir state =>
      simp [Machine.step, hget] at h
      rcases h with rfl
      simp [TM.Model.Step, TM.Model.step, hget]

private lemma tableMultistep_to_modelMultistep
    {l s : ℕ} {M : Machine l s}
    {n : ℕ} {A B : Config l s}
    (h : A -[M]{n}-> B) :
    ({ state := A.state, tape := A.tape } : TM.Model.Config (Machine l s))
      -[M]{n}->'
    ({ state := B.state, tape := B.tape } : TM.Model.Config (Machine l s)) := by
  induction h with
  | refl =>
      exact .refl
  | succ hAB hBC IH =>
      exact .step (tableStep_to_modelStep hAB) IH

private lemma tableHalts_to_modelHalts
    {l s : ℕ} {M : Machine l s}
    (h : M.halts (init : Config l s)) :
    TM.Model.halts M (default : TM.Model.Config (Machine l s)) := by
  rcases h with ⟨n, C, hLast, hReach⟩
  exact ⟨n, ({ state := C.state, tape := C.tape } : TM.Model.Config (Machine l s)),
    tableLastState_to_modelLastState hLast, by
    exact tableMultistep_to_modelMultistep hReach⟩

private lemma modelMultistepBase_to_tableMultistep
    {l s : ℕ} {M : Machine l s}
    {n : ℕ} {A B : TM.Model.Config (Machine l s)}
    (h : A -[M]{n}->>' B) :
    (⟨A.state, A.tape⟩ : Config l s) -[M]{n}-> (⟨B.state, B.tape⟩ : Config l s) := by
  induction h with
  | refl =>
      exact .refl
  | step hAB hBC IH =>
      obtain ⟨hn, hAB'⟩ := modelStepBase_to_tableStep hAB
      cases hn
      simpa [Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using Machine.Multistep.succ hAB' IH

/-- Transport a model-level halting certificate to a tabular one. -/
def modelHaltMToTableHaltM
    {l s : ℕ} {M : Machine l s} :
    TM.Model.HaltM M Unit → HaltM M Unit
  | .unknown _ => .unknown ()
  | .halts_prf n C h =>
      .halts_prf n ⟨C.state, C.tape⟩ <| by
        rcases h with ⟨hLast, hReach⟩
        constructor
        · exact modelLastState_to_tableLastState hLast
        · exact modelMultistepBase_to_tableMultistep hReach
  | .loops_prf h =>
      .loops_prf (by
        intro hhalts
        exact h (tableHalts_to_modelHalts hhalts))

end TM.Table.Model
