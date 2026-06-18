/-
Basic transcript machinery for translated cyclers.

This file is the shared foundation for the proof-oriented files in this folder:
- cached search state and validity,
- loop-detection helpers used by the executable decider.

The looping proof itself lives in `Looping.lean`.
-/
import Busybeaver.Deciders.TranslatedCyclers.Reachability

namespace Deciders.TranslatedCyclers

open TM.Model

variable {BM : Type _} [TM.Model BM]

structure TickCache (m : TickingMachine BM) where
  cfg : TickingConfig BM
  history : List (Tick BM)
  baseSteps : Nat

namespace TickCache

structure Valid (m : TickingMachine BM) (σ : TickCache m) where
  transcript : (default : TickingConfig BM) t-[m:σ.history.reverse]->>' σ.cfg
  multistepBase : (default : TickingConfig BM) -[m]{σ.baseSteps}->>' σ.cfg

def initial (m : TickingMachine BM) : TickCache m := {
  cfg := default
  history := []
  baseSteps := 0
}

lemma initial_valid (m : TickingMachine BM) : Valid m (initial m) := {
  transcript := by simpa [initial] using TReach.MultiTStep.refl (default : TickingConfig BM)
  multistepBase := .refl
}

end TickCache

lemma stepTick_halts
    {m : TickingMachine BM} {σ : TickCache m} (hvalid : TickCache.Valid m σ)
    (hstep : stepTick m σ.cfg = ⟨dn, .halted out⟩) :
    TM.Model.LastState m σ.cfg ∧
      ((default : TickingConfig BM) -[m]{σ.baseSteps}->>' σ.cfg) := by
  constructor
  · unfold TM.Model.LastState
    unfold stepTick at hstep
    cases hs : TM.Model.step m σ.cfg with
    | mk dn outcome =>
        cases outcome <;> simp [hs] at hstep ⊢
  · exact hvalid.multistepBase

lemma stepTick_continue_valid
    {m : TickingMachine BM} {σ : TickCache m} (hvalid : TickCache.Valid m σ)
    (hstep : stepTick m σ.cfg = ⟨dn, .continue (cfg, t)⟩) :
    TickCache.Valid m {
      cfg := cfg
      history := t :: σ.history
      baseSteps := σ.baseSteps + dn
    } := by
  have hsingle : σ.cfg t-[m:[t]]->>' cfg := by
    exact TReach.MultiTStep.step
      (A := σ.cfg) (B := cfg) (C := cfg) (t := t) (L := [])
      (by simpa [TReach.TStep] using congrArg TM.StepResult.outcome hstep)
      (TReach.MultiTStep.refl cfg)
  have hbase : TM.Model.StepBase m dn σ.cfg cfg := by
    unfold TM.Model.StepBase
    unfold stepTick at hstep
    cases hs : TM.Model.step m σ.cfg with
    | mk dn' outcome =>
        cases outcome <;> simp [hs] at hstep ⊢
        exact ⟨hstep.1, hstep.2.1⟩
  refine {
    transcript := ?_
    multistepBase := ?_
  }
  · simpa using TReach.trans hvalid.transcript hsingle
  · simpa using
      TM.Model.MultistepBase.trans hvalid.multistepBase (TM.Model.MultistepBase.single hbase)

lemma List.takeWhile_append_drop {p : α → Bool} (L : List α) :
    (L.takeWhile p) ++ (L.drop (L.takeWhile p).length) = L := by
  induction L with
  | nil =>
      simp
  | cons head tail IH =>
      by_cases h : p head = true
      · rw [List.takeWhile_cons_of_pos h]
        simp [IH]
      · rw [List.takeWhile_cons_of_neg h]
        simp

def detectFrontLoop (q : TM.Model.State BM) (L : List (Tick BM)) :
    Option {L' : List (Tick BM) //
      L' ++ L' <+: ((q, (⊥ : TickSymbol BM)) :: L) ∧ (q, (⊥ : TickSymbol BM)) ∈ L'} :=
  let rec loopy (left : List (Tick BM)) (right : List (Tick BM))
      (hq : (q, (⊥ : TickSymbol BM)) ∈ left)
      (hL : (q, (⊥ : TickSymbol BM)) :: L = left ++ right) :
      Option {P : List (Tick BM) × List (Tick BM) //
        (q, (⊥ : TickSymbol BM)) :: L = P.1 ++ P.2 ∧
          P.1 <+: P.2 ∧ (q, (⊥ : TickSymbol BM)) ∈ P.1} :=
    if hlr : left.length > right.length then
      .none
    else if hl : left <+: right then
      .some ⟨(left, right), ⟨hL, hl, hq⟩⟩
    else match right with
    | [] =>
        by
          simp at hlr
          absurd hlr
          exact List.ne_nil_of_mem hq
    | head :: tail =>
        let upto := tail.takeWhile (fun t => t.2 ≠ (⊥ : TickSymbol BM))
        loopy (left ++ head :: upto) (tail.drop upto.length)
          (by
            simp
            left
            exact hq)
          (by
            rw [hL]
            simp [upto]
            symm
            exact List.takeWhile_append_drop tail)
  termination_by right.length
  (loopy [(q, (⊥ : TickSymbol BM))] L (by simp) (by simp)).map fun x =>
    match x with
    | ⟨(left, right), ⟨hsum, hpref, hq⟩⟩ =>
        ⟨left, by
          constructor
          · rcases hpref with ⟨r, hr⟩
            refine ⟨r, ?_⟩
            calc
              left ++ left ++ r = left ++ (left ++ r) := by simp [List.append_assoc]
              _ = left ++ right := by rw [hr]
              _ = (q, ⊥) :: L := hsum.symm
          · exact hq⟩

def List.repeat (L : List α) : Nat → List α
  | 0 => []
  | n + 1 => L ++ List.repeat L n

@[simp] lemma List.repeat_zero : List.repeat L 0 = [] := rfl

@[simp] lemma List.repeat_succ : List.repeat L (n + 1) = L ++ List.repeat L n := rfl

lemma List.repeat_concat_comm : List.repeat L n ++ L = L ++ List.repeat L n := by
  induction n with
  | zero =>
      simp
  | succ n IH =>
      simp [IH, List.append_assoc]

@[simp] lemma List.repeat_length : (List.repeat L n).length = n * L.length := by
  induction n with
  | zero =>
      simp
  | succ n IH =>
      simp [IH, Nat.succ_mul, Nat.add_comm]

@[simp] lemma List.repeat_add : List.repeat L (n + k) = List.repeat L n ++ List.repeat L k := by
  induction k with
  | zero =>
      simp
  | succ k IH =>
      have hk : n + (k + 1) = (n + k) + 1 := by omega
      rw [hk, List.repeat_succ, IH, List.repeat_succ]
      rw [← List.append_assoc, ← List.repeat_concat_comm, List.append_assoc]

end Deciders.TranslatedCyclers
