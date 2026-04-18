/-
Transcript-local partial tape constraints for translated cyclers.

This file isolates the head-relative tape information needed to replay a transcript. The key
high-level facts are:
- a successful run realizes the start and finish constraints;
- satisfying the start constraint is enough to replay the transcript once more.
-/
import Busybeaver.Deciders.TranslatedCyclers.Geometry

namespace Deciders.TranslatedCyclers

open TM.Model

variable {BM : Type _} [TM.Model BM]

abbrev PartialTape (BM : Type _) [TM.Model BM] := Int → Option (TickSymbol BM)

namespace PartialTape

/-- A tape models a partial tape when it agrees on every known offset. -/
def Models (T : Turing.Tape (TickSymbol BM)) (P : PartialTape BM) : Prop :=
  ∀ i s, P i = some s → T.nth i = s

/-- Reindex a partial tape after shifting the head by `k`. -/
def shift (k : Int) (P : PartialTape BM) : PartialTape BM :=
  fun i => P (i + k)

/-- Right-biased union of partial tape information. -/
def merge (P Q : PartialTape BM) : PartialTape BM :=
  fun i => match Q i with | some s => some s | none => P i

def singleton (i : Int) (s : TickSymbol BM) : PartialTape BM :=
  fun j => if j = i then some s else none

/-- Drop any information about the current head position. -/
def eraseHead (P : PartialTape BM) : PartialTape BM :=
  fun i => if i = 0 then none else P i

/--
Pull back a next-step partial tape through one wrapped ticking step.

Cells away from the current head are reindexed across the move. Information about the current head
cell is dropped because that cell is overwritten by the step itself.
-/
def preStep (m : TickingMachine BM) (t : Tick BM) (P : PartialTape BM) : PartialTape BM :=
  eraseHead (shift (-shiftDelta (dirOfTick m t)) P)

lemma models_shift {T : Turing.Tape (TickSymbol BM)} {P : PartialTape BM}
    (h : Models T P) :
    Models T (shift 0 P) := by
  intro i s hs
  exact h i s (by simpa [shift] using hs)

lemma models_merge_left {T : Turing.Tape (TickSymbol BM)} {P Q : PartialTape BM}
    (hP : Models T P) (hQ : Models T Q) :
    Models T (merge P Q) := by
  intro i s hs
  unfold merge at hs
  cases hqi : Q i with
  | none =>
      exact hP i s (by simpa [hqi] using hs)
  | some t =>
      have hts : t = s := by
        have : some t = some s := by simpa [hqi] using hs
        injection this with hts
      subst hts
      exact hQ i t hqi

lemma models_singleton {T : Turing.Tape (TickSymbol BM)} {i : Int} {s : TickSymbol BM}
    (h : T.nth i = s) :
    Models T (singleton (BM := BM) i s) := by
  intro j s' hs
  unfold singleton at hs
  by_cases hij : j = i
  · simp [hij] at hs
    subst hij
    subst hs
    simpa using h
  · simp [hij] at hs

lemma shift_apply (k : Int) (P : PartialTape BM) (i : Int) :
    shift k P i = P (i + k) := rfl

lemma eraseHead_apply (P : PartialTape BM) (i : Int) :
    eraseHead P i = (if i = 0 then none else P i) := rfl

lemma preStep_apply (m : TickingMachine BM) (t : Tick BM) (P : PartialTape BM) (i : Int) :
    preStep m t P i =
      if i = 0 then none else P (i - shiftDelta (dirOfTick m t)) := by
  unfold preStep eraseHead shift
  by_cases hi : i = 0
  · simp [hi]
  · simp [hi, sub_eq_add_neg]

end PartialTape

notation T " ⊨ " P => PartialTape.Models T P

private lemma tstep_tick_eq {m : TickingMachine BM} {A B : TickingConfig BM} {t : Tick BM}
    (h : A t-[m:t]->' B) :
    t = (A.state, A.tape.head) := by
  unfold TReach.TStep stepTick at h
  cases hs : TM.Model.step m A with
  | mk dn outcome =>
      cases outcome <;> simp [hs] at h
      simpa using h.2.symm

private lemma tstep_tape_eq {m : TickingMachine BM} {A B : TickingConfig BM} {t : Tick BM}
    (h : A t-[m:t]->' B) :
    B.tape = (A.tape.write (writeOfTick m t)).move (dirOfTick m t) := by
  have ht : t = (A.state, A.tape.head) := tstep_tick_eq h
  subst ht
  have hstep : A -[m]->' B := TReach.single_step h
  unfold TM.Model.Step at hstep
  rw [TM.Model.step_stmt m A] at hstep
  cases hstmt : TM.Model.stmt m A with
  | mk dn stmt =>
      cases stmt with
      | halt =>
          simp [hstmt] at hstep
      | next sym dir state =>
          simp [hstmt] at hstep
          cases hstep
          have hconfig :
              TM.Model.stmt m (configOfTick ((A.state, A.tape.head) : Tick BM)) = TM.Model.stmt m A := by
            apply TM.Model.stmt_eq_of_state_head_eq m
            · simp [configOfTick]
            · rfl
          simp [writeOfTick, dirOfTick, stmtOfTick, hconfig, hstmt]

private lemma tstep_nth_preStep {m : TickingMachine BM} {A B : TickingConfig BM} {t : Tick BM}
    (h : A t-[m:t]->' B) {i : Int} (hi : i ≠ 0) :
    B.tape.nth (i - shiftDelta (dirOfTick m t)) = A.tape.nth i := by
  rw [tstep_tape_eq h]
  cases hdir : dirOfTick m t with
  | left =>
      rw [Turing.Tape.move_left_nth]
      simpa [shiftDelta, hdir] using (Turing.Tape.write_nth_of_ne_zero _ _ hi)
  | right =>
      rw [Turing.Tape.move_right_nth]
      simpa [shiftDelta, hdir] using (Turing.Tape.write_nth_of_ne_zero _ _ hi)

private lemma tstep_written_cell {m : TickingMachine BM} {A B : TickingConfig BM} {t : Tick BM}
    (h : A t-[m:t]->' B) :
    B.tape.nth (-shiftDelta (dirOfTick m t)) = writeOfTick m t := by
  rw [tstep_tape_eq h]
  cases hdir : dirOfTick m t with
  | left =>
      rw [Turing.Tape.move_left_nth]
      simpa [shiftDelta, hdir] using (Turing.Tape.write_nth_zero A.tape (writeOfTick m t))
  | right =>
      rw [Turing.Tape.move_right_nth]
      simpa [shiftDelta, hdir] using (Turing.Tape.write_nth_zero A.tape (writeOfTick m t))

private lemma tstep_nth_shift {m : TickingMachine BM} {A B : TickingConfig BM} {t : Tick BM}
    (h : A t-[m:t]->' B) {i : Int}
    (hi : i ≠ -shiftDelta (dirOfTick m t)) :
    B.tape.nth i = A.tape.nth (i + shiftDelta (dirOfTick m t)) := by
  have hi' : i + shiftDelta (dirOfTick m t) ≠ 0 := by
    intro h0
    apply hi
    omega
  simpa [sub_eq_add_neg, add_comm, add_left_comm, add_assoc] using
    (tstep_nth_preStep h (i := i + shiftDelta (dirOfTick m t)) hi')

private lemma replay_first_step
    {m : TickingMachine BM} {A A₀ B₀ : TickingConfig BM} {t : Tick BM}
    (hRef : A₀ t-[m:t]->' B₀)
    (hState : A.state = A₀.state) (hHead : A.tape.head = A₀.tape.head) :
    ∃ B : TickingConfig BM, (A t-[m:t]->' B) ∧ B.state = B₀.state := by
  have ht : t = (A₀.state, A₀.tape.head) := tstep_tick_eq hRef
  have hstmtEq : TM.Model.stmt m A = TM.Model.stmt m A₀ := by
    apply TM.Model.stmt_eq_of_state_head_eq m
    · exact hState
    · exact hHead
  have hstep : A₀ -[m]->' B₀ := TReach.single_step hRef
  unfold TM.Model.Step at hstep
  rw [TM.Model.step_stmt m A₀] at hstep
  cases hstmt0 : TM.Model.stmt m A₀ with
  | mk dn stmt =>
      cases stmt with
      | halt =>
          simp [hstmt0] at hstep
      | next sym dir state =>
          simp [hstmt0] at hstep
          cases hstep
          let B : TickingConfig BM := {
            state := state
            tape := (A.tape.write sym).move dir
          }
          refine ⟨B, ?_, rfl⟩
          subst ht
          unfold TReach.TStep stepTick
          rw [TM.Model.step_stmt m A]
          rw [hstmtEq, hstmt0]
          simp [B, hState, hHead]

/--
The partial tape required at the start of a transcript.

Sketch:
- record the read symbol at the current head position;
- shift the tail constraint by the move determined by the current tick;
- keep only the start-time information needed to realize the transcript.
-/
def startConstraint (m : TickingMachine BM) (L : List (Tick BM)) : PartialTape BM := by
  induction L with
  | nil =>
      exact fun _ => none
  | cons t L IH =>
      exact PartialTape.merge
        (PartialTape.singleton 0 t.2)
        (PartialTape.preStep m t IH)

/--
The partial tape known at the end of a transcript, in final-head coordinates.

Sketch:
- replay the writes determined by the transcript;
- shift coordinates after each move;
- keep only the offsets whose values are forced by the run.
-/
-- TODO: This lemmas don't need TickingMachine, they can be defined on top of any Model
def finishConstraint (m : TickingMachine BM) (L : List (Tick BM)) : PartialTape BM := by
  induction L with
  | nil =>
      exact fun _ => none
  | cons t L IH =>
      exact PartialTape.merge
        (PartialTape.singleton (-netShift m (t :: L)) (writeOfTick m t))
        IH

private lemma run_finish_models_and_none
    {m : TickingMachine BM} {A B : TickingConfig BM} {L : List (Tick BM)}
    (h : A t-[m:L]->>' B) :
    (B.tape ⊨ finishConstraint m L) ∧
      (∀ i, finishConstraint m L i = none → B.tape.nth i = A.tape.nth (i + netShift m L)) := by
  induction h with
  | refl C =>
      constructor
      · intro i s hs
        simp [finishConstraint] at hs
      · intro i hi
        simp [finishConstraint] at hi
        simp [netShift]
  | step A B C t L hAB hBC IH =>
      rcases IH with ⟨hModelsTail, hNoneTail⟩
      constructor
      · intro i s hs
        unfold finishConstraint at hs
        change (match finishConstraint m L i with
          | some s => some s
          | none => PartialTape.singleton (BM := BM) (-netShift m (t :: L)) (writeOfTick m t) i) = some s at hs
        cases htail : finishConstraint m L i with
        | some s' =>
            have hs' : s' = s := by
              simp [htail] at hs
              exact hs
            subst s'
            exact hModelsTail _ _ htail
        | none =>
            have hsing : PartialTape.singleton (BM := BM) (-netShift m (t :: L)) (writeOfTick m t) i = some s := by
              simpa [htail] using hs
            have hi : i = -netShift m (t :: L) ∧ writeOfTick m t = s := by
              simpa [PartialTape.singleton] using hsing
            rcases hi with ⟨rfl, rfl⟩
            have hpres := hNoneTail (-netShift m (t :: L)) htail
            have hshift : -netShift m (t :: L) + netShift m L = -shiftDelta (dirOfTick m t) := by
              simp [netShift]
            rw [hshift, tstep_written_cell hAB] at hpres
            exact hpres
      · intro i hi
        unfold finishConstraint at hi
        change (match finishConstraint m L i with
          | some s => some s
          | none => PartialTape.singleton (BM := BM) (-netShift m (t :: L)) (writeOfTick m t) i) = none at hi
        have htail : finishConstraint m L i = none := by
          cases hfin : finishConstraint m L i with
          | none =>
              rfl
          | some s =>
              simp [hfin] at hi
        have hne : i ≠ -netShift m (t :: L) := by
          intro hEq
          have : PartialTape.singleton (BM := BM) (-netShift m (t :: L)) (writeOfTick m t) i = none := by
              simpa [htail] using hi
          simp [PartialTape.singleton, hEq] at this
        have hpresTail := hNoneTail i htail
        have hstep :
            B.tape.nth (i + netShift m L) = A.tape.nth (i + netShift m L + shiftDelta (dirOfTick m t)) := by
          apply tstep_nth_shift hAB
          intro hEq
          apply hne
          simp [netShift]
          omega
        rw [hpresTail, hstep]
        simp [netShift, add_assoc, add_comm]

/--
Any successful transcript run realizes the corresponding start constraint.

Depends on:
- the recursive definition of `startConstraint`.

Idea:
- induct on the transcript and expose the first tick via `TReach.MultiTStep.step`.
-/
lemma run_implies_models_start {m : TickingMachine BM} {A B : TickingConfig BM} {L : List (Tick BM)}
    (h : A t-[m:L]->>' B) :
    A.tape ⊨ startConstraint m L := by
  induction h with
  | refl C =>
      intro i s hs
      simp [startConstraint] at hs
  | step A B C t L hAB hBC IH =>
      have ht : t = (A.state, A.tape.head) := tstep_tick_eq hAB
      subst ht
      change A.tape ⊨
        PartialTape.merge
          (PartialTape.singleton 0 A.tape.head)
          (PartialTape.preStep m (A.state, A.tape.head) (startConstraint m L))
      intro i s hs
      unfold PartialTape.merge at hs
      cases hpre : PartialTape.preStep m (A.state, A.tape.head) (startConstraint m L) i with
      | none =>
          by_cases hi : i = 0
          · have hs0 : A.tape.head = s := by
              subst i
              have hpre0 :
                  PartialTape.preStep m (A.state, A.tape.head) (startConstraint m L) 0 = none := by
                simp [PartialTape.preStep_apply]
              rw [hpre0] at hs
              simp [PartialTape.singleton] at hs
              exact hs
            subst i
            simpa using hs0
          · have : False := by
              simp [hpre, hi, PartialTape.singleton] at hs
            contradiction
      | some s' =>
          have hs' : s' = s := by
            simp [hpre] at hs
            exact hs
          subst s'
          have hi : i ≠ 0 := by
            intro hi0
            rw [PartialTape.preStep_apply, hi0] at hpre
            cases hpre
          rw [PartialTape.preStep_apply, if_neg hi] at hpre
          have htail : B.tape.nth (i - shiftDelta (dirOfTick m (A.state, A.tape.head))) = s := by
            change B.tape.nth (i - shiftDelta (dirOfTick m (A.state, A.tape.head))) = s
            have hpre' :
                startConstraint m L (i - shiftDelta (dirOfTick m (A.state, A.tape.head))) = some s := by
              simpa using hpre
            exact IH _ _ hpre'
          rw [tstep_nth_preStep hAB hi] at htail
          exact htail

/--
Any successful transcript run realizes the corresponding finish constraint.

Depends on:
- the recursive definition of `finishConstraint`.

Idea:
- induct on the transcript, updating the partial information after the first wrapped step.
-/
lemma run_implies_models_finish {m : TickingMachine BM} {A B : TickingConfig BM} {L : List (Tick BM)}
    (h : A t-[m:L]->>' B) :
    B.tape ⊨ finishConstraint m L := by
  exact (run_finish_models_and_none h).1

lemma run_implies_finish_none
    {m : TickingMachine BM} {A B : TickingConfig BM} {L : List (Tick BM)} {i : Int}
    (h : A t-[m:L]->>' B) (hi : finishConstraint m L i = none) :
    B.tape.nth i = A.tape.nth (i + netShift m L) := by
  exact (run_finish_models_and_none h).2 i hi

/--
Satisfying the start constraint is enough to replay a transcript, relative to a reference run.

Depends on:
- `startConstraint`.

Idea:
- a bare tape constraint is not enough: we also need a reference execution to know that every tick
  in `L` is a continuing step, and a starting-state equality to align the first state;
- induct on the reference run, replaying the same wrapped step whenever the current configuration
  has the same state/head pair.
-/
lemma models_start_implies_exists_run
    {m : TickingMachine BM} {A A₀ B₀ : TickingConfig BM} {L : List (Tick BM)}
    (hRef : A₀ t-[m:L]->>' B₀) (hState : A.state = A₀.state)
    (h : A.tape ⊨ startConstraint m L) :
    ∃ B, A t-[m:L]->>' B := by
  induction hRef generalizing A with
  | refl C =>
      exact ⟨A, by simpa using TReach.MultiTStep.refl A⟩
  | step A₀ B₁ C t L hRefStep hRefTail IH =>
      have ht : t = (A₀.state, A₀.tape.head) := tstep_tick_eq hRefStep
      have hHead : A.tape.head = A₀.tape.head := by
        have h0 : startConstraint m (t :: L) 0 = some t.2 := by
          simp [startConstraint, PartialTape.merge, PartialTape.singleton, PartialTape.preStep_apply]
        have hHead' : A.tape.nth 0 = t.2 := h 0 _ h0
        subst ht
        simpa using hHead'
      obtain ⟨B, hAB, hBState⟩ := replay_first_step hRefStep hState hHead
      have hBModels : B.tape ⊨ startConstraint m L := by
        intro i s hs
        by_cases hi : i = -shiftDelta (dirOfTick m t)
        · have hrefStart : B₁.tape.nth i = s := run_implies_models_start hRefTail _ _ hs
          have hrefWritten : B₁.tape.nth i = writeOfTick m t := by
            subst hi
            exact tstep_written_cell hRefStep
          have hswrite : s = writeOfTick m t := by
            rw [hrefWritten] at hrefStart
            exact hrefStart.symm
          subst hi
          rw [hswrite]
          exact tstep_written_cell hAB
        · have hk : i + shiftDelta (dirOfTick m t) ≠ 0 := by
            intro hk0
            apply hi
            omega
          have hpre :
              PartialTape.preStep m t (startConstraint m L)
                (i + shiftDelta (dirOfTick m t)) = some s := by
            rw [PartialTape.preStep_apply]
            simp [hk, hs]
          have hfull :
              startConstraint m (t :: L) (i + shiftDelta (dirOfTick m t)) = some s := by
            unfold startConstraint
            change (match PartialTape.preStep m t (startConstraint m L) (i + shiftDelta (dirOfTick m t)) with
              | some s => some s
              | none => PartialTape.singleton 0 t.2 (i + shiftDelta (dirOfTick m t))) = some s
            simp [hpre]
          have hAcell : A.tape.nth (i + shiftDelta (dirOfTick m t)) = s := h _ _ hfull
          rw [tstep_nth_shift hAB hi]
          exact hAcell
      obtain ⟨D, hBD⟩ := IH hBState hBModels
      exact ⟨D, TReach.MultiTStep.step (A := A) (B := B) (C := D) (t := t) (L := L) hAB hBD⟩

/--
Start and finish constraints agree on any offset where both are defined after the net shift.

Depends on:
- `run_implies_models_start`
- `run_implies_models_finish`

Idea:
- compare both constraints on the same actual tape arising as the middle configuration of two
  consecutive transcript runs.
-/
lemma start_finish_agree_on_overlap
    {m : TickingMachine BM} {A B C : TickingConfig BM} {L : List (Tick BM)}
    (hAB : A t-[m:L]->>' B) (hBC : B t-[m:L]->>' C) :
    ∀ i s,
      startConstraint m L i = some s →
      PartialTape.shift (-netShift m L) (finishConstraint m L) i = some s := by
  sorry

end Deciders.TranslatedCyclers
