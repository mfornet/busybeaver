/-
Transcript-local partial tape constraints for translated cyclers.

This file isolates the head-relative tape information needed to replay a transcript. The key
high-level facts are:
- a successful run realizes the start and finish constraints;
- satisfying the start constraint is enough to replay the transcript once more.
-/
import Busybeaver.Deciders.TranslatedCyclers.PartialTape

namespace Deciders.TranslatedCyclers

open TM.Model

variable {BM : Type _} [TM.Model BM]

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

lemma tstep_written_cell {m : TickingMachine BM} {A B : TickingConfig BM} {t : Tick BM}
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
Start and finish constraints agree on any offset where both are defined.

Depends on:
- `run_implies_models_start`
- `run_implies_models_finish`

Idea:
- compare both constraints on the same actual tape `B`, which is simultaneously the *finish* of the
  first run `A t-[m:L]->>' B` and the *start* of the second run `B t-[m:L]->>' C`.

Note on coordinates: both `startConstraint` and `finishConstraint` of a run are expressed relative
to the run's own start/finish head respectively. For the shared config `B`, the second run starts at
`B` and the first run finishes at `B`, so both constraints live in *the same* `B`-relative
coordinate system. Hence they are compared at the *same* offset `i` (there is no net-shift between
them — the net shift only relates a single run's own start- and finish-coordinates).
-/
lemma start_finish_agree_on_overlap
    {m : TickingMachine BM} {A B C : TickingConfig BM} {L : List (Tick BM)}
    (hAB : A t-[m:L]->>' B) (hBC : B t-[m:L]->>' C) :
    ∀ i s w,
      startConstraint m L i = some s →
      finishConstraint m L i = some w →
      s = w := by
  intro i s w hstart hfinish
  -- `B` realizes the start constraint (it starts the second run)…
  have hs : B.tape.nth i = s := run_implies_models_start hBC i s hstart
  -- …and the finish constraint (it finishes the first run).
  have hw : B.tape.nth i = w := run_implies_models_finish hAB i w hfinish
  exact hs.symm.trans hw

/-! ### Domain structure of the start/finish constraints

The remaining frontier argument only needs to know *where* the constraints are defined (their
"domains" are the visited offsets) and how the two domains are related by the net shift. We expose
these facts purely in terms of `startConstraint`/`finishConstraint`, so the geometric head walk never
has to be reasoned about explicitly. -/

/-- Unfolding of the start constraint on a cons. -/
lemma startConstraint_cons (m : TickingMachine BM) (t : Tick BM) (L : List (Tick BM)) (i : Int) :
    startConstraint m (t :: L) i =
      PartialTape.merge (PartialTape.singleton 0 t.2)
        (PartialTape.preStep m t (startConstraint m L)) i := rfl

/-- The start constraint is always defined at the current head (offset `0`). -/
lemma startConstraint_zero (m : TickingMachine BM) (t : Tick BM) (L : List (Tick BM)) :
    startConstraint m (t :: L) 0 = some t.2 := by
  rw [startConstraint_cons]
  simp [PartialTape.merge, PartialTape.preStep_apply, PartialTape.singleton]

/-- The start constraint of a cons is `none` at `i` iff `i ≠ 0` and the tail is `none` one step
back. -/
lemma startConstraint_cons_eq_none_iff
    (m : TickingMachine BM) (t : Tick BM) (L : List (Tick BM)) (i : Int) :
    startConstraint m (t :: L) i = none ↔
      i ≠ 0 ∧ startConstraint m L (i - shiftDelta (dirOfTick m t)) = none := by
  rw [startConstraint_cons, PartialTape.merge_eq_none, PartialTape.preStep_apply,
    PartialTape.singleton_eq_none]
  by_cases hi : i = 0
  · simp [hi]
  · simp [hi]

/-- Value of the start constraint away from the head: it is the tail's value one step back. -/
lemma startConstraint_cons_apply_of_ne
    (m : TickingMachine BM) (t : Tick BM) (L : List (Tick BM)) {i : Int} (hi : i ≠ 0) :
    startConstraint m (t :: L) i = startConstraint m L (i - shiftDelta (dirOfTick m t)) := by
  rw [startConstraint_cons]
  unfold PartialTape.merge
  rw [PartialTape.preStep_apply, if_neg hi]
  cases hX : startConstraint m L (i - shiftDelta (dirOfTick m t)) with
  | some s => rfl
  | none => simp [PartialTape.singleton, hi]

/-- Unfolding of the finish constraint on a cons. -/
lemma finishConstraint_cons (m : TickingMachine BM) (t : Tick BM) (L : List (Tick BM)) (i : Int) :
    finishConstraint m (t :: L) i =
      PartialTape.merge (PartialTape.singleton (-netShift m (t :: L)) (writeOfTick m t))
        (finishConstraint m L) i := rfl

/-- The finish constraint is `none` exactly where the *shifted* start constraint is `none`: the two
constraints have the same set of touched cells, related by the net head displacement. -/
lemma finish_none_iff_start_none_shift
    (m : TickingMachine BM) (L : List (Tick BM)) (k : Int) :
    finishConstraint m L k = none ↔ startConstraint m L (k + netShift m L) = none := by
  induction L generalizing k with
  | nil => simp [finishConstraint, startConstraint]
  | cons t L IH =>
      have hδ : k + netShift m (t :: L) - shiftDelta (dirOfTick m t) = k + netShift m L := by
        simp only [netShift]; omega
      rw [finishConstraint_cons, PartialTape.merge_eq_none, PartialTape.singleton_eq_none,
        startConstraint_cons_eq_none_iff, hδ, IH k]
      constructor
      · rintro ⟨h1, h2⟩; exact ⟨by omega, h1⟩
      · rintro ⟨h1, h2⟩; exact ⟨h2, by omega⟩

/-- `ne_none` form of `startConstraint_cons_eq_none_iff`. -/
lemma startConstraint_cons_ne_none_iff
    (m : TickingMachine BM) (t : Tick BM) (L : List (Tick BM)) (i : Int) :
    startConstraint m (t :: L) i ≠ none ↔
      i = 0 ∨ startConstraint m L (i - shiftDelta (dirOfTick m t)) ≠ none := by
  rw [ne_eq, startConstraint_cons_eq_none_iff]
  tauto

/-- Whenever the start constraint is defined anywhere, it is defined at the head (offset `0`): a
nonempty visited set always contains `0`. -/
lemma startConstraint_zero_ne_none_of_ne_none
    (m : TickingMachine BM) (L : List (Tick BM)) (x : Int)
    (h : startConstraint m L x ≠ none) :
    startConstraint m L 0 ≠ none := by
  cases L with
  | nil => simp [startConstraint] at h
  | cons t L => rw [startConstraint_zero]; simp

/-- `shiftDelta` of any tick direction is `±1`. -/
lemma shiftDelta_dirOfTick_eq (m : TickingMachine BM) (t : Tick BM) :
    shiftDelta (dirOfTick m t) = 1 ∨ shiftDelta (dirOfTick m t) = -1 := by
  cases h : dirOfTick m t <;> simp [shiftDelta, h]

/-- The set of offsets where the start constraint is defined is convex (an interval): this is the
geometric content that the head walk visits a contiguous range. -/
lemma startConstraint_convex (m : TickingMachine BM) (L : List (Tick BM)) {a b c : Int}
    (ha : startConstraint m L a ≠ none) (hb : startConstraint m L b ≠ none)
    (hac : a ≤ c) (hcb : c ≤ b) : startConstraint m L c ≠ none := by
  induction L generalizing a b c with
  | nil => simp [startConstraint] at ha
  | cons t L IH =>
      have hδ : shiftDelta (dirOfTick m t) = 1 ∨ shiftDelta (dirOfTick m t) = -1 :=
        shiftDelta_dirOfTick_eq m t
      rw [startConstraint_cons_ne_none_iff] at ha hb ⊢
      by_cases hc0 : c = 0
      · exact Or.inl hc0
      · refine Or.inr ?_
        rcases ha with rfl | haS
        · rcases hb with rfl | hbS
          · exfalso; omega
          · have h0L : startConstraint m L 0 ≠ none :=
              startConstraint_zero_ne_none_of_ne_none m L _ hbS
            exact IH h0L hbS (by rcases hδ with h | h <;> omega) (by omega)
        · rcases hb with rfl | hbS
          · have h0L : startConstraint m L 0 ≠ none :=
              startConstraint_zero_ne_none_of_ne_none m L _ haS
            exact IH haS h0L (by omega) (by rcases hδ with h | h <;> omega)
          · exact IH haS hbS (by omega) (by omega)

/-- One-sided "no gap" consequence of convexity: to the right of a gap, the start constraint stays
undefined. -/
lemma startConstraint_none_right (m : TickingMachine BM) (L : List (Tick BM)) {x y z : Int}
    (hx : startConstraint m L x ≠ none) (hy : startConstraint m L y = none)
    (hxy : x ≤ y) (hyz : y ≤ z) : startConstraint m L z = none := by
  by_contra hz
  exact (startConstraint_convex m L hx hz hxy hyz) hy

/-- One-sided "no gap" consequence of convexity: to the left of a gap, the start constraint stays
undefined. -/
lemma startConstraint_none_left (m : TickingMachine BM) (L : List (Tick BM)) {x y z : Int}
    (hx : startConstraint m L x ≠ none) (hy : startConstraint m L y = none)
    (hyx : y ≤ x) (hzy : z ≤ y) : startConstraint m L z = none := by
  by_contra hz
  exact (startConstraint_convex m L hz hx hzy hyx) hy

/-- The finish constraint of a nonempty transcript is defined at `1` or at `-1`: the *last* tick's
write lands one step from the final head, witnessing that the head walk reaches the net shift. -/
lemma finish_boundary (m : TickingMachine BM) :
    ∀ (L : List (Tick BM)), L ≠ [] →
      finishConstraint m L 1 ≠ none ∨ finishConstraint m L (-1) ≠ none := by
  intro L
  induction L with
  | nil => intro h; exact absurd rfl h
  | cons t L IH =>
      intro _
      cases L with
      | nil =>
          have hnz : finishConstraint m [t] (-netShift m [t]) ≠ none := by
            rw [finishConstraint_cons, ne_eq, PartialTape.merge_eq_none, not_and]
            intro _
            simp [PartialTape.singleton]
          have hns : netShift m [t] = shiftDelta (dirOfTick m t) := by simp [netShift]
          rcases shiftDelta_dirOfTick_eq m t with h | h
          · right
            have hv : -netShift m [t] = -1 := by rw [hns]; omega
            rwa [hv] at hnz
          · left
            have hv : -netShift m [t] = 1 := by rw [hns]; omega
            rwa [hv] at hnz
      | cons u L' =>
          rcases IH (by simp) with h | h
          · left
            rw [finishConstraint_cons, ne_eq, PartialTape.merge_eq_none]
            push_neg
            intro hc
            exact absurd hc h
          · right
            rw [finishConstraint_cons, ne_eq, PartialTape.merge_eq_none]
            push_neg
            intro hc
            exact absurd hc h

/-- Start-side boundary: a nonempty transcript reads some cell within one step of the net shift. In
particular the visited window reaches out to `netShift ± 1`. -/
lemma start_boundary (m : TickingMachine BM) (L : List (Tick BM)) (hL : L ≠ []) :
    ∃ v, startConstraint m L v ≠ none ∧ (v = netShift m L - 1 ∨ v = netShift m L + 1) := by
  rcases finish_boundary m L hL with h | h
  · -- finish 1 ≠ none ⟹ start (1 + netShift) ≠ none
    refine ⟨1 + netShift m L, ?_, Or.inr (by omega)⟩
    intro hstart
    exact h ((finish_none_iff_start_none_shift m L 1).2 hstart)
  · refine ⟨-1 + netShift m L, ?_, Or.inl (by omega)⟩
    intro hstart
    exact h ((finish_none_iff_start_none_shift m L (-1)).2 hstart)

end Deciders.TranslatedCyclers
