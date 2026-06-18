/-
High-level looping proof for translated cyclers.

Proof sketch for the missing extension theorem:
1. Strengthen `ticking_extends` with a reachability hypothesis from `default`; without this the
   ticking frontier statement is false for arbitrary wrapped tapes.
2. Build transcript-local start/finish constraints in head-relative coordinates and track the net
   head shift of the transcript.
3. Prove that running a transcript realizes the start constraint, and yields the finish constraint.
4. Use reachability of ticking configs to show that once a `⊥` is observed on one side, every cell
   further out on that side is still `⊥`.
5. Bridge the shifted finish constraint back into the next start constraint, then replay the same
   transcript from the third configuration.

Dependency summary:
1. `Geometry.lean` computes the transcript head walk.
2. `Constraints.lean` defines the start/finish partial tape obligations and replay lemmas.
3. `Frontier.lean` proves the reachable ticking suffix invariant.
4. This file combines overlap plus frontier filling to replay one more transcript copy.
-/
import Busybeaver.Deciders.TranslatedCyclers.Constraints
import Busybeaver.Deciders.TranslatedCyclers.Frontier

namespace Deciders.TranslatedCyclers

open TM.Model

variable {BM : Type _} [TM.Model BM]

/--
Running the same nonempty transcript from two starts produces the same ending control state.

Depends on:
- the fact that the next state of a wrapped step is determined by the transcript tick.

Idea:
- peel the common first tick;
- if the tail is empty, compare the first steps directly;
- otherwise recurse on the common tail.
-/
private lemma transcript_end_state_eq_cons
    {m : TickingMachine BM} {A B A' B' : TickingConfig BM} {t : Tick BM} {L : List (Tick BM)}
    (h : A t-[m:t :: L]->>' B) (h' : A' t-[m:t :: L]->>' B') :
    B.state = B'.state := by
  have hstep_state_eq :
      ∀ {u : Tick BM} {X Y X' Y' : TickingConfig BM},
        (X t-[m:u]->' Y) → (X' t-[m:u]->' Y') → Y.state = Y'.state := by
    intro u X Y X' Y' hXY hX'Y'
    have htX : u = (X.state, X.tape.head) := by
      unfold TReach.TStep stepTick at hXY
      cases hs : TM.Model.step m X with
      | mk dn outcome =>
          cases outcome <;> simp [hs] at hXY
          simpa using hXY.2.symm
    have htX' : u = (X'.state, X'.tape.head) := by
      unfold TReach.TStep stepTick at hX'Y'
      cases hs : TM.Model.step m X' with
      | mk dn outcome =>
          cases outcome <;> simp [hs] at hX'Y'
          simpa using hX'Y'.2.symm
    have hpair : (X.state, X.tape.head) = (X'.state, X'.tape.head) := by
      rw [← htX, htX']
    have hState : X.state = X'.state := by
      exact congrArg Prod.fst hpair
    have hHead : X.tape.head = X'.tape.head := by
      exact congrArg Prod.snd hpair
    have hstmt : TM.Model.stmt m X = TM.Model.stmt m X' := by
      exact TM.Model.stmt_eq_of_state_head_eq m X X' hState hHead
    have hStep : X -[m]->' Y := TReach.single_step hXY
    have hStep' : X' -[m]->' Y' := TReach.single_step hX'Y'
    unfold TM.Model.Step at hStep hStep'
    rw [TM.Model.step_stmt m X] at hStep
    rw [TM.Model.step_stmt m X'] at hStep'
    rw [← hstmt] at hStep'
    cases hstmtX : TM.Model.stmt m X with
    | mk dn stmt =>
        cases stmt with
        | halt =>
            simp [hstmtX] at hStep
        | next sym dir state =>
            simp [hstmtX] at hStep hStep'
            cases hStep
            cases hStep'
            rfl
  have aux :
      ∀ {M : List (Tick BM)} {X Y X' Y' : TickingConfig BM},
        TReach.MultiTStep m M X Y →
        TReach.MultiTStep m M X' Y' →
        M ≠ [] →
        Y.state = Y'.state := by
    intro M
    induction M with
    | nil =>
        intro X Y X' Y' hXY hX'Y' hne
        cases (hne rfl)
    | cons t₀ M IH =>
        intro X Y X' Y' hXY hX'Y' _hneq
        cases M with
        | nil =>
            cases hXY with
            | step X Z Y t₀ L₀ hXZ hZY =>
                cases hZY
                cases hX'Y' with
                | step X' Z' Y' t₀ L₀' hX'Z' hZ'Y' =>
                    cases hZ'Y'
                    exact hstep_state_eq hXZ hX'Z'
        | cons t₁ M' =>
            cases hXY with
            | step X Z Y t₀ L₀ hXZ hZY =>
                cases hX'Y' with
                | step X' Z' Y' t₀ L₀' hX'Z' hZ'Y' =>
                    exact IH hZY hZ'Y' (by simp)
  exact aux h h' (by simp)

/-- The statement of a continuing tick is a `next` (it does not halt). -/
private lemma tstep_stmtOfTick_next {m : TickingMachine BM} {A B : TickingConfig BM} {t : Tick BM}
    (h : A t-[m:t]->' B) :
    ∃ dn sym dir st, stmtOfTick m t = (dn, GStmt.next sym dir st) := by
  have ht : t = (A.state, A.tape.head) := by
    unfold TReach.TStep stepTick at h
    cases hs : TM.Model.step m A with
    | mk dn outcome =>
        cases outcome <;> simp [hs] at h
        simpa using h.2.symm
  have hstep : A -[m]->' B := TReach.single_step h
  unfold TM.Model.Step at hstep
  rw [TM.Model.step_stmt m A] at hstep
  have hconfig : stmtOfTick m t = TM.Model.stmt m A := by
    rw [ht]
    unfold stmtOfTick
    apply TM.Model.stmt_eq_of_state_head_eq m
    · simp [configOfTick]
    · rfl
  rw [hconfig]
  cases hstmt : TM.Model.stmt m A with
  | mk dn stmt =>
      cases stmt with
      | halt => rw [hstmt] at hstep; simp at hstep
      | next sym dir st => exact ⟨dn, sym, dir, st, rfl⟩

/-- Every symbol recorded by the finish constraint of a *run* is a real (non-`⊥`) write. -/
private lemma run_finish_write_nonbot {m : TickingMachine BM} {A B : TickingConfig BM}
    {L : List (Tick BM)} (h : A t-[m:L]->>' B) :
    ∀ k w, finishConstraint m L k = some w → w ≠ (⊥ : TickSymbol BM) := by
  induction h with
  | refl C => intro k w hk; simp [finishConstraint] at hk
  | step X Y Z t L' hstep htail IH =>
      intro k w hk
      rw [finishConstraint_cons, PartialTape.merge_eq_some] at hk
      rcases hk with hk | ⟨_, hk⟩
      · exact IH k w hk
      · simp only [PartialTape.singleton] at hk
        split at hk
        · injection hk with hk
          obtain ⟨dn, sym, dir, st, hnext⟩ := tstep_stmtOfTick_next hstep
          rw [← hk]
          exact writeOfTick_ne_bot_of_next hnext
        · simp at hk

/-- A `⊥`-read in the transcript of a *run* is recorded by the start constraint: there is an offset
the run reads `⊥` at first visit. (False without realizability — the `⊥` could be overwritten in an
arbitrary transcript; the run rules that out.) -/
private lemma record_bot {m : TickingMachine BM} {A B : TickingConfig BM} {L : List (Tick BM)}
    {q : TM.Model.State BM} (h : A t-[m:L]->>' B) (hRecord : (q, (⊥ : TickSymbol BM)) ∈ L) :
    ∃ p, startConstraint m L p = some (⊥ : TickSymbol BM) := by
  induction h with
  | refl C => exact absurd hRecord (by simp)
  | step X Y Z t L' hstep htail IH =>
      rcases List.mem_cons.mp hRecord with hEq | hMem
      · refine ⟨0, ?_⟩
        rw [startConstraint_zero, ← hEq]
      · obtain ⟨p', hp'⟩ := IH hMem
        by_cases hz : p' + shiftDelta (dirOfTick m t) = 0
        · exfalso
          have hp'val : p' = -shiftDelta (dirOfTick m t) := by omega
          have hY : Y.tape.nth p' = (⊥ : TickSymbol BM) :=
            run_implies_models_start htail p' ⊥ hp'
          rw [hp'val] at hY
          rw [tstep_written_cell hstep] at hY
          obtain ⟨dn, sym, dir, st, hnext⟩ := tstep_stmtOfTick_next hstep
          exact writeOfTick_ne_bot_of_next hnext hY
        · refine ⟨p' + shiftDelta (dirOfTick m t), ?_⟩
          rw [startConstraint_cons_apply_of_ne m t L' hz]
          simpa using hp'

/--
Frontier fact for the *fresh* offsets of a detected loop.

Consider an offset `j` that the transcript reads at its start (`startConstraint m L j = some s`) but
whose write the run `B → C` never pins down (`finishConstraint m L j = none`). Such an offset lies
just *beyond* the visited window on the side the head is translating toward. This lemma states that
both the required start symbol `s` and the actual cell `B.tape` carries there are `⊥`.

Why both are `⊥` (informal):
- Writes are never `⊥` (`stmt_next_nonbot`), so every already-visited ("exhaust") cell is non-`⊥`.
  Hence a `⊥`-read (which `hRecord` guarantees exists) can only happen at a cell the run reaches for
  the *first* time, i.e. at the moving frontier.
- For a reachable tape the non-`⊥` cells form a bounded prefix on each side
  (`SidePrefixes` / `reachable_nonbot_interval`). Combined with the previous point, the run's visited
  window reaches the frontier on the translation side, so every cell strictly beyond it is `⊥`
  (`reachable_bot_suffix_left` / `reachable_bot_suffix_right`).
- The two runs `A → B` and `B → C` realize the *same* transcript, which forces the agreement used to
  transport the frontier `⊥` between the two configurations.

This is the genuine core of translated-cycler correctness; it crucially needs *both* runs (a
single-run version is false: a config could carry non-`⊥` junk beyond an under-reaching run).
-/
private lemma fresh_cell_is_bot
    {m : TickingMachine BM} {A B C : TickingConfig BM} {L : List (Tick BM)}
    {q : TM.Model.State BM} {n : Nat}
    (hReach : (default : TickingConfig BM) -[m]{n}->>' A)
    (hAB : A t-[m:L]->>' B) (hBC : B t-[m:L]->>' C)
    (hRecord : (q, (⊥ : TickSymbol BM)) ∈ L)
    {j : Int} {s : TickSymbol BM}
    (hstart : startConstraint m L j = some s)
    (hfin : finishConstraint m L j = none) :
    s = (⊥ : TickSymbol BM) ∧ B.tape.nth (j + netShift m L) = (⊥ : TickSymbol BM) := by
  -- A `⊥`-read witness `p`, defined in the start constraint.
  have hL : L ≠ [] := List.ne_nil_of_mem hRecord
  obtain ⟨p, hp⟩ := record_bot hAB hRecord
  have hpne : startConstraint m L p ≠ none := by rw [hp]; simp
  have hsne : startConstraint m L j ≠ none := by rw [hstart]; simp
  have h0ne : startConstraint m L 0 ≠ none := startConstraint_zero_ne_none_of_ne_none m L j hsne
  -- `A` and `B` carry `⊥` at `p`.
  have hAp : A.tape.nth p = (⊥ : TickSymbol BM) := run_implies_models_start hAB p ⊥ hp
  have hBp : B.tape.nth p = (⊥ : TickSymbol BM) := run_implies_models_start hBC p ⊥ hp
  -- `p` is fresh for the run `A → B` too: its write is never pinned (else it would be non-`⊥`).
  have hfinp : finishConstraint m L p = none := by
    cases hfp : finishConstraint m L p with
    | none => rfl
    | some w =>
        have hw1 : B.tape.nth p = w := run_implies_models_finish hAB p w hfp
        have hw2 : w ≠ (⊥ : TickSymbol BM) := run_finish_write_nonbot hAB p w hfp
        rw [hBp] at hw1
        exact absurd hw1.symm hw2
  -- Second `⊥` witness in `A`, one period out.
  have hApΔ : A.tape.nth (p + netShift m L) = (⊥ : TickSymbol BM) := by
    have h := run_implies_finish_none hAB hfinp
    rw [hBp] at h
    exact h.symm
  -- Reframe both goals onto `A`'s tape.
  have hBj : B.tape.nth j = s := run_implies_models_start hBC j s hstart
  have hsA : s = A.tape.nth (j + netShift m L) := by
    have h := run_implies_finish_none hAB hfin
    rw [hBj] at h
    exact h
  have hstartjΔ : startConstraint m L (j + netShift m L) = none :=
    (finish_none_iff_start_none_shift m L j).1 hfin
  have hstartpΔ : startConstraint m L (p + netShift m L) = none :=
    (finish_none_iff_start_none_shift m L p).1 hfinp
  -- A pure cycler (`netShift = 0`) has no fresh offsets, so `netShift ≠ 0`.
  have hΔne : netShift m L ≠ 0 := by
    intro h0; rw [h0, add_zero] at hstartjΔ; exact hsne hstartjΔ
  rcases lt_or_gt_of_ne hΔne with hΔneg | hΔpos
  · -- Translation to the left: the fresh cells lie left of the visited window.
    have hpjΔ : j + netShift m L < p := by
      by_contra hle; push_neg at hle
      exact hpne (startConstraint_none_left m L hsne hstartjΔ (by omega) hle)
    obtain ⟨v, hvne, hveq⟩ := start_boundary m L hL
    have hvjΔ : j + netShift m L < v := by
      by_contra hle; push_neg at hle
      exact hvne (startConstraint_none_left m L hsne hstartjΔ (by omega) hle)
    have hj0 : j ≤ 0 := by rcases hveq with h | h <;> omega
    have hpΔneg : p + netShift m L ≤ -1 := by
      by_contra hle; push_neg at hle
      exact (startConstraint_convex m L h0ne hpne (by omega) (by omega)) hstartpΔ
    have claim : ∀ x, x ≤ j + netShift m L → A.tape.nth x = (⊥ : TickSymbol BM) := by
      intro x hx
      by_cases hpm1 : p ≤ -1
      · exact reachable_bot_mono_left hReach hpm1 (by omega) hAp
      · push_neg at hpm1
        exact reachable_bot_mono_left hReach hpΔneg (by omega) hApΔ
    have hstartj2Δ : startConstraint m L (j + 2 * netShift m L) = none :=
      startConstraint_none_left m L hsne hstartjΔ (by omega) (by omega)
    have hfinjΔ : finishConstraint m L (j + netShift m L) = none := by
      rw [finish_none_iff_start_none_shift]
      rw [show (j + netShift m L) + netShift m L = j + 2 * netShift m L from by omega]
      exact hstartj2Δ
    have hBjΔ : B.tape.nth (j + netShift m L) = A.tape.nth (j + 2 * netShift m L) := by
      have h := run_implies_finish_none hAB hfinjΔ
      rw [show (j + netShift m L) + netShift m L = j + 2 * netShift m L from by omega] at h
      exact h
    refine ⟨?_, ?_⟩
    · rw [hsA]; exact claim _ (le_refl _)
    · rw [hBjΔ]; exact claim _ (by omega)
  · -- Translation to the right: the fresh cells lie right of the visited window.
    have hpjΔ : p < j + netShift m L := by
      by_contra hle; push_neg at hle
      exact hpne (startConstraint_none_right m L hsne hstartjΔ (by omega) hle)
    obtain ⟨v, hvne, hveq⟩ := start_boundary m L hL
    have hvjΔ : v < j + netShift m L := by
      by_contra hle; push_neg at hle
      exact hvne (startConstraint_none_right m L hsne hstartjΔ (by omega) hle)
    have hj0 : 0 ≤ j := by rcases hveq with h | h <;> omega
    have hpΔ1 : 1 ≤ p + netShift m L := by
      by_contra hle; push_neg at hle
      exact (startConstraint_convex m L hpne h0ne (by omega) (by omega)) hstartpΔ
    have claim : ∀ x, j + netShift m L ≤ x → A.tape.nth x = (⊥ : TickSymbol BM) := by
      intro x hx
      by_cases hp1 : 1 ≤ p
      · exact reachable_bot_mono_right hReach hp1 (by omega) hAp
      · push_neg at hp1
        exact reachable_bot_mono_right hReach hpΔ1 (by omega) hApΔ
    have hstartj2Δ : startConstraint m L (j + 2 * netShift m L) = none :=
      startConstraint_none_right m L hsne hstartjΔ (by omega) (by omega)
    have hfinjΔ : finishConstraint m L (j + netShift m L) = none := by
      rw [finish_none_iff_start_none_shift]
      rw [show (j + netShift m L) + netShift m L = j + 2 * netShift m L from by omega]
      exact hstartj2Δ
    have hBjΔ : B.tape.nth (j + netShift m L) = A.tape.nth (j + 2 * netShift m L) := by
      have h := run_implies_finish_none hAB hfinjΔ
      rw [show (j + netShift m L) + netShift m L = j + 2 * netShift m L from by omega] at h
      exact h
    refine ⟨?_, ?_⟩
    · rw [hsA]; exact claim _ (le_refl _)
    · rw [hBjΔ]; exact claim _ (by omega)

/--
The third configuration satisfies the ordinary start constraint of the transcript.

Depends on:
- `run_implies_models_finish`
- `run_implies_finish_none`
- `start_finish_agree_on_overlap`
- `fresh_cell_is_bot`

Idea:
- for each required next-start offset, split on whether the run `B → C` already determined that
  cell in `finishConstraint`;
- overlap is discharged through `finishConstraint` plus `start_finish_agree_on_overlap`;
- fresh cells come from the untouched reachable frontier and therefore carry `⊥`
  (`fresh_cell_is_bot`).
-/
private lemma ticking_extends_start_model
    {m : TickingMachine BM} {A B C : TickingConfig BM} {L : List (Tick BM)}
    {q : TM.Model.State BM} {n : Nat}
    -- TODO: Replace this with (default -[m]->* A) here and everywhere else where the value of `n` is not used or constrained in the hypotheses.
    (hReach : (default : TickingConfig BM) -[m]{n}->>' A)
    (hAB : A t-[m:L]->>' B) (hBC : B t-[m:L]->>' C)
    (hRecord : (q, (⊥ : TickSymbol BM)) ∈ L) :
    C.tape ⊨ startConstraint m L := by
  intro j s hstart
  -- Goal: `C.tape.nth j = s`. Split on whether the run `B → C` already determined cell `j`
  -- (in final/`C`-relative coordinates) via its finish constraint.
  cases hfin : finishConstraint m L j with
  | some w =>
      -- Overlap: `C` realizes the finish constraint of `B → C`, and the start/finish values
      -- agree at this offset because they are both realized by the shared config `B`.
      have hCw : C.tape.nth j = w := run_implies_models_finish hBC j w hfin
      have hsw : s = w := start_finish_agree_on_overlap hAB hBC j s w hstart hfin
      rw [hCw, hsw]
  | none =>
      -- Fresh: cell `j` was untouched by `B → C`, so its value comes from the reachable frontier.
      -- We reduce to two `⊥` facts: the required start value `s` and the actual cell `B.tape`
      -- carries at the corresponding (start-coordinate) offset `j + netShift m L`.
      have hC : C.tape.nth j = B.tape.nth (j + netShift m L) := run_implies_finish_none hBC hfin
      obtain ⟨hs_bot, hcell_bot⟩ := fresh_cell_is_bot hReach hAB hBC hRecord hstart hfin
      rw [hC, hs_bot, hcell_bot]

/--
Reachable transcript extension theorem.

Depends on:
- `ticking_extends_start_model`
- `models_start_implies_exists_run`

Idea:
- show that the third configuration satisfies the ordinary start constraint, note that its control
  state matches the repeated start state, and replay the transcript from there.
-/
private lemma ticking_extends
    {m : TickingMachine BM} {A B C : TickingConfig BM} {L : List (Tick BM)}
    {q : TM.Model.State BM} {n : Nat}
    (hReach : (default : TickingConfig BM) -[m]{n}->>' A)
    (hAB : A t-[m:L]->>' B) (hBC : B t-[m:L]->>' C)
    (hRecord : (q, (⊥ : TickSymbol BM)) ∈ L) :
    ∃ D, C t-[m:L]->>' D := by
  cases L with
  | nil =>
      cases hRecord
  | cons t L' =>
      have hState' : B.state = C.state :=
        transcript_end_state_eq_cons
          (A := A) (B := B) (A' := B) (B' := C) (t := t) (L := L')
          hAB hBC
      have hState : C.state = B.state := hState'.symm
      have hStart : C.tape ⊨ startConstraint m (t :: L') :=
        ticking_extends_start_model hReach hAB hBC hRecord
      exact models_start_implies_exists_run hBC hState hStart

private lemma ticking_extends_many
    {m : TickingMachine BM} {A B C : TickingConfig BM} {L : List (Tick BM)}
    {q : TM.Model.State BM} {n₀ : Nat}
    (hReach : (default : TickingConfig BM) -[m]{n₀}->>' A)
    (hAB : A t-[m:L]->>' B) (hBC : B t-[m:L]->>' C)
    (hRecord : (q, (⊥ : TickSymbol BM)) ∈ L) :
    ∀ n, ∃ D, B t-[m:List.repeat L n]->>' D := by
  intro n
  induction n generalizing A B C n₀ with
  | zero =>
      exact ⟨B, .refl B⟩
  | succ n IH =>
      obtain ⟨D, hCD⟩ := ticking_extends hReach hAB hBC hRecord
      obtain ⟨nB, hReachB⟩ := TReach.to_multistepBase hAB
      obtain ⟨E, hDE⟩ := IH (TM.Model.MultistepBase.trans hReach hReachB) hBC hCD
      exact ⟨E, by
        simpa [List.repeat_succ] using TReach.trans hBC hDE⟩

private lemma ticking_loops
    {m : TickingMachine BM} {A B C : TickingConfig BM} {L : List (Tick BM)}
    {q : TM.Model.State BM} {n₀ : Nat}
    (hReach : (default : TickingConfig BM) -[m]{n₀}->>' A)
    (hAB : A t-[m:L]->>' B) (hBC : B t-[m:L]->>' C)
    (hRecord : (q, (⊥ : TickSymbol BM)) ∈ L) :
    ¬TM.Model.halts m A := by
  intro hhalts
  obtain ⟨n, E, hEl, hEr⟩ := hhalts
  have hLlen : 0 < L.length := List.length_pos_of_mem hRecord
  have hLrep : n < (List.repeat L (n / L.length + 1)).length := by
    rw [List.repeat_length, Nat.add_comm, Nat.add_mul, one_mul]
    simpa [Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using Nat.lt_div_mul_add hLlen
  obtain ⟨E', hBE'⟩ := ticking_extends_many hReach hAB hBC hRecord (n / L.length)
  have hAE' : A t-[m:L ++ List.repeat L (n / L.length)]->>' E' := TReach.trans hAB hBE'
  have hAE'ms : A -[m]{(L ++ List.repeat L (n / L.length)).length}->' E' := TReach.to_multistep hAE'
  have hEE' : E -[m]{(L ++ List.repeat L (n / L.length)).length - n}->' E' := by
    exact TM.Model.Multistep.split_le hAE'ms hEr (Nat.le_of_lt hLrep)
  refine TM.Model.halts_in_base.no_multistep' hEl ?_ hEE'
  simpa [List.length_append] using Nat.sub_pos_of_lt hLrep

private lemma twice_loop
    {m : TickingMachine BM} {A B : TickingConfig BM} {L : List (Tick BM)}
    {q : TM.Model.State BM} {n : Nat}
    (hReach : (default : TickingConfig BM) -[m]{n}->>' A)
    (h : A t-[m:L ++ L]->>' B) (hRecord : (q, (⊥ : TickSymbol BM)) ∈ L) :
    ¬TM.Model.halts m A := by
  obtain ⟨C, hAC, hCB⟩ := TReach.split h
  exact ticking_loops hReach hAC hCB hRecord

theorem twice_suffix_loop
    {m : TickingMachine BM} {A : TickingConfig BM} {L L' : List (Tick BM)}
    {q : TM.Model.State BM}
    (h : (default : TickingConfig BM) t-[m:L]->>' A) (hL' : L' ++ L' <:+ L)
    (hRecord : (q, (⊥ : TickSymbol BM)) ∈ L') :
    ¬TM.Model.halts m (default : TickingConfig BM) := by
  rw [List.suffix_iff_eq_append] at hL'
  rw [← hL'] at h
  obtain ⟨C, hAC, hCB⟩ := TReach.split h
  have hCnothalts : ¬TM.Model.halts m C := by
    obtain ⟨k, hk⟩ := TReach.to_multistepBase hAC
    exact twice_loop hk hCB hRecord
  exact TM.Model.halts.skip (TReach.to_multistep hAC) hCnothalts

end Deciders.TranslatedCyclers
