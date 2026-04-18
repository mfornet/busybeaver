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
import Busybeaver.Deciders.TranslatedCyclers.Bridge

namespace Deciders.TranslatedCyclers

open TM.Model

variable {BM : Type _} [TM.Model BM]

/--
Reindex the overlap theorem at the current final offset.

Depends on:
- `start_finish_agree_on_overlap`

Idea:
- the same physical tape cell has start coordinate `i + netShift m L` and final coordinate `i`.
-/
private lemma overlap_current_offset
    {m : TickingMachine BM} {A B C : TickingConfig BM} {L : List (Tick BM)}
    (hAB : A t-[m:L]->>' B) (hBC : B t-[m:L]->>' C) :
    ∀ i s,
      startConstraint m L (i + netShift m L) = some s →
      finishConstraint m L i = some s := by
  intro i s hs
  have hshift :
      PartialTape.shift (-netShift m L) (finishConstraint m L) (i + netShift m L) = some s :=
    start_finish_agree_on_overlap hAB hBC (i + netShift m L) s hs
  simpa [PartialTape.shift] using hshift

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

/--
The third configuration satisfies the ordinary start constraint of the transcript.

Depends on:
- `run_implies_models_finish`
- `run_implies_finish_none`
- `overlap_current_offset`
- `start_offset_overlap_or_fresh`
- `fresh_current_cell_is_bot`
- `start_finish_agree_on_overlap`

Idea:
- for each required next-start offset, split on whether the previous run already determined that
  cell in `finishConstraint`;
- overlap is discharged through `finishConstraint`;
- fresh cells come from the untouched reachable frontier and therefore carry `⊥`.
-/
private lemma ticking_extends_start_model
    {m : TickingMachine BM} {A B C : TickingConfig BM} {L : List (Tick BM)}
    {q : TM.Model.State BM} {n : Nat}
    (hReach : (default : TickingConfig BM) -[m]{n}->>' A)
    (hAB : A t-[m:L]->>' B) (hBC : B t-[m:L]->>' C)
    (hRecord : (q, (⊥ : TickSymbol BM)) ∈ L) :
    C.tape ⊨ startConstraint m L := by
  obtain ⟨nB, hReachB_from_A⟩ := TReach.to_multistepBase hAB
  have hReachB : (default : TickingConfig BM) -[m]{n + nB}->>' B :=
    TM.Model.MultistepBase.trans hReach hReachB_from_A
  intro i s hs
  rcases start_offset_overlap_or_fresh hRecord i s hs with hover | ⟨hnone, hsbot⟩
  · have hfin : finishConstraint m L i = some s :=
      overlap_current_offset hAB hBC i s hover
    exact run_implies_models_finish hBC i s hfin
  · have hpres : C.tape.nth i = B.tape.nth (i + netShift m L) :=
      run_implies_finish_none hBC hnone
    have hbot : B.tape.nth (i + netShift m L) = (⊥ : TickSymbol BM) :=
      fresh_current_cell_is_bot hReachB hBC hRecord i hnone
    rw [hpres, hbot, hsbot]

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
    {m : TickingMachine BM} {A B : TickingConfig BM} {L L' : List (Tick BM)}
    {q : TM.Model.State BM} {n : Nat}
    (hReach : (default : TickingConfig BM) -[m]{n}->>' A)
    (h : A t-[m:L]->>' B) (hL' : L' ++ L' <:+ L)
    (hRecord : (q, (⊥ : TickSymbol BM)) ∈ L') :
    ¬TM.Model.halts m A := by
  rw [List.suffix_iff_eq_append] at hL'
  rw [← hL'] at h
  obtain ⟨C, hAC, hCB⟩ := TReach.split h
  have hCnothalts : ¬TM.Model.halts m C := by
    obtain ⟨k, hk⟩ := TReach.to_multistepBase hAC
    have hReachC : (default : TickingConfig BM) -[m]{n + k}->>' C :=
      TM.Model.MultistepBase.trans hReach hk
    exact twice_loop hReachC hCB hRecord
  exact TM.Model.halts.skip (TReach.to_multistep hAC) hCnothalts

end Deciders.TranslatedCyclers
