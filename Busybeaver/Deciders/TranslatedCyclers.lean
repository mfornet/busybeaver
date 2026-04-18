/-
Translated cycler decider based on [transcripts](https://www.sligocki.com/2024/06/12/tm-transcripts.html).

The ticking behavior is implemented as a wrapper machine in `TM.Wrappers.Ticking`; the decider
itself only runs a search over that wrapped machine and then discharges the corresponding proof
obligations separately.
-/
import Busybeaver.TM.Model.Reachability
import Busybeaver.TM.Wrappers.Ticking

namespace Deciders.TranslatedCyclers

open TM.Model

variable {BM : Type _} [TM.Model BM]

abbrev TickingMachine (BM : Type _) [TM.Model BM] := TM.Wrappers.Ticking.Machine BM
abbrev TickingConfig (BM : Type _) [TM.Model BM] := TM.Model.Config (TickingMachine BM)
abbrev TickSymbol (BM : Type _) [TM.Model BM] := WithBot (TM.Model.Symbol BM)
abbrev Tick (BM : Type _) [TM.Model BM] := TM.Model.State BM × TickSymbol BM

def stepTick (m : TickingMachine BM) (C : TickingConfig BM) :
    TM.StepResult (TickingConfig BM × Tick BM) :=
  match TM.Model.step m C with
  | ⟨dn, .halted _⟩ => ⟨dn, .halted (C, (C.state, C.tape.head))⟩
  | ⟨dn, .continue cfg⟩ => ⟨dn, .continue (cfg, (C.state, C.tape.head))⟩

namespace TReach

-- TODO: This should not be expressed in terms of ticking machines, but rather as a generalization of `Multistep`
--       This should be in reachability without mentioning any specific machine, but instead talk about Models.
-- TODO: Let's rename Ticking Machines to Unwritten Machine (i.e they have the ability to distinguish between written and unwritten cells).
def TStep (m : TickingMachine BM) (A : TickingConfig BM) (t : Tick BM)
    (B : TickingConfig BM) : Prop :=
  (stepTick m A).outcome = .continue (B, t)

notation A " t-[" m ":" t "]->' " B => TStep m A t B

inductive MultiTStep (m : TickingMachine BM) :
    List (Tick BM) → TickingConfig BM → TickingConfig BM → Prop
| refl C : MultiTStep m [] C C
| step A B C t L : (A t-[m:t]->' B) → MultiTStep m L B C → MultiTStep m (t :: L) A C

notation A " t-[" m ":" L "]->>' " B => MultiTStep m L A B

lemma single_step {m : TickingMachine BM} (h : A t-[m:t]->' B) : A -[m]->' B := by
  unfold TStep at h
  unfold TM.Model.Step
  unfold stepTick at h
  cases hs : TM.Model.step m A with
  | mk dn outcome =>
      cases outcome <;> simp [hs] at h ⊢
      exact h.1

lemma to_multistep {m : TickingMachine BM} (h : A t-[m:L]->>' B) : A -[m]{L.length}->' B := by
  induction h with
  | refl =>
      exact .refl
  | step A B C t L hAB hBC IH =>
      simpa using TM.Model.Multistep.step (single_step hAB) IH

lemma to_multistepBase {m : TickingMachine BM} (h : A t-[m:L]->>' B) : ∃ n, A -[m]{n}->>' B := by
  exact TM.Model.Multistep.to_base (to_multistep h)

lemma trans {m : TickingMachine BM} (hAB : A t-[m:L]->>' B) (hBC : B t-[m:L']->>' C) :
    A t-[m:L ++ L']->>' C := by
  induction hAB with
  | refl =>
      simpa using hBC
  | step A B D t L hAB hBD IH =>
      simpa using
        MultiTStep.step (A := A) (B := B) (C := C) (t := t) (L := L ++ L') hAB (IH hBC)

lemma split {m : TickingMachine BM} (h : A t-[m:L ++ L']->>' B) :
    ∃ C, (A t-[m:L]->>' C) ∧ (C t-[m:L']->>' B) := by
  induction L generalizing A with
  | nil =>
      exact ⟨A, TReach.MultiTStep.refl A, by simpa using h⟩
  | cons t L IH =>
      cases h with
      | step A B C _ L'' hAB hBC =>
          obtain ⟨C, hAC, hCB⟩ := IH hBC
          exact ⟨C, MultiTStep.step (A := A) (B := B) (C := C) (t := t) (L := L) hAB hAC, hCB⟩

end TReach

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
  transcript := by simpa using TReach.MultiTStep.refl (default : TickingConfig BM)
  multistepBase := .refl
}

end TickCache

private lemma stepTick_halts
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

private lemma stepTick_continue_valid
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

private def List.repeat (L : List α) : Nat → List α
  | 0 => []
  | n + 1 => L ++ List.repeat L n

@[simp] private lemma List.repeat_zero : List.repeat L 0 = [] := rfl

@[simp] private lemma List.repeat_succ : List.repeat L (n + 1) = L ++ List.repeat L n := rfl

private lemma List.repeat_concat_comm : List.repeat L n ++ L = L ++ List.repeat L n := by
  induction n with
  | zero =>
      simp
  | succ n IH =>
      simp [IH, List.append_assoc]

@[simp] private lemma List.repeat_length : (List.repeat L n).length = n * L.length := by
  induction n with
  | zero =>
      simp
  | succ n IH =>
      simp [IH, Nat.succ_mul, Nat.add_comm]

@[simp] private lemma List.repeat_add : List.repeat L (n + k) = List.repeat L n ++ List.repeat L k := by
  induction k with
  | zero =>
      simp
  | succ k IH =>
      have hk : n + (k + 1) = (n + k) + 1 := by omega
      rw [hk, List.repeat_succ, IH, List.repeat_succ]
      rw [← List.append_assoc, ← List.repeat_concat_comm, List.append_assoc]

private lemma ticking_extends
    {m : TickingMachine BM} {A B C : TickingConfig BM} {L : List (Tick BM)}
    {q : TM.Model.State BM}
    (hAB : A t-[m:L]->>' B) (hBC : B t-[m:L]->>' C)
    (hRecord : (q, (⊥ : TickSymbol BM)) ∈ L)
    (hReachA : default -[m]->*' A) :
    ∃ D, C t-[m:L]->>' D := by
  sorry

private lemma ticking_extends_many
    {m : TickingMachine BM} {A B C : TickingConfig BM} {L : List (Tick BM)}
    {q : TM.Model.State BM}
    (hAB : A t-[m:L]->>' B) (hBC : B t-[m:L]->>' C)
    (hRecord : (q, (⊥ : TickSymbol BM)) ∈ L)
    (hReachA : default -[m]->*' A) :
    ∀ n, ∃ D, B t-[m:List.repeat L n]->>' D := by
  intro n
  induction n generalizing A B C with
  | zero =>
      exact ⟨B, .refl B⟩
  | succ n IH =>
      have hReachB : (default : TickingConfig BM) -[m]->*' B := by
        exact TM.Model.Machine.EvStep.trans hReachA
          (TM.Model.Multistep.to_evstep (TReach.to_multistep hAB))
      obtain ⟨D, hCD⟩ := ticking_extends hAB hBC hRecord hReachA
      obtain ⟨E, hDE⟩ := IH hBC hCD hReachB
      exact ⟨E, by
        simpa [List.repeat_succ] using TReach.trans hBC hDE⟩

private lemma ticking_loops
    {m : TickingMachine BM} {A B C : TickingConfig BM} {L : List (Tick BM)}
    {q : TM.Model.State BM}
    (hAB : A t-[m:L]->>' B) (hBC : B t-[m:L]->>' C)
    (hRecord : (q, (⊥ : TickSymbol BM)) ∈ L)
    (hReachA : default -[m]->*' A) :
    ¬TM.Model.halts m A := by
  intro hhalts
  obtain ⟨n, E, hEl, hEr⟩ := hhalts
  have hLlen : 0 < L.length := List.length_pos_of_mem hRecord
  have hLrep : n < (List.repeat L (n / L.length + 1)).length := by
    rw [List.repeat_length, Nat.add_comm, Nat.add_mul, one_mul]
    simpa [Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using Nat.lt_div_mul_add hLlen
  obtain ⟨E', hBE'⟩ := ticking_extends_many hAB hBC hRecord hReachA (n / L.length)
  have hAE' : A t-[m:L ++ List.repeat L (n / L.length)]->>' E' := TReach.trans hAB hBE'
  have hAE'ms : A -[m]{(L ++ List.repeat L (n / L.length)).length}->' E' := TReach.to_multistep hAE'
  have hEE' : E -[m]{(L ++ List.repeat L (n / L.length)).length - n}->' E' := by
    exact TM.Model.Multistep.split_le hAE'ms hEr (Nat.le_of_lt hLrep)
  refine TM.Model.halts_in_base.no_multistep' hEl ?_ hEE'
  simpa [List.length_append] using Nat.sub_pos_of_lt hLrep

private lemma twice_loop
    {m : TickingMachine BM} {A B : TickingConfig BM} {L : List (Tick BM)}
    {q : TM.Model.State BM}
    (h : A t-[m:L ++ L]->>' B) (hRecord : (q, (⊥ : TickSymbol BM)) ∈ L)
    (hReachA : default -[m]->*' A) :
    ¬TM.Model.halts m A := by
  obtain ⟨C, hAC, hCB⟩ := TReach.split h
  exact ticking_loops hAC hCB hRecord hReachA

theorem twice_suffix_loop
    {m : TickingMachine BM} {A : TickingConfig BM} {L L' : List (Tick BM)}
    {q : TM.Model.State BM}
    (h : (default : TickingConfig BM) t-[m:L]->>' A) (hL' : L' ++ L' <:+ L)
    (hRecord : (q, (⊥ : TickSymbol BM)) ∈ L') :
    ¬TM.Model.halts m (default : TickingConfig BM) := by
  rw [List.suffix_iff_eq_append] at hL'
  rw [← hL'] at h
  obtain ⟨C, hAC, hCB⟩ := TReach.split h
  have hReachC : default -[m]->*' C := by
    exact TM.Model.Multistep.to_evstep (TReach.to_multistep hAC)
  have hCnothalts : ¬TM.Model.halts m C := by
    exact twice_loop hCB hRecord hReachC
  exact TM.Model.halts.skip_evstep
    (TM.Model.Multistep.to_evstep (TReach.to_multistep hAC)) hCnothalts

inductive SearchResult : TickingMachine BM → Type _
  | timeout {m : TickingMachine BM} (cache : TickCache m) : SearchResult m
  | halts {m : TickingMachine BM} (cache : TickCache m) : SearchResult m
  | loops {m : TickingMachine BM} (cache : TickCache m)
      (loop : {L : List (Tick BM) //
        L ++ L <:+ cache.history.reverse ∧ ∃ q, (q, (⊥ : TickSymbol BM)) ∈ L}) :
      SearchResult m

mutual

private def runSearchNext
    (m : TickingMachine BM) (n : Nat) (cache : TickCache m) :
    TM.StepResult (TickingConfig BM × Tick BM) → SearchResult m
  | ⟨_, .halted _⟩ =>
      .halts cache
  | ⟨dn, .continue (cfg, t)⟩ =>
      let cache' : TickCache m := {
        cfg := cfg
        history := t :: cache.history
        baseSteps := cache.baseSteps + dn
      }
      if hb : t.2 = (⊥ : TickSymbol BM) then
        match detectFrontLoop t.1 cache.history with
        | some Lh =>
            .loops cache' ⟨Lh.1.reverse, by
              obtain ⟨L, hL, hq⟩ := Lh
              have ht : (t.1, (⊥ : TickSymbol BM)) = t := by
                cases t with
                | mk q b =>
                    simp at hb
                    cases hb
                    rfl
              constructor
              · have hL' : L.reverse ++ L.reverse <:+ (t :: cache.history).reverse := by
                  conv_lhs =>
                    rw [← List.reverse_append]
                  rw [List.reverse_suffix]
                  simpa [ht] using hL
                simpa [cache'] using hL'
              · exact ⟨t.1, by simpa [List.mem_reverse] using hq⟩⟩
        | none => runSearchLoop m n cache'
      else
        runSearchLoop m n cache'

private def runSearchLoop (m : TickingMachine BM) : Nat → TickCache m → SearchResult m
  | .zero, cache => .timeout cache
  | .succ n, cache => runSearchNext m n cache (stepTick m cache.cfg)

end

@[specialize bound]
def runSearchWrapped (bound : Nat) (m : TickingMachine BM)
    (start : TickCache m := TickCache.initial m) :
    SearchResult m :=
  runSearchLoop m bound start

lemma haltsResult_gives_wrappedHalts
    {bound : Nat} {m : TickingMachine BM} {start cache : TickCache m}
    (hvalid : TickCache.Valid m start)
    (hSearch : runSearchWrapped bound m start = .halts cache) :
    TM.Model.LastState m cache.cfg ∧
      ((default : TickingConfig BM) -[m]{cache.baseSteps}->>' cache.cfg) := by
  induction bound generalizing start with
  | zero =>
      simp [runSearchWrapped, runSearchLoop] at hSearch
  | succ bound IH =>
      cases hstep : stepTick m start.cfg with
      | mk dn outcome =>
          cases hout : outcome <;> rename_i out
          ·
            have hstep' : stepTick m start.cfg = ⟨dn, .continue out⟩ := by
              simpa [hout] using hstep
            rcases out with ⟨cfg, t⟩
            let start' : TickCache m := {
              cfg := cfg
              history := t :: start.history
              baseSteps := start.baseSteps + dn
            }
            have hvalid' : TickCache.Valid m start' := stepTick_continue_valid hvalid hstep'
            by_cases hb : t.2 = (⊥ : TickSymbol BM)
            · cases hdet : detectFrontLoop t.1 start.history with
              | some Lh =>
                  have : False := by
                    simp [runSearchWrapped, runSearchLoop, runSearchNext, hstep, hout, hb, hdet] at hSearch
                  exact False.elim this
              | none =>
                  have hSearch' : runSearchWrapped bound m start' = SearchResult.halts cache := by
                    simpa [runSearchWrapped, runSearchLoop, runSearchNext, hstep, hout, hb, hdet, start'] using hSearch
                  exact IH hvalid' hSearch'
            · have hSearch' : runSearchWrapped bound m start' = SearchResult.halts cache := by
                simpa [runSearchWrapped, runSearchLoop, runSearchNext, hstep, hout, hb, start'] using hSearch
              exact IH hvalid' hSearch'
          ·
            have hstep' : stepTick m start.cfg = ⟨dn, .halted out⟩ := by
              simpa [hout] using hstep
            have hEq : start = cache := by
              simpa [runSearchWrapped, runSearchLoop, runSearchNext, hstep, hout] using hSearch
            cases hEq
            exact stepTick_halts hvalid hstep'

private lemma loopResult_gives_nonHalting_fromDefault
    {bound : Nat} {m : TickingMachine BM} {start cache : TickCache m}
    {loopWitness : {L : List (Tick BM) //
      L ++ L <:+ cache.history.reverse ∧ ∃ q, (q, (⊥ : TickSymbol BM)) ∈ L}}
    (hvalid : TickCache.Valid m start)
    (hSearch : runSearchWrapped bound m start = .loops cache loopWitness) :
    ¬TM.Model.halts m (default : TickingConfig BM) := by
  induction bound generalizing start with
  | zero =>
      simp [runSearchWrapped, runSearchLoop] at hSearch
  | succ bound IH =>
      cases hstep : stepTick m start.cfg with
      | mk dn outcome =>
          cases hout : outcome <;> rename_i out
          ·
            have hstep' : stepTick m start.cfg = ⟨dn, .continue out⟩ := by
              simpa [hout] using hstep
            rcases out with ⟨cfg, t⟩
            let start' : TickCache m := {
              cfg := cfg
              history := t :: start.history
              baseSteps := start.baseSteps + dn
            }
            have hvalid' : TickCache.Valid m start' := stepTick_continue_valid hvalid hstep'
            by_cases hb : t.2 = (⊥ : TickSymbol BM)
            · cases hdet : detectFrontLoop t.1 start.history with
              | some Lh =>
                  have hEq : SearchResult.loops start' ⟨Lh.1.reverse, by
                      obtain ⟨L, hL, hq⟩ := Lh
                      have ht : (t.1, (⊥ : TickSymbol BM)) = t := by
                        cases t with
                        | mk q b =>
                            simp at hb
                            cases hb
                            rfl
                      constructor
                      · have hL' : L.reverse ++ L.reverse <:+ (t :: start.history).reverse := by
                          conv_lhs =>
                            rw [← List.reverse_append]
                          rw [List.reverse_suffix]
                          simpa [ht] using hL
                        simpa [start'] using hL'
                      · exact ⟨t.1, by simpa [List.mem_reverse] using hq⟩⟩ = SearchResult.loops cache loopWitness := by
                    simpa [runSearchWrapped, runSearchLoop, runSearchNext, hstep, hout, hb, hdet, start'] using hSearch
                  have hcache : start' = cache := by
                    injection hEq with hcache
                  subst hcache
                  rcases loopWitness.2.2 with ⟨q, hq⟩
                  exact twice_suffix_loop hvalid'.transcript loopWitness.2.1 hq
              | none =>
                  have hSearch' : runSearchWrapped bound m start' = SearchResult.loops cache loopWitness := by
                    simpa [runSearchWrapped, runSearchLoop, runSearchNext, hstep, hout, hb, hdet, start'] using hSearch
                  exact IH hvalid' hSearch'
            · have hSearch' : runSearchWrapped bound m start' = SearchResult.loops cache loopWitness := by
                simpa [runSearchWrapped, runSearchLoop, runSearchNext, hstep, hout, hb, start'] using hSearch
              exact IH hvalid' hSearch'
          ·
            have : False := by
              simp [runSearchWrapped, runSearchLoop, runSearchNext, hstep, hout] at hSearch
            exact False.elim this

lemma loopResult_gives_wrappedNonHalting
    {bound : Nat} {m : TickingMachine BM} {cache : TickCache m}
    {loopWitness : {L : List (Tick BM) //
      L ++ L <:+ cache.history.reverse ∧ ∃ q, (q, (⊥ : TickSymbol BM)) ∈ L}}
    (hSearch : runSearchWrapped bound m = .loops cache loopWitness) :
    ¬TM.Model.halts m (default : TickingConfig BM) := by
  exact loopResult_gives_nonHalting_fromDefault (TickCache.initial_valid m) hSearch

@[specialize bound]
def runSearch (bound : Nat) (m : BM) :
    SearchResult (TM.Wrappers.Ticking.wrap m) :=
  runSearchWrapped bound (TM.Wrappers.Ticking.wrap m)

@[specialize bound]
def translatedCyclerDecider (bound : Nat) (m : BM) : TM.Model.HaltM m Unit :=
  let wm := TM.Wrappers.Ticking.wrap m
  match hSearch : runSearchWrapped bound wm with
  | .timeout _ => .unknown ()
  | .halts cache =>
      let hWrapped := haltsResult_gives_wrappedHalts (TickCache.initial_valid wm) hSearch
      let hBase := TM.Wrappers.Ticking.halts_of_wrapped_halts (m := m) hWrapped
      .halts_prf cache.baseSteps (TM.Wrappers.Ticking.forgetConfig cache.cfg) hBase
  | .loops cache loopWitness =>
      .loops_prf (by
        intro hBase
        have hWrapped : TM.Model.halts wm (default : TickingConfig BM) :=
          TM.Wrappers.Ticking.wrapped_halts_of_halts (m := m) hBase
        exact loopResult_gives_wrappedNonHalting hSearch hWrapped)

end Deciders.TranslatedCyclers
