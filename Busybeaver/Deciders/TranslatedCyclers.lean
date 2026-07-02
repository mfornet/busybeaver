/-
Translated cycler decider based on [transcripts](https://www.sligocki.com/2024/06/12/tm-transcripts.html).

The ticking behavior is implemented as a wrapper machine in `TM.Wrappers.Ticking`; the decider
itself only runs a search over that wrapped machine and then discharges the corresponding proof
obligations separately.
-/
import Busybeaver.Deciders.TranslatedCyclers.Looping

namespace Deciders.TranslatedCyclers

open TM.Model

variable {BM : Type _} [TM.Model BM]

inductive SearchResult : TickingMachine BM → Type _
  | timeout {m : TickingMachine BM} (cache : TickCache m) : SearchResult m
  | halts {m : TickingMachine BM} (cache : TickCache m) : SearchResult m
  | loops {m : TickingMachine BM} (cache : TickCache m)
      (loop : {L : List (Tick BM) //
        L ++ L <:+ cache.history.reverse ∧ ∃ q, (q, (⊥ : TickSymbol BM)) ∈ L}) :
      SearchResult m

/-- The loop witness produced from a detected front loop `Lh` over `history`, after prepending the
new tick `t` (whose written symbol is blank, `hb`). Shared by the executable search and its
correctness proof. -/
private lemma frontLoop_to_witness {t : Tick BM} {history : List (Tick BM)}
    (hb : t.2 = (⊥ : TickSymbol BM))
    (Lh : {L' : List (Tick BM) //
      L' ++ L' <+: ((t.1, (⊥ : TickSymbol BM)) :: history) ∧
        (t.1, (⊥ : TickSymbol BM)) ∈ L'}) :
    Lh.1.reverse ++ Lh.1.reverse <:+ (t :: history).reverse ∧
      ∃ q, (q, (⊥ : TickSymbol BM)) ∈ Lh.1.reverse := by
  obtain ⟨L, hL, hq⟩ := Lh
  refine ⟨?_, t.1, by simpa [List.mem_reverse] using hq⟩
  have ht : (t.1, (⊥ : TickSymbol BM)) = t := by
    cases t with
    | mk q b => simp at hb; cases hb; rfl
  conv_lhs => rw [← List.reverse_append]
  rw [List.reverse_suffix]
  simpa [ht] using hL

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
        | some Lh => .loops cache' ⟨Lh.1.reverse, frontLoop_to_witness hb Lh⟩
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
  | zero => simp [runSearchWrapped, runSearchLoop] at hSearch
  | succ bound IH =>
      cases hstep : stepTick m start.cfg with
      | mk dn outcome =>
          cases hout : outcome with
          | «continue» out =>
              obtain ⟨cfg, t⟩ := out
              have hstep' : stepTick m start.cfg = ⟨dn, .continue (cfg, t)⟩ := by rw [hstep, hout]
              let start' : TickCache m :=
                { cfg := cfg, history := t :: start.history, baseSteps := start.baseSteps + dn }
              have hvalid' : TickCache.Valid m start' := stepTick_continue_valid hvalid hstep'
              by_cases hb : t.2 = (⊥ : TickSymbol BM)
              · cases hdet : detectFrontLoop t.1 start.history with
                | some Lh =>
                    simp [runSearchWrapped, runSearchLoop, runSearchNext, hstep, hout, hb, hdet]
                      at hSearch
                | none =>
                    exact IH hvalid' (by
                      simpa [runSearchWrapped, runSearchLoop, runSearchNext, hstep, hout, hb, hdet,
                        start'] using hSearch)
              · exact IH hvalid' (by
                  simpa [runSearchWrapped, runSearchLoop, runSearchNext, hstep, hout, hb, start']
                    using hSearch)
          | halted out =>
              have hstep' : stepTick m start.cfg = ⟨dn, .halted out⟩ := by rw [hstep, hout]
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
  | zero => simp [runSearchWrapped, runSearchLoop] at hSearch
  | succ bound IH =>
      cases hstep : stepTick m start.cfg with
      | mk dn outcome =>
          cases hout : outcome with
          | «continue» out =>
              obtain ⟨cfg, t⟩ := out
              have hstep' : stepTick m start.cfg = ⟨dn, .continue (cfg, t)⟩ := by rw [hstep, hout]
              let start' : TickCache m :=
                { cfg := cfg, history := t :: start.history, baseSteps := start.baseSteps + dn }
              have hvalid' : TickCache.Valid m start' := stepTick_continue_valid hvalid hstep'
              by_cases hb : t.2 = (⊥ : TickSymbol BM)
              · cases hdet : detectFrontLoop t.1 start.history with
                | some Lh =>
                    have hEq : SearchResult.loops start' ⟨Lh.1.reverse, frontLoop_to_witness hb Lh⟩
                        = SearchResult.loops cache loopWitness := by
                      simpa [runSearchWrapped, runSearchLoop, runSearchNext, hstep, hout, hb, hdet,
                        start'] using hSearch
                    injection hEq with hcache
                    subst hcache
                    obtain ⟨q, hq⟩ := loopWitness.2.2
                    exact twice_suffix_loop hvalid'.transcript loopWitness.2.1 hq
                | none =>
                    exact IH hvalid' (by
                      simpa [runSearchWrapped, runSearchLoop, runSearchNext, hstep, hout, hb, hdet,
                        start'] using hSearch)
              · exact IH hvalid' (by
                  simpa [runSearchWrapped, runSearchLoop, runSearchNext, hstep, hout, hb, start']
                    using hSearch)
          | halted out =>
              simp [runSearchWrapped, runSearchLoop, runSearchNext, hstep, hout] at hSearch

lemma loopResult_gives_wrappedNonHalting
    {bound : Nat} {m : TickingMachine BM} {cache : TickCache m}
    {loopWitness : {L : List (Tick BM) //
      L ++ L <:+ cache.history.reverse ∧ ∃ q, (q, (⊥ : TickSymbol BM)) ∈ L}}
    (hSearch : runSearchWrapped bound m = .loops cache loopWitness) :
    ¬TM.Model.halts m (default : TickingConfig BM) :=
  loopResult_gives_nonHalting_fromDefault (TickCache.initial_valid m) hSearch

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
  | .loops _ _ =>
      .loops_prf fun hBase =>
        loopResult_gives_wrappedNonHalting hSearch
          (TM.Wrappers.Ticking.wrapped_halts_of_halts (m := m) hBase)

end Deciders.TranslatedCyclers
