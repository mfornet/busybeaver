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
  rcases hs : TM.Model.step m A with ⟨dn, outcome⟩
  cases outcome <;> simp [TStep, TM.Model.Step, stepTick, hs] at h ⊢
  exact h.1

lemma to_multistep {m : TickingMachine BM} (h : A t-[m:L]->>' B) : A -[m]{L.length}->' B := by
  induction h with
  | refl => exact .refl
  | step A B C t L hAB hBC IH => exact .step (single_step hAB) IH

lemma to_multistepBase {m : TickingMachine BM} (h : A t-[m:L]->>' B) : ∃ n, A -[m]{n}->>' B :=
  TM.Model.Multistep.to_base (to_multistep h)

lemma trans {m : TickingMachine BM} (hAB : A t-[m:L]->>' B) (hBC : B t-[m:L']->>' C) :
    A t-[m:L ++ L']->>' C := by
  induction hAB with
  | refl => simpa using hBC
  | step A B D t L hAB hBD IH => exact .step A B C t _ hAB (IH hBC)

lemma split {m : TickingMachine BM} (h : A t-[m:L ++ L']->>' B) :
    ∃ C, (A t-[m:L]->>' C) ∧ (C t-[m:L']->>' B) := by
  induction L generalizing A with
  | nil => exact ⟨A, .refl A, by simpa using h⟩
  | cons t L IH =>
      cases h with
      | step A B C _ L'' hAB hBC =>
          obtain ⟨C, hAC, hCB⟩ := IH hBC
          exact ⟨C, .step A B C t L hAB hAC, hCB⟩

end TReach

end Deciders.TranslatedCyclers
