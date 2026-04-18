import Busybeaver.Deciders.TranslatedCyclers.Constraints
import Busybeaver.Deciders.TranslatedCyclers.Frontier

namespace Deciders.TranslatedCyclers

open TM.Model

variable {BM : Type _} [TM.Model BM]

/--
Each required start cell for the next copy is either overlap or genuinely fresh.

Depends on:
- transcript geometry for `startConstraint` and `finishConstraint`

Idea:
- compare the start-support with its `netShift`-translate;
- overlap cells stay inside the previously written region;
- cells that fall outside that region are the fresh fringe, and their required symbol is `⊥`.
-/
lemma start_offset_overlap_or_fresh
    {m : TickingMachine BM} {L : List (Tick BM)} {q : TM.Model.State BM}
    (hRecord : (q, (⊥ : TickSymbol BM)) ∈ L) :
    ∀ i s,
      startConstraint m L i = some s →
      startConstraint m L (i + netShift m L) = some s ∨
        (finishConstraint m L i = none ∧ s = (⊥ : TickSymbol BM)) := by
  /-
  Proof sketch:
  - reason on the transcript head walk rather than the recursive `merge` structure directly;
  - if the translated offset `i + netShift m L` is still in the start-support, we are in the
    overlap case;
  - otherwise `i` lies in the fresh fringe exposed by the translation, and the repeated transcript
    can only require `⊥` there because `hRecord` witnesses a frontier read in the period.
  -/
  sorry

/--
If a final offset was not determined by the previous run, its source cell in the middle
configuration is still `⊥`.

Depends on:
- `reachable_bot_suffix_left`
- `reachable_bot_suffix_right`

Idea:
- `finishConstraint m L i = none` means the second run never wrote the source cell that ends at
  final offset `i`;
- that source cell therefore lies in the untouched frontier of the reachable middle configuration.
-/
lemma fresh_current_cell_is_bot
    {m : TickingMachine BM} {B C : TickingConfig BM} {L : List (Tick BM)}
    {q : TM.Model.State BM} {n : Nat}
    (hReachB : (default : TickingConfig BM) -[m]{n}->>' B)
    (_hBC : B t-[m:L]->>' C)
    (_hRecord : (q, (⊥ : TickSymbol BM)) ∈ L) :
    ∀ i,
      finishConstraint m L i = none →
      B.tape.nth (i + netShift m L) = (⊥ : TickSymbol BM) := by
  /-
  Proof sketch:
  - split on the sign of `netShift m L`;
  - use the shape of `finishConstraint` to show that `i + netShift m L` lies beyond the written
    interval visited by the second copy;
  - apply the reachable ticking frontier invariant on the corresponding side.
  -/
  sorry

end Deciders.TranslatedCyclers
