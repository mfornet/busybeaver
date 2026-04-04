import Busybeaver.ClosedSet
import Busybeaver.Deciders.NGramCPS.SearchLemmas

open TM

namespace NGramCPS

/--
The initial configuration already lies in the base predicate of the initial search
state. This is the seed for the later `ClosedSet.enters` proof after the final-state
monotonicity lemmas are added.
-/
lemma initial_enters (cfg : NGramCPSConfig) :
    ∃ N : { C // Base cfg.n (initialState (l := l) (s := s) cfg) C }, (init : Config l s) -[M]->* N := by
  refine ⟨⟨init, initial_base (l := l) (s := s) cfg⟩, ?_⟩
  exact Machine.EvStep.refl

/--
Top-level proof entrypoint for `NGramCPS`.

Once the closure lemmas are in place, this theorem should turn a successful
search result into a `ClosedSet` certificate over full configurations.
-/
theorem closedResult_gives_closedSet (cfg : NGramCPSConfig) {finalState : SearchState l s}
    (hSearch : runSearch M cfg.bound (initialState cfg) = .closed finalState) :
    ClosedSet M (Base cfg.n finalState) (init : Config l s) := by
  sorry

end NGramCPS
