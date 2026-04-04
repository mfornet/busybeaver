import Busybeaver.ClosedSet
import Busybeaver.Deciders.NGramCPS.BaseProgress
import Busybeaver.Deciders.NGramCPS.FinalStateLemmas

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
The blank initial configuration still satisfies the final `Base` predicate after a
successful closed search.

Why this is correct:
- `init` already satisfies `Base` for the initial search state;
- a closed search result can only enlarge `partialConfigs`, `leftNGrams`, and
  `rightNGrams`, so the original witness for `init` remains valid.

Proof outline:
- start from `initial_base`;
- transport each membership fact from `initialState cfg` to `finalState` using
  monotonicity lemmas for `runSearch`.

Proof complexity:
- medium; this is the main dependency of `enters_of_closedResult`, and it only
  needs search monotonicity, not semantic step reasoning.
-/
lemma initial_in_final_base (cfg : NGramCPSConfig) {finalState : SearchState l s}
    (hSearch : runSearch M cfg.bound (initialState cfg) = .closed finalState) :
    Base cfg.n finalState (init : Config l s) := by
  constructor
  · refine ⟨{
        left := Array.replicate cfg.n default,
        head := default,
        state := default,
        right := Array.replicate cfg.n default
      }, initial_partial_mem_of_closedResult (l := l) (s := s) (M := M) cfg hSearch, ?_⟩
    exact initial_matches (l := l) (s := s) cfg
  constructor
  · intro k
    rw [blank_leftWindowAt]
    exact blank_left_mem_of_closedResult (l := l) (s := s) (M := M) cfg hSearch
  · intro k
    rw [blank_rightWindowAt]
    exact blank_right_mem_of_closedResult (l := l) (s := s) (M := M) cfg hSearch

/--
Any configuration in `Base cfg.n finalState` has a progressing successor still in
`Base cfg.n finalState`, provided the search finished with `.closed finalState`.

Why this is correct:
- the stored visible `PartialConfig` gives the local machine action;
- the global window side conditions provide the far symbol needed when stepping;
- the final closed search result guarantees that the corresponding successor
  partial configuration is already represented in the final certificate.

Proof outline:
- unpack the `Base` witness for the input configuration;
- use the final-state fixpoint theorem to choose a stored successor partial config;
- show the actual one-step machine successor satisfies the three pieces of `Base`.

Proof complexity:
- high; this is the core closure lemma and depends on both the algorithmic
  fixpoint results and the tape-window transition lemmas.
-/
lemma base_progress_of_closedResult (cfg : NGramCPSConfig) {finalState : SearchState l s}
    (hcfg : cfg.n ≠ 0)
    (hSearch : runSearch M cfg.bound (initialState cfg) = .closed finalState) :
    ∀ A : { C // Base cfg.n finalState C }, ∃ B : { C // Base cfg.n finalState C }, A -[M]->+ B := by
  intro A
  rcases A.property with ⟨⟨pc, hpc, hmatch⟩, hleft, hright⟩
  obtain ⟨expansion, hstep, hleftExp, hrightExp, hsuccExp⟩ :=
    partialConfig_fixpoint_of_closedResult (l := l) (s := s) (M := M) cfg hSearch hpc
  cases hstmt : M.get A.1.state A.1.tape.head with
  | halt =>
      have hstmt' : M.get pc.state pc.head = .halt := by
        simpa [MatchesPartial_state hmatch, MatchesPartial_head hmatch] using hstmt
      simp [stepPartialConfig, hstmt'] at hstep
  | next writeSym dir nextState =>
      cases dir with
      | right =>
          exact base_successor_of_rightStep_of_fixpoint (l := l) (s := s) (M := M) cfg
            hcfg hmatch hleft hright ⟨expansion, hstep, hleftExp, hrightExp, hsuccExp⟩
            (by simpa using hstmt)
      | left =>
          exact base_successor_of_leftStep_of_fixpoint (l := l) (s := s) (M := M) cfg
            hcfg hmatch hleft hright ⟨expansion, hstep, hleftExp, hrightExp, hsuccExp⟩
            (by simpa using hstmt)

/--
If `runSearch` returns `.closed finalState`, then the blank initial configuration
must enter `Base cfg.n finalState`.

Why this is correct:
- `initialState cfg` already satisfies `Base cfg.n` at `init`.
- successful search only grows the certificate; it never removes the blank
  `n`-grams or the initial partial configuration.

Proof outline:
- lift `initial_base` from `initialState cfg` to `finalState` using monotonicity
  of `runSearch` on `partialConfigs`, `leftNGrams`, and `rightNGrams`.

Proof complexity:
- medium; this depends on the search-monotonicity lemmas but not on the semantic
  step-closure part.
-/
lemma enters_of_closedResult (cfg : NGramCPSConfig) {finalState : SearchState l s}
    (hSearch : runSearch M cfg.bound (initialState cfg) = .closed finalState) :
    ∃ N : { C // Base cfg.n finalState C }, (init : Config l s) -[M]->* N := by
  refine ⟨⟨init, initial_in_final_base (l := l) (s := s) (M := M) cfg hSearch⟩, ?_⟩
  exact Machine.EvStep.refl

/--
If `runSearch` returns `.closed finalState`, then `Base cfg.n finalState` is
closed under progressing machine steps.

Why this is correct:
- a `Base` witness gives one stored visible `PartialConfig` plus global coverage
  of all left/right side windows by the final `n`-gram sets;
- the final closed search result means every stored `PartialConfig` was expanded
  successfully under the final certificate with no halting edge.

Proof outline:
- unpack `A : { C // Base cfg.n finalState C }`;
- rule out the halting case using the final-state fixpoint theorem;
- in the left/right step cases, use the matching stored expansion together with
  the side-window invariants to build a successor full configuration in `Base`.

Proof complexity:
- high; this is the main semantic theorem and depends on both the final-state
  fixpoint lemmas for `runRound`/`runSearch` and the tape-window transition lemmas.
-/
lemma closed_of_closedResult (cfg : NGramCPSConfig) {finalState : SearchState l s}
    (hcfg : cfg.n ≠ 0)
    (hSearch : runSearch M cfg.bound (initialState cfg) = .closed finalState) :
    ∀ A : { C // Base cfg.n finalState C }, ∃ B : { C // Base cfg.n finalState C }, A -[M]->+ B := by
  exact base_progress_of_closedResult (l := l) (s := s) (M := M) cfg hcfg hSearch

/--
Top-level proof entrypoint for `NGramCPS`.

Once the closure lemmas are in place, this theorem should turn a successful
search result into a `ClosedSet` certificate over full configurations.
-/
theorem closedResult_gives_closedSet (cfg : NGramCPSConfig) {finalState : SearchState l s}
    (hcfg : cfg.n ≠ 0)
    (hSearch : runSearch M cfg.bound (initialState cfg) = .closed finalState) :
    ClosedSet M (Base cfg.n finalState) (init : Config l s) := by
  refine ⟨closed_of_closedResult (l := l) (s := s) (M := M) cfg hcfg hSearch, ?_⟩
  exact enters_of_closedResult (l := l) (s := s) (M := M) cfg hSearch

end NGramCPS
