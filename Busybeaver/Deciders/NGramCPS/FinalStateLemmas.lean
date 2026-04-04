import Busybeaver.Deciders.NGramCPS.FixpointLemmas

open TM

namespace NGramCPS

/--
The initial blank partial configuration remains present in the final closed search
state.

Why this is correct:
- `initialState cfg` contains exactly this partial configuration;
- the search only adds to `partialConfigs`, it never removes entries.

Proof outline:
- prove `runSearch` preserves membership of existing `partialConfigs`;
- specialize that preservation theorem to the initial partial configuration.

Proof complexity:
- medium; purely algorithmic, depending only on monotonicity of the search loops.
-/
lemma initial_partial_mem_of_closedResult (cfg : NGramCPSConfig) {finalState : SearchState l s}
    (hSearch : runSearch M cfg.bound (initialState cfg) = .closed finalState) :
    {
      left := Array.replicate cfg.n default,
      head := default,
      state := default,
      right := Array.replicate cfg.n default
    } ∈ finalState.partialConfigs := by
  exact runSearch_closed_preserves_partialConfig_mem (l := l) (s := s) (M := M) cfg hSearch
    (initial_partial_mem (l := l) (s := s) cfg)

/--
The blank left `n`-gram remains present in the final closed search state.

Why this is correct:
- `initialState cfg` contains the blank `n`-gram in `leftNGrams`;
- the search only adds to `leftNGrams`, it never removes entries.

Proof outline:
- prove `runSearch` preserves membership of existing `leftNGrams`;
- specialize to `Array.replicate cfg.n default`.

Proof complexity:
- medium; purely algorithmic and parallel to the partial-config preservation proof.
-/
lemma blank_left_mem_of_closedResult (cfg : NGramCPSConfig) {finalState : SearchState l s}
    (hSearch : runSearch M cfg.bound (initialState cfg) = .closed finalState) :
    Array.replicate cfg.n default ∈ finalState.leftNGrams := by
  exact runSearch_closed_preserves_leftNGram_mem (l := l) (s := s) (M := M) cfg hSearch
    (blank_left_mem_initial (l := l) (s := s) cfg)

/--
The blank right `n`-gram remains present in the final closed search state.

Why this is correct:
- `initialState cfg` contains the blank `n`-gram in `rightNGrams`;
- the search only adds to `rightNGrams`, it never removes entries.

Proof outline:
- prove `runSearch` preserves membership of existing `rightNGrams`;
- specialize to `Array.replicate cfg.n default`.

Proof complexity:
- medium; purely algorithmic and parallel to the left-side version.
-/
lemma blank_right_mem_of_closedResult (cfg : NGramCPSConfig) {finalState : SearchState l s}
    (hSearch : runSearch M cfg.bound (initialState cfg) = .closed finalState) :
    Array.replicate cfg.n default ∈ finalState.rightNGrams := by
  exact runSearch_closed_preserves_rightNGram_mem (l := l) (s := s) (M := M) cfg hSearch
    (blank_right_mem_initial (l := l) (s := s) cfg)

/--
Any stored partial configuration is already closed under one `stepPartialConfig`
in the final search state.

Why this is correct:
- the last successful round of the search re-expands all known partial
  configurations under the final `leftNGrams` and `rightNGrams`;
- because the result is `.closed finalState`, that last pass found no halting edge
  and no genuinely new `n`-grams or partial configurations.

Proof outline:
- extract the final successful `runRound` from `runSearch`;
- show every `pc ∈ finalState.partialConfigs` is processed in that final round;
- read back the corresponding `Expansion` and prove all emitted data is already in
  the final arrays.

Proof complexity:
- high; this is the main algorithmic fixpoint theorem and depends on the inner/outer
  loop structure of `runRound` and `runSearch`.
-/
lemma partialConfig_fixpoint_of_closedResult (cfg : NGramCPSConfig) {finalState : SearchState l s}
    (hSearch : runSearch M cfg.bound (initialState cfg) = .closed finalState)
    {pc : PartialConfig l s} (hpc : pc ∈ finalState.partialConfigs) :
    ∃ expansion,
      stepPartialConfig M finalState.leftNGrams finalState.rightNGrams pc = .advanced expansion ∧
      (∀ ng ∈ expansion.leftNGrams, ng ∈ finalState.leftNGrams) ∧
      (∀ ng ∈ expansion.rightNGrams, ng ∈ finalState.rightNGrams) ∧
      (∀ pc' ∈ expansion.successors, pc' ∈ finalState.partialConfigs) := by
  obtain ⟨remaining, state, hRound, hfrontier⟩ :=
    runSearch_closed_extract_finalRound (l := l) (s := s) (M := M) cfg hSearch
  exact runRound_closed_fixpoint_of_fullFrontier (l := l) (s := s) (M := M) hRound hfrontier hpc

end NGramCPS
