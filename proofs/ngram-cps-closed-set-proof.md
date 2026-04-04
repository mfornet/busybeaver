# NGramCPS Closed-Set Proof Roadmap

## Goal

Replace the `NGramCPS` `.loops_prf (by sorry)` in [Busybeaver/Deciders/NGramCPS.lean](/Users/mnaeraxr/Documents/projects/busy-beaver-research/busybeaver/Busybeaver/Deciders/NGramCPS.lean) with a proof through [Busybeaver/ClosedSet.lean](/Users/mnaeraxr/Documents/projects/busy-beaver-research/busybeaver/Busybeaver/ClosedSet.lean).

Chosen shape:
- `SearchResult.closed` should carry the final `SearchState`.
- The proof should build `ClosedSet M (Base finalState) init`.
- The final `loops_prf` should be obtained by `ClosedSet.nonHalting` or the `closed_set` tactic.

What this proof is trying to establish:
- a successful `NGramCPS` search computes a finite certificate,
- that certificate induces a predicate on full `Config`s,
- the blank initial configuration enters that predicate,
- the predicate is closed under progress,
- therefore the machine cannot halt from `init`.

What this proof is not trying to establish:
- that every stored `PartialConfig` is reachable from `init`,
- that the search is complete in any stronger semantic sense than what `ClosedSet` needs,
- any algorithmic strengthening beyond the current search.

## High-Level Strategy

The proof should treat the final search object as a finite closed-set witness generator.

The core idea is:
- `runSearch` finishes with `.closed finalState`.
- `finalState` contains:
  - all currently known left `n`-grams,
  - all currently known right `n`-grams,
  - all currently known `PartialConfig`s.
- From this data, define a predicate `Base finalState : Config l s → Prop`.
- Show that `Base finalState` is a `ClosedSet` predicate.

The key conceptual move is that `Base finalState` must talk about:
- one visible local witness `PartialConfig`,
- and all side windows of the full tape, not just the currently visible one.

Reason:
- when stepping, `expandLeft` and `expandRight` need one fresh far symbol outside the visible window,
- that symbol is justified by a side `n`-gram already present in `leftNGrams` or `rightNGrams`,
- so the proof needs a global invariant saying all side windows of the configuration are already covered by the final `n`-gram sets.

This avoids the wrong proof target:
- it is not enough to say “the visible window matches some stored `PartialConfig`”.
- closure would fail because the next fresh far symbol comes from a shifted side window.

## Proof Objects To Introduce

### `SearchResult.closed` carrying `SearchState`

Suggested shape:
- `SearchResult.closed : SearchState l s → SearchResult`

Meaning:
- a successful search returns the final certificate object explicitly.

Why needed:
- the `loops_prf` proof must refer to the actual final `SearchState`.
- recomputing or reconstructing it after success would make the proof brittle.

Depends on:
- `SearchState`
- `runRound`
- `runSearch`

### Suggested helper: visible/offset window extractors

Suggested definitions:
- `leftWindowAt (n : ℕ) (k : ℕ) (C : Config l s) : NGram s`
- `rightWindowAt (n : ℕ) (k : ℕ) (C : Config l s) : NGram s`

Intended meaning:
- `leftWindowAt n k C` is the length-`n` left-side window starting at distance `k` from the head, stored in the same head-facing convention as `PartialConfig.left`.
- `rightWindowAt n k C` is the analogous right-side window.

Why needed:
- the proof needs a precise bridge from full tapes to the `NGram` objects manipulated by the search.
- these definitions are the common vocabulary for semantic lemmas and closure proofs.

Depends on:
- `Turing.Tape`
- likely helper lemmas from [Busybeaver/TuringExt.lean](/Users/mnaeraxr/Documents/projects/busy-beaver-research/busybeaver/Busybeaver/TuringExt.lean)

### Suggested helper: `MatchesPartial`

Suggested shape:
- `MatchesPartial (pc : PartialConfig l s) (C : Config l s) : Prop`

Intended meaning:
- `pc` is exactly the visible centered window of `C`.

Likely fields:
- `pc.state = C.state`
- `pc.head = C.tape.head`
- `pc.left = leftWindowAt n 0 C`
- `pc.right = rightWindowAt n 0 C`

Why needed:
- it isolates the local correspondence between a full configuration and a stored partial witness.

Depends on:
- `PartialConfig`
- window extractors

### Suggested helper: `AllLeftWindowsIn`

Suggested shape:
- `AllLeftWindowsIn (ngrams : Array (NGram s)) (C : Config l s) : Prop`

Intended meaning:
- every length-`n` left-side window of `C` is in `ngrams`.

Why needed:
- when stepping left/right, older windows shift and a new visible side window must already be justified by global side coverage.

Depends on:
- `leftWindowAt`

### Suggested helper: `AllRightWindowsIn`

Suggested shape:
- `AllRightWindowsIn (ngrams : Array (NGram s)) (C : Config l s) : Prop`

Intended meaning:
- every length-`n` right-side window of `C` is in `ngrams`.

Why needed:
- symmetric role to `AllLeftWindowsIn`.

Depends on:
- `rightWindowAt`

### Suggested helper: `Base finalState`

Suggested shape:
- `Base (finalState : SearchState l s) (C : Config l s) : Prop`

Intended meaning:
- `C` is represented by the final search object strongly enough for closure under one real machine step.

Likely components:
- `∃ pc, pc ∈ finalState.partialConfigs ∧ MatchesPartial pc C`
- `AllLeftWindowsIn finalState.leftNGrams C`
- `AllRightWindowsIn finalState.rightNGrams C`

Why needed:
- this is the predicate supplied to `ClosedSet`.

Depends on:
- `SearchState`
- `MatchesPartial`
- `AllLeftWindowsIn`
- `AllRightWindowsIn`

## Main Theorems

### `closedResult_gives_closedSet`

Statement shape:
- if `runSearch M cfg.bound (initialState cfg) = .closed finalState`, then `ClosedSet M (Base finalState) init`

Dependencies:
- `enters_of_closed_result`
- `closed_of_closed_result`

Likely proof method:
- constructor for `ClosedSet`
- reuse the two dedicated theorems below

Proof idea:
- this packages the full proof interface expected by `ClosedSet.nonHalting`.
- it should be the theorem consumed directly in the final `loops_prf`.

### `enters_of_closed_result`

Statement shape:
- if `runSearch ... = .closed finalState`, then `∃ N : {C // Base finalState C}, init -[M]->* N`

Dependencies:
- initial-state membership lemmas
- blank-window lemmas

Likely proof method:
- choose `init`
- prove `Base finalState init`
- use reflexivity for the multistep

Proof idea:
- the blank partial configuration and blank left/right `n`-grams are present in the initial state and remain present forever.
- every left/right window of the blank tape is the blank `n`-gram.

### `closed_of_closed_result`

Statement shape:
- if `runSearch ... = .closed finalState`, then
  `∀ A : {C // Base finalState C}, ∃ B : {C // Base finalState C}, A -[M]->+ B`

Dependencies:
- final-state fixpoint theorem
- tape-window transition lemmas
- local expansion correctness lemmas

Likely proof method:
- unpack `A`
- case split on `M.get A.state A.tape.head`
- show `.halt` is impossible
- in `.next writeSym dir nextState`, construct the real successor config and prove it lies in `Base finalState`

Proof idea:
- the visible window gives a stored `PartialConfig`.
- the final-state fixpoint theorem says this partial config has already been expanded successfully with no missing successors.
- the global side-window invariants justify the fresh far symbol chosen by `matchingLastSymbols`.

### Final theorem used in the decider

Statement shape:
- from `runSearch ... = .closed finalState`, derive `¬ M.halts init`

Dependencies:
- `closedResult_gives_closedSet`
- `ClosedSet.nonHalting`

Likely proof method:
- directly apply `ClosedSet.nonHalting`

Proof idea:
- once the `ClosedSet` instance exists, the rest should be one line.

## Lemma Clusters

### 1. Search monotonicity lemmas

Purpose:
- show search never removes previously discovered data.

Sublemmas:

#### `insertIfNew_mem_preserved`

Statement shape:
- if `x ∈ as`, then `x ∈ insertIfNew as a`

Dependencies:
- array membership simplification

Likely proof method:
- case split on `a ∈ as`

What it buys:
- base monotonicity for all search collections.

#### `insertAllIfNew_mem_preserved`

Statement shape:
- if `x ∈ base`, then `x ∈ insertAllIfNew base extra`

Dependencies:
- `insertIfNew_mem_preserved`

Likely proof method:
- induction/fold over `extra`

What it buys:
- persistence of earlier n-grams/configs across rounds.

#### `runRound_preserves_existing_membership`

Statement shape:
- anything present in the input `SearchState` remains present in the output state of `runRound` when it returns `restart` or `closed`

Dependencies:
- insert lemmas
- `addSuccessors`

Likely proof method:
- induction on the recursion of `runRound`

What it buys:
- lets `enters` import initial blank data into the final state.

#### `runSearch_preserves_initial_membership`

Statement shape:
- blank left/right `n`-grams and the initial `PartialConfig` are in the final state of a `.closed`

Dependencies:
- `runRound_preserves_existing_membership`
- recursion of `runSearchOuter`

Likely proof method:
- induction on outer recursion

What it buys:
- direct setup for `Base finalState init`.

### 2. Final-state / fixpoint lemmas

Purpose:
- capture exactly what “search returned `.closed finalState`” means operationally.

Sublemmas:

#### `closed_result_no_halting_partial`

Statement shape:
- if `runSearch ... = .closed finalState` and `pc ∈ finalState.partialConfigs`, then `stepPartialConfig M finalState.leftNGrams finalState.rightNGrams pc ≠ .haltingEdge`

Dependencies:
- `runRound`
- final closed round semantics

Likely proof method:
- derive contradiction with the last successful round

What it buys:
- rules out the impossible halting branch in `ClosedSet.closed`.

#### `closed_result_successors_already_present`

Statement shape:
- if `runSearch ... = .closed finalState` and
  `stepPartialConfig ... pc = .advanced expansion` with `pc ∈ finalState.partialConfigs`,
  then:
  - every `ng ∈ expansion.leftNGrams` is in `finalState.leftNGrams`,
  - every `ng ∈ expansion.rightNGrams` is in `finalState.rightNGrams`,
  - every `pc' ∈ expansion.successors` is in `finalState.partialConfigs`

Dependencies:
- final round restart-free closure

Likely proof method:
- prove from the last `runRound` ending in `.closed`

What it buys:
- exact bridge from algorithmic expansion to proof closure.

#### `closed_result_is_fixpoint`

Statement shape:
- packaged theorem combining `closed_result_no_halting_partial` and `closed_result_successors_already_present`

Dependencies:
- previous two lemmas

Likely proof method:
- theorem packaging only

What it buys:
- one reusable statement for the main `ClosedSet.closed` proof.

### 3. Tape-window extraction lemmas

Purpose:
- connect full tape semantics with the head-facing `NGram` representation.

Sublemmas:

#### `blank_leftWindowAt`

Statement shape:
- for `init`, every `leftWindowAt n k init = Array.replicate n default`

Dependencies:
- blank tape lemmas from `TuringExt`

Likely proof method:
- extensionality on the extracted list/array

What it buys:
- one half of `Base finalState init`.

#### `blank_rightWindowAt`

Statement shape:
- for `init`, every `rightWindowAt n k init = Array.replicate n default`

Dependencies:
- same as above

Likely proof method:
- same

What it buys:
- other half of `Base finalState init`.

#### `matchesPartial_visible_windows`

Statement shape:
- if `MatchesPartial pc C`, then `pc.left/right/head/state` agree with the visible centered window of `C`

Dependencies:
- definition unfolding

Likely proof method:
- trivial by simp/unfold

What it buys:
- standard unpacking lemma used throughout.

#### `step_right_visible_window`

Statement shape:
- if `C' = { state := nextState, tape := C.tape.write writeSym |>.move .right }`,
  then the visible left/head/right data of `C'` is exactly what `expandRight` expects:
  - left becomes `shiftInNear writeSym (leftWindowAt n 0 C)`
  - head becomes the nearest symbol of the old right side
  - right visible prefix becomes the old right window minus its first symbol

Dependencies:
- tape move/write lemmas
- window extractor definitions

Likely proof method:
- `simp [Turing.Tape.write, Turing.Tape.move]`
- tape extensionality or `nth` reasoning

What it buys:
- semantic correctness of the local right-step shape.

#### `step_left_visible_window`

Statement shape:
- mirror of `step_right_visible_window`

Dependencies:
- symmetric tape lemmas

Likely proof method:
- same

What it buys:
- semantic correctness of the local left-step shape.

#### `step_right_shifted_windows`

Statement shape:
- after a real right move, every left/right offset window of the successor is either:
  - the newly emitted/justified one at offset `0`, or
  - an old window from the predecessor at offset `k` or `k+1`

Dependencies:
- window extractor definitions
- move/write lemmas

Likely proof method:
- case analysis on offset

What it buys:
- propagation of `AllLeftWindowsIn` / `AllRightWindowsIn`.

#### `step_left_shifted_windows`

Statement shape:
- mirror of `step_right_shifted_windows`

Dependencies:
- same

Likely proof method:
- same

What it buys:
- symmetric propagation lemma.

### 4. Local expansion correctness lemmas

Purpose:
- show the real machine successor corresponds to one of the successors emitted by `expandLeft` / `expandRight`.

Sublemmas:

#### `actual_right_extension_is_matched`

Statement shape:
- if the actual far-right side `n`-gram of `C` belongs to `rightNGrams`,
  then its final symbol belongs to `matchingLastSymbols (visiblePrefix) rightNGrams default`

Dependencies:
- matching membership lemma
- prefix equality of the actual shifted right window

Likely proof method:
- exhibit the actual right `n`-gram as a witness inside `rightNGrams`

What it buys:
- existence of the concrete successor partial config for a right move.

#### `actual_left_extension_is_matched`

Statement shape:
- left-side mirror of the previous lemma

Dependencies:
- same

Likely proof method:
- same

What it buys:
- existence of the concrete successor partial config for a left move.

#### `expandRight_contains_real_successor`

Statement shape:
- if `pc` matches `C`, and the actual far-right extension is in `rightNGrams`,
  then `expandRight rightNGrams pc writeSym nextState` contains a successor `pc'` matching the real successor config

Dependencies:
- `step_right_visible_window`
- `actual_right_extension_is_matched`

Likely proof method:
- construct `pc'`
- prove it appears in `successors`

What it buys:
- the local witness needed for `Base finalState` after a right step.

#### `expandLeft_contains_real_successor`

Statement shape:
- mirror of `expandRight_contains_real_successor`

Dependencies:
- symmetric lemmas

Likely proof method:
- same

What it buys:
- local witness after a left step.

### 5. Matching / enumeration lemmas

Purpose:
- make `matchingLastSymbols` usable in proofs without repeatedly unfolding array combinators.

Sublemmas:

#### `matchingLastSymbols_mem`

Statement shape:
- if `ng ∈ ngrams` and `ng.take prefix.size = prefix`, then `ng.getD prefix.size fallback ∈ matchingLastSymbols prefix ngrams fallback`

Dependencies:
- behavior of `Array.filterMap`

Likely proof method:
- unfold once, then prove membership in `filterMap`

What it buys:
- one reusable theorem for both move directions.

#### `expandRight_emits_newLeft`

Statement shape:
- `shiftInNear writeSym pc.left ∈ (expandRight ...).leftNGrams`

Dependencies:
- definition of `expandRight`

Likely proof method:
- simp

What it buys:
- offset `0` part of the left-window invariant after a right move.

#### `expandLeft_emits_newRight`

Statement shape:
- `shiftInNear writeSym pc.right ∈ (expandLeft ...).rightNGrams`

Dependencies:
- definition of `expandLeft`

Likely proof method:
- simp

What it buys:
- offset `0` part of the right-window invariant after a left move.

## Closure Proof Walkthrough

The target is:
- for any `A : {C // Base finalState C}`, produce `B : {C // Base finalState C}` with `A -[M]->+ B`.

Unpack `A.prop` into:
- a visible witness `pc ∈ finalState.partialConfigs`,
- `MatchesPartial pc A`,
- `AllLeftWindowsIn finalState.leftNGrams A`,
- `AllRightWindowsIn finalState.rightNGrams A`.

Then case split on `M.get A.state A.tape.head`.

### Halting branch

Goal:
- show this cannot happen.

Argument:
- by `MatchesPartial`, `pc.state = A.state` and `pc.head = A.tape.head`,
- so `stepPartialConfig M finalState.leftNGrams finalState.rightNGrams pc = .haltingEdge`,
- but `pc ∈ finalState.partialConfigs`,
- this contradicts `closed_result_no_halting_partial`.

This branch should end in contradiction before needing to construct `B`.

### Move-right branch

Suppose:
- `M.get A.state A.tape.head = .next writeSym .right nextState`

Choose the real successor:
- `Bcfg := { state := nextState, tape := A.tape.write writeSym |>.move .right }`

Need to prove:
- `A -[M]->+ Bcfg`
- `Base finalState Bcfg`

#### Step relation

Use:
- `Machine.Progress` from the one-step semantics,
- likely via `Reachability.some`/`some'` or direct simplification of `Machine.step`.

#### Visible partial witness for `Bcfg`

Need:
- some `pc' ∈ finalState.partialConfigs` with `MatchesPartial pc' Bcfg`

Route:
- from `MatchesPartial pc A`, compute the visible update expected by `expandRight`,
- from `AllRightWindowsIn ... A`, the actual shifted right-side `n`-gram at offset `1` is in `finalState.rightNGrams`,
- by `actual_right_extension_is_matched`, the actual far symbol is enumerated by `matchingLastSymbols`,
- by `expandRight_contains_real_successor`, the corresponding `pc'` is in `expansion.successors`,
- by `closed_result_successors_already_present`, `pc' ∈ finalState.partialConfigs`.

#### Left-window invariant for `Bcfg`

Need:
- `AllLeftWindowsIn finalState.leftNGrams Bcfg`

Split by offset:
- offset `0` is the newly visible left `n`-gram, exactly emitted by `expandRight`,
- offsets `k+1` are inherited from old left-side windows of `A`.

Route:
- use `expandRight_emits_newLeft`,
- then use `closed_result_successors_already_present`,
- use `step_right_shifted_windows` for the inherited offsets,
- then discharge inherited membership from `AllLeftWindowsIn ... A`.

#### Right-window invariant for `Bcfg`

Need:
- `AllRightWindowsIn finalState.rightNGrams Bcfg`

Split by offset:
- offset `0` is the actual right-side `n`-gram used to justify the far symbol; it was already in `finalState.rightNGrams` by assumption on `A`,
- offsets `k+1` come from older right windows of `A`.

Route:
- use the global right-window assumption on `A`,
- then use `step_right_shifted_windows`.

### Move-left branch

This is the mirror image:
- choose `Bcfg := { state := nextState, tape := A.tape.write writeSym |>.move .left }`
- use `AllLeftWindowsIn ... A` to justify the fresh far-left symbol,
- use `expandLeft_contains_real_successor`,
- propagate `AllRightWindowsIn` with the newly emitted right `n`-gram,
- propagate `AllLeftWindowsIn` by shifted old windows.

The proof script should follow the same template as the right branch to keep symmetry obvious.

## Entry Proof Walkthrough

Target:
- `∃ N : {C // Base finalState C}, init -[M]->* N`

Take:
- `N := ⟨init, hBaseInit⟩`

Then:
- the reachability proof is `Machine.Multistep.refl`.

So the real work is `hBaseInit : Base finalState init`.

That breaks into three parts.

### Visible witness part

Need:
- some `pc ∈ finalState.partialConfigs` matching `init`

Use:
- the initial `PartialConfig` in `initialState cfg`
- a monotonicity theorem showing it remains in the final state

Then prove `MatchesPartial pc init` by unfolding:
- state is `default`
- head is `default`
- left visible window is all blanks
- right visible window is all blanks

### Left-window coverage

Need:
- every left-side window of `init` belongs to `finalState.leftNGrams`

Use:
- every left window of the blank tape is the blank `n`-gram,
- the blank `n`-gram is present initially and preserved by search.

### Right-window coverage

Same argument as the left side.

## Dependency Graph / Suggested Order Of Formalization

Recommended order:

1. Adjust `SearchResult.closed` to carry `SearchState`.
2. Introduce proof predicates:
   - suggested helper window extractors,
   - `MatchesPartial`,
   - `AllLeftWindowsIn`,
   - `AllRightWindowsIn`,
   - `Base`.
3. Prove basic array membership lemmas:
   - `insertIfNew`
   - `insertAllIfNew`
   - `addSuccessors`
4. Prove search monotonicity:
   - data is never removed,
   - initial blank data survives to the final state.
5. Prove the final-state fixpoint theorem:
   - no halting partial config remains,
   - all emitted data from final expansions is already present.
6. Prove tape/window extraction lemmas on `Config` and `Turing.Tape`.
7. Prove local expansion correctness:
   - actual machine successor corresponds to one emitted successor partial config.
8. Prove `enters`.
9. Prove `closed`.
10. Package into `ClosedSet` and replace the `sorry`.

Why this order minimizes churn:
- the algorithmic lemmas do not depend on tape semantics,
- the semantic window lemmas do not depend on `ClosedSet`,
- the final `ClosedSet` proof then becomes mostly assembly rather than exploration.

## Known Hard Parts / Risks

### Head-facing window extraction from `Turing.Tape`

Risk:
- the tape stores left/right in different underlying directions than the proof wants.

Expected friction:
- getting the extracted `NGram` convention to line up exactly with `PartialConfig.left` and `PartialConfig.right`.

Mitigation:
- define window extractors once and prove extensional lemmas against them early.

### Relating actual far symbols to `matchingLastSymbols`

Risk:
- the proof needs to show that the one concrete far symbol from the real tape is among the candidates returned by `matchingLastSymbols`.

Expected friction:
- array `filterMap` membership reasoning.

Mitigation:
- isolate one clean `matchingLastSymbols_mem` lemma and never unfold the combinator in higher-level proofs.

### Array membership proofs becoming ugly

Risk:
- direct equality proofs on arrays are likely to be brittle.

Mitigation:
- phrase almost all theorems as membership lemmas `x ∈ arr`,
- keep equality proofs only for local semantic lemmas where unavoidable.

### Accidentally proving too much reachability

Risk:
- it is tempting to try to show every stored `PartialConfig` is reachable from `init`.

Why to avoid it:
- `ClosedSet` does not need that theorem,
- it will likely cause unnecessary proof work and proof fragility.

### Interleaving semantic and algorithmic lemmas too early

Risk:
- trying to prove the whole `ClosedSet.closed` theorem before the fixpoint theorem and window lemmas exist.

Mitigation:
- keep the clusters separate until both are stable.

## Out Of Scope For This Proof Pass

Do not fold these into the proof effort:
- performance refactors,
- replacing `Array` with `Vector`,
- changing the search algorithm,
- strengthening the decider beyond the current `.closed` / `.haltingEdge` / `.timeout` behavior,
- proving extra reachability or completeness claims not needed by `ClosedSet`.

The only acceptable mentions of these topics in the Lean work are:
- as blockers,
- as TODOs,
- or as reasons to keep statements membership-based rather than overly dependent on concrete data structures.

## Minimal End-To-End Proof Skeleton

This is pseudocode Lean, not intended to compile as written.

```lean
def nGramCPSDecider (cfg : NGramCPSConfig) (M : Machine l s) : HaltM M Unit :=
  if cfg.n = 0 then
    .unknown ()
  else
    match runSearch M cfg.bound (initialState cfg) with
    | .closed finalState =>
        .loops_prf (by
          have hClosedSet : ClosedSet M (Base finalState) init :=
            closedResult_gives_closedSet (M := M) (cfg := cfg) ?hSearch
          exact hClosedSet.nonHalting
        )
    | .haltingEdge => .unknown ()
    | .timeout => .unknown ()
```

Alternative proof style:

```lean
| .closed finalState =>
    .loops_prf (by
      closed_set (Base finalState)
      · exact closed_of_closed_result ...
      · exact enters_of_closed_result ...
    )
```

The first style is likely easier to maintain once the helper theorems exist.

