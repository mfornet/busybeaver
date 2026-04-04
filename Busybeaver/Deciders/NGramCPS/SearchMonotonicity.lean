import Busybeaver.Deciders.NGramCPS.SearchLemmas

open TM

namespace NGramCPS

/--
`insertAllIfNew` never removes elements already present in its base array.

Why this is correct:
- `insertAllIfNew` is a fold of `insertIfNew`;
- `insertIfNew` either keeps the array unchanged or appends one new element.

Proof outline:
- induct on the list of extra elements;
- use `mem_insertIfNew_of_mem` at the induction step.

Proof complexity:
- low; this only depends on the local behavior of `insertIfNew`.
-/
lemma mem_insertAllIfNew_of_mem [DecidableEq α] {base extra : Array α} {x : α}
    (hx : x ∈ base) :
    x ∈ insertAllIfNew base extra := by
  unfold insertAllIfNew
  induction extra.toList generalizing base with
  | nil =>
      simpa
  | cons a rest IH =>
      simpa using
        IH (base := insertIfNew base a) (mem_insertIfNew_of_mem hx)

/--
`addSuccessors` never removes a partial configuration that was already known.

Why this is correct:
- each fold step either leaves the accumulator unchanged or pushes one new
  successor onto the known array;
- neither branch removes existing entries.

Proof outline:
- induct on the successor list processed by `addSuccessors`;
- in the non-membership branch, use membership in `Array.push`.

Proof complexity:
- low; purely local to the `addSuccessors` fold.
-/
lemma mem_addSuccessors_known_of_mem {known : Array (PartialConfig l s)}
    {frontier : List (PartialConfig l s)} {successors : Array (PartialConfig l s)}
    {x : PartialConfig l s} (hx : x ∈ known) :
    x ∈ (addSuccessors known frontier successors).1 := by
  unfold addSuccessors
  induction successors.toList generalizing known frontier with
  | nil =>
      simpa
  | cons cfg rest IH =>
      by_cases hcfg : cfg ∈ known
      · simpa [hcfg] using IH (known := known) (frontier := frontier) hx
      · have hx' : x ∈ known.push cfg := by
          simp [Array.mem_push, hx]
        simpa [hcfg] using
          IH (known := known.push cfg) (frontier := cfg :: frontier) hx'

/--
`addSuccessors` never removes an element already present in the frontier list.

Why this is correct:
- the frontier component of `addSuccessors` only prepends new successors;
- existing frontier entries are kept in both branches of the fold step.

Proof outline:
- induct on the successor list processed by `addSuccessors`;
- in the non-membership branch, lift membership through list `cons`.

Proof complexity:
- low; purely local to the `addSuccessors` fold.
-/
lemma mem_addSuccessors_frontier_of_mem {known : Array (PartialConfig l s)}
    {frontier : List (PartialConfig l s)} {successors : Array (PartialConfig l s)}
    {x : PartialConfig l s} (hx : x ∈ frontier) :
    x ∈ (addSuccessors known frontier successors).2 := by
  unfold addSuccessors
  induction successors.toList generalizing known frontier with
  | nil =>
      simpa
  | cons cfg rest IH =>
      by_cases hcfg : cfg ∈ known
      · simpa [hcfg] using IH (known := known) (frontier := frontier) hx
      · have hx' : x ∈ (cfg :: frontier) := by simp [hx]
        simpa [hcfg] using
          IH (known := known.push cfg) (frontier := cfg :: frontier) hx'

/--
If a `runRound` call closes successfully, any partial configuration already
present in the input state remains present in the final state.

Why this is correct:
- every step of `runRound` updates `partialConfigs` through `addSuccessors`;
- `addSuccessors` only inserts new configurations and never removes existing ones.

Proof outline:
- induct over the recursive structure of `runRound`;
- use `mem_addSuccessors_known_of_mem` at the expansion step.

Proof complexity:
- medium; the only real difficulty is following the control flow of `runRound`.
-/
lemma runRound_closed_preserves_partialConfig_mem
    {bound : ℕ} {state finalState : SearchState l s} {changed : Bool}
    {pc : PartialConfig l s}
    (hRound : runRound M bound state changed = .closed finalState)
    (hpc : pc ∈ state.partialConfigs) :
    pc ∈ finalState.partialConfigs := by
  induction bound generalizing state changed finalState with
  | zero =>
      cases hfrontier : state.frontier with
      | nil =>
          cases hchanged : changed with
          | false =>
              simp [runRound, hfrontier, hchanged] at hRound
              cases hRound
              exact hpc
          | true =>
              simp [runRound, hfrontier, hchanged] at hRound
      | cons hd tl =>
          simp [runRound, hfrontier] at hRound
  | succ bound IH =>
      cases hfrontier : state.frontier with
      | nil =>
          cases hchanged : changed with
          | false =>
              simp [runRound, hfrontier, hchanged] at hRound
              cases hRound
              exact hpc
          | true =>
              simp [runRound, hfrontier, hchanged] at hRound
      | cons hd tl =>
          unfold runRound at hRound
          rw [hfrontier] at hRound
          cases hstep : stepPartialConfig M state.leftNGrams state.rightNGrams hd with
          | haltingEdge =>
              simp [hstep] at hRound
          | advanced expansion =>
              set nextLeft := insertAllIfNew state.leftNGrams expansion.leftNGrams with hnextLeft
              set nextRight := insertAllIfNew state.rightNGrams expansion.rightNGrams with hnextRight
              set nextConfigs := (addSuccessors state.partialConfigs tl expansion.successors).1 with hnextConfigs
              set nextFrontier := (addSuccessors state.partialConfigs tl expansion.successors).2 with hnextFrontier
              set changed' :=
                changed ||
                nextLeft.size ≠ state.leftNGrams.size ||
                nextRight.size ≠ state.rightNGrams.size with hchanged'
              let nextState : SearchState l s := {
                leftNGrams := nextLeft
                rightNGrams := nextRight
                partialConfigs := nextConfigs
                frontier := nextFrontier
              }
              have hpc' : pc ∈ nextState.partialConfigs := by
                dsimp [nextState]
                simpa [nextConfigs] using mem_addSuccessors_known_of_mem (known := state.partialConfigs)
                  (frontier := tl) (successors := expansion.successors) hpc
              have hRound' : runRound M bound nextState changed' = .closed finalState := by
                simpa [nextLeft, nextRight, nextConfigs, nextFrontier, changed', nextState, hstep]
                  using hRound
              exact IH hRound' hpc'

/--
If a `runRound` call closes successfully, any left `n`-gram already present in
the input state remains present in the final state.

Why this is correct:
- every step updates `leftNGrams` via `insertAllIfNew`;
- `insertAllIfNew` never removes existing elements.

Proof outline:
- induct over the recursive structure of `runRound`;
- use `mem_insertAllIfNew_of_mem` whenever the left side is updated.

Proof complexity:
- medium; structurally parallel to the partial-config preservation theorem.
-/
lemma runRound_closed_preserves_leftNGram_mem
    {bound : ℕ} {state finalState : SearchState l s} {changed : Bool}
    {ng : NGram s}
    (hRound : runRound M bound state changed = .closed finalState)
    (hng : ng ∈ state.leftNGrams) :
    ng ∈ finalState.leftNGrams := by
  induction bound generalizing state changed finalState with
  | zero =>
      cases hfrontier : state.frontier with
      | nil =>
          cases hchanged : changed with
          | false =>
              simp [runRound, hfrontier, hchanged] at hRound
              cases hRound
              exact hng
          | true =>
              simp [runRound, hfrontier, hchanged] at hRound
      | cons hd tl =>
          simp [runRound, hfrontier] at hRound
  | succ bound IH =>
      cases hfrontier : state.frontier with
      | nil =>
          cases hchanged : changed with
          | false =>
              simp [runRound, hfrontier, hchanged] at hRound
              cases hRound
              exact hng
          | true =>
              simp [runRound, hfrontier, hchanged] at hRound
      | cons hd tl =>
          unfold runRound at hRound
          rw [hfrontier] at hRound
          cases hstep : stepPartialConfig M state.leftNGrams state.rightNGrams hd with
          | haltingEdge =>
              simp [hstep] at hRound
          | advanced expansion =>
              set nextLeft := insertAllIfNew state.leftNGrams expansion.leftNGrams with hnextLeft
              set nextRight := insertAllIfNew state.rightNGrams expansion.rightNGrams with hnextRight
              set nextConfigs := (addSuccessors state.partialConfigs tl expansion.successors).1 with hnextConfigs
              set nextFrontier := (addSuccessors state.partialConfigs tl expansion.successors).2 with hnextFrontier
              set changed' :=
                changed ||
                nextLeft.size ≠ state.leftNGrams.size ||
                nextRight.size ≠ state.rightNGrams.size with hchanged'
              let nextState : SearchState l s := {
                leftNGrams := nextLeft
                rightNGrams := nextRight
                partialConfigs := nextConfigs
                frontier := nextFrontier
              }
              have hng' : ng ∈ nextState.leftNGrams := by
                dsimp [nextState]
                simpa [nextLeft] using mem_insertAllIfNew_of_mem (base := state.leftNGrams)
                  (extra := expansion.leftNGrams) hng
              have hRound' : runRound M bound nextState changed' = .closed finalState := by
                simpa [nextLeft, nextRight, nextConfigs, nextFrontier, changed', nextState, hstep]
                  using hRound
              exact IH hRound' hng'

/--
If a `runRound` call closes successfully, any right `n`-gram already present in
the input state remains present in the final state.

Why this is correct:
- every step updates `rightNGrams` via `insertAllIfNew`;
- `insertAllIfNew` never removes existing elements.

Proof outline:
- induct over the recursive structure of `runRound`;
- use `mem_insertAllIfNew_of_mem` whenever the right side is updated.

Proof complexity:
- medium; structurally parallel to the left-side theorem.
-/
lemma runRound_closed_preserves_rightNGram_mem
    {bound : ℕ} {state finalState : SearchState l s} {changed : Bool}
    {ng : NGram s}
    (hRound : runRound M bound state changed = .closed finalState)
    (hng : ng ∈ state.rightNGrams) :
    ng ∈ finalState.rightNGrams := by
  induction bound generalizing state changed finalState with
  | zero =>
      cases hfrontier : state.frontier with
      | nil =>
          cases hchanged : changed with
          | false =>
              simp [runRound, hfrontier, hchanged] at hRound
              cases hRound
              exact hng
          | true =>
              simp [runRound, hfrontier, hchanged] at hRound
      | cons hd tl =>
          simp [runRound, hfrontier] at hRound
  | succ bound IH =>
      cases hfrontier : state.frontier with
      | nil =>
          cases hchanged : changed with
          | false =>
              simp [runRound, hfrontier, hchanged] at hRound
              cases hRound
              exact hng
          | true =>
              simp [runRound, hfrontier, hchanged] at hRound
      | cons hd tl =>
          unfold runRound at hRound
          rw [hfrontier] at hRound
          cases hstep : stepPartialConfig M state.leftNGrams state.rightNGrams hd with
          | haltingEdge =>
              simp [hstep] at hRound
          | advanced expansion =>
              set nextLeft := insertAllIfNew state.leftNGrams expansion.leftNGrams with hnextLeft
              set nextRight := insertAllIfNew state.rightNGrams expansion.rightNGrams with hnextRight
              set nextConfigs := (addSuccessors state.partialConfigs tl expansion.successors).1 with hnextConfigs
              set nextFrontier := (addSuccessors state.partialConfigs tl expansion.successors).2 with hnextFrontier
              set changed' :=
                changed ||
                nextLeft.size ≠ state.leftNGrams.size ||
                nextRight.size ≠ state.rightNGrams.size with hchanged'
              let nextState : SearchState l s := {
                leftNGrams := nextLeft
                rightNGrams := nextRight
                partialConfigs := nextConfigs
                frontier := nextFrontier
              }
              have hng' : ng ∈ nextState.rightNGrams := by
                dsimp [nextState]
                simpa [nextRight] using mem_insertAllIfNew_of_mem (base := state.rightNGrams)
                  (extra := expansion.rightNGrams) hng
              have hRound' : runRound M bound nextState changed' = .closed finalState := by
                simpa [nextLeft, nextRight, nextConfigs, nextFrontier, changed', nextState, hstep]
                  using hRound
              exact IH hRound' hng'

/--
If a `runRound` call restarts, any partial configuration already present in the
input state remains present in the restart state.

Why this is correct:
- a restart round is still built out of the same `addSuccessors` updates as a
  closed round;
- those updates only add to `partialConfigs`.

Proof outline:
- follow the recursive structure of `runRound`;
- use `mem_addSuccessors_known_of_mem` in the expansion step.

Proof complexity:
- medium; parallel to the closed-result preservation theorem.
-/
lemma runRound_restart_preserves_partialConfig_mem
    {bound remaining : ℕ} {state restartState : SearchState l s} {changed : Bool}
    {pc : PartialConfig l s}
    (hRound : runRound M bound state changed = .restart remaining restartState)
    (hpc : pc ∈ state.partialConfigs) :
    pc ∈ restartState.partialConfigs := by
  induction bound generalizing state changed remaining restartState with
  | zero =>
      cases hfrontier : state.frontier with
      | nil =>
          cases hchanged : changed with
          | false =>
              simp [runRound, hfrontier, hchanged] at hRound
          | true =>
              simp [runRound, hfrontier, hchanged] at hRound
              rcases hRound with ⟨rfl, rfl⟩
              exact hpc
      | cons hd tl =>
          simp [runRound, hfrontier] at hRound
  | succ bound IH =>
      cases hfrontier : state.frontier with
      | nil =>
          cases hchanged : changed with
          | false =>
              simp [runRound, hfrontier, hchanged] at hRound
          | true =>
              simp [runRound, hfrontier, hchanged] at hRound
              rcases hRound with ⟨rfl, rfl⟩
              exact hpc
      | cons hd tl =>
          unfold runRound at hRound
          rw [hfrontier] at hRound
          cases hstep : stepPartialConfig M state.leftNGrams state.rightNGrams hd with
          | haltingEdge =>
              simp [hstep] at hRound
          | advanced expansion =>
              set nextLeft := insertAllIfNew state.leftNGrams expansion.leftNGrams with hnextLeft
              set nextRight := insertAllIfNew state.rightNGrams expansion.rightNGrams with hnextRight
              set nextConfigs := (addSuccessors state.partialConfigs tl expansion.successors).1 with hnextConfigs
              set nextFrontier := (addSuccessors state.partialConfigs tl expansion.successors).2 with hnextFrontier
              set changed' :=
                changed ||
                nextLeft.size ≠ state.leftNGrams.size ||
                nextRight.size ≠ state.rightNGrams.size with hchanged'
              let nextState : SearchState l s := {
                leftNGrams := nextLeft
                rightNGrams := nextRight
                partialConfigs := nextConfigs
                frontier := nextFrontier
              }
              have hpc' : pc ∈ nextState.partialConfigs := by
                dsimp [nextState]
                simpa [nextConfigs] using mem_addSuccessors_known_of_mem (known := state.partialConfigs)
                  (frontier := tl) (successors := expansion.successors) hpc
              have hRound' : runRound M bound nextState changed' = .restart remaining restartState := by
                simpa [nextLeft, nextRight, nextConfigs, nextFrontier, changed', nextState, hstep]
                  using hRound
              exact IH hRound' hpc'

/--
If a `runRound` call restarts, any left `n`-gram already present in the input
state remains present in the restart state.

Why this is correct:
- restart rounds update `leftNGrams` only via `insertAllIfNew`;
- those updates never remove existing elements.

Proof outline:
- follow the recursive structure of `runRound`;
- use `mem_insertAllIfNew_of_mem` whenever the left side is updated.

Proof complexity:
- medium; parallel to the closed-result left-side preservation theorem.
-/
lemma runRound_restart_preserves_leftNGram_mem
    {bound remaining : ℕ} {state restartState : SearchState l s} {changed : Bool}
    {ng : NGram s}
    (hRound : runRound M bound state changed = .restart remaining restartState)
    (hng : ng ∈ state.leftNGrams) :
    ng ∈ restartState.leftNGrams := by
  induction bound generalizing state changed remaining restartState with
  | zero =>
      cases hfrontier : state.frontier with
      | nil =>
          cases hchanged : changed with
          | false =>
              simp [runRound, hfrontier, hchanged] at hRound
          | true =>
              simp [runRound, hfrontier, hchanged] at hRound
              rcases hRound with ⟨rfl, rfl⟩
              exact hng
      | cons hd tl =>
          simp [runRound, hfrontier] at hRound
  | succ bound IH =>
      cases hfrontier : state.frontier with
      | nil =>
          cases hchanged : changed with
          | false =>
              simp [runRound, hfrontier, hchanged] at hRound
          | true =>
              simp [runRound, hfrontier, hchanged] at hRound
              rcases hRound with ⟨rfl, rfl⟩
              exact hng
      | cons hd tl =>
          unfold runRound at hRound
          rw [hfrontier] at hRound
          cases hstep : stepPartialConfig M state.leftNGrams state.rightNGrams hd with
          | haltingEdge =>
              simp [hstep] at hRound
          | advanced expansion =>
              set nextLeft := insertAllIfNew state.leftNGrams expansion.leftNGrams with hnextLeft
              set nextRight := insertAllIfNew state.rightNGrams expansion.rightNGrams with hnextRight
              set nextConfigs := (addSuccessors state.partialConfigs tl expansion.successors).1 with hnextConfigs
              set nextFrontier := (addSuccessors state.partialConfigs tl expansion.successors).2 with hnextFrontier
              set changed' :=
                changed ||
                nextLeft.size ≠ state.leftNGrams.size ||
                nextRight.size ≠ state.rightNGrams.size with hchanged'
              let nextState : SearchState l s := {
                leftNGrams := nextLeft
                rightNGrams := nextRight
                partialConfigs := nextConfigs
                frontier := nextFrontier
              }
              have hng' : ng ∈ nextState.leftNGrams := by
                dsimp [nextState]
                simpa [nextLeft] using mem_insertAllIfNew_of_mem (base := state.leftNGrams)
                  (extra := expansion.leftNGrams) hng
              have hRound' : runRound M bound nextState changed' = .restart remaining restartState := by
                simpa [nextLeft, nextRight, nextConfigs, nextFrontier, changed', nextState, hstep]
                  using hRound
              exact IH hRound' hng'

/--
If a `runRound` call restarts, any right `n`-gram already present in the input
state remains present in the restart state.

Why this is correct:
- restart rounds update `rightNGrams` only via `insertAllIfNew`;
- those updates never remove existing elements.

Proof outline:
- follow the recursive structure of `runRound`;
- use `mem_insertAllIfNew_of_mem` whenever the right side is updated.

Proof complexity:
- medium; parallel to the closed-result right-side preservation theorem.
-/
lemma runRound_restart_preserves_rightNGram_mem
    {bound remaining : ℕ} {state restartState : SearchState l s} {changed : Bool}
    {ng : NGram s}
    (hRound : runRound M bound state changed = .restart remaining restartState)
    (hng : ng ∈ state.rightNGrams) :
    ng ∈ restartState.rightNGrams := by
  induction bound generalizing state changed remaining restartState with
  | zero =>
      cases hfrontier : state.frontier with
      | nil =>
          cases hchanged : changed with
          | false =>
              simp [runRound, hfrontier, hchanged] at hRound
          | true =>
              simp [runRound, hfrontier, hchanged] at hRound
              rcases hRound with ⟨rfl, rfl⟩
              exact hng
      | cons hd tl =>
          simp [runRound, hfrontier] at hRound
  | succ bound IH =>
      cases hfrontier : state.frontier with
      | nil =>
          cases hchanged : changed with
          | false =>
              simp [runRound, hfrontier, hchanged] at hRound
          | true =>
              simp [runRound, hfrontier, hchanged] at hRound
              rcases hRound with ⟨rfl, rfl⟩
              exact hng
      | cons hd tl =>
          unfold runRound at hRound
          rw [hfrontier] at hRound
          cases hstep : stepPartialConfig M state.leftNGrams state.rightNGrams hd with
          | haltingEdge =>
              simp [hstep] at hRound
          | advanced expansion =>
              set nextLeft := insertAllIfNew state.leftNGrams expansion.leftNGrams with hnextLeft
              set nextRight := insertAllIfNew state.rightNGrams expansion.rightNGrams with hnextRight
              set nextConfigs := (addSuccessors state.partialConfigs tl expansion.successors).1 with hnextConfigs
              set nextFrontier := (addSuccessors state.partialConfigs tl expansion.successors).2 with hnextFrontier
              set changed' :=
                changed ||
                nextLeft.size ≠ state.leftNGrams.size ||
                nextRight.size ≠ state.rightNGrams.size with hchanged'
              let nextState : SearchState l s := {
                leftNGrams := nextLeft
                rightNGrams := nextRight
                partialConfigs := nextConfigs
                frontier := nextFrontier
              }
              have hng' : ng ∈ nextState.rightNGrams := by
                dsimp [nextState]
                simpa [nextRight] using mem_insertAllIfNew_of_mem (base := state.rightNGrams)
                  (extra := expansion.rightNGrams) hng
              have hRound' : runRound M bound nextState changed' = .restart remaining restartState := by
                simpa [nextLeft, nextRight, nextConfigs, nextFrontier, changed', nextState, hstep]
                  using hRound
              exact IH hRound' hng'

/--
Successful `runSearchOuter` preserves previously known partial configurations.

Why this is correct:
- `runSearchOuter` either returns the current round result directly or continues
  from a `.restart` state produced by `runRound`;
- every such restart state still contains all earlier known partial configurations.

Proof outline:
- induct over the outer-loop recursion;
- use `runRound_closed_preserves_partialConfig_mem` in the closed branch and the
  induction hypothesis in the restart branch.

Proof complexity:
- medium; this depends on the round-level preservation theorem and the control
  flow of the outer loop.
-/
lemma runSearchOuter_closed_preserves_partialConfig_mem
    {rounds remaining : ℕ} {state finalState : SearchState l s} {pc : PartialConfig l s}
    (hSearch : runSearchOuter M rounds remaining state = .closed finalState)
    (hpc : pc ∈ state.partialConfigs) :
    pc ∈ finalState.partialConfigs := by
  revert remaining state finalState hSearch hpc
  induction rounds with
  | zero =>
      intro remaining state finalState hSearch hpc
      simp [runSearchOuter] at hSearch
  | succ rounds IH =>
      intro remaining state finalState hSearch hpc
      unfold runSearchOuter at hSearch
      cases hRound : runRound M remaining state false with
      | closed roundState =>
          simp [hRound] at hSearch
          cases hSearch
          exact runRound_closed_preserves_partialConfig_mem (l := l) (s := s) (M := M) hRound hpc
      | haltingEdge =>
          simp [hRound] at hSearch
      | timeout =>
          simp [hRound] at hSearch
      | restart remaining' restartState =>
          simp [hRound] at hSearch
          exact IH (remaining := remaining') (state := restartState) (finalState := finalState) hSearch
            (runRound_restart_preserves_partialConfig_mem (l := l) (s := s) (M := M) hRound hpc)

/--
Successful `runSearchOuter` preserves previously known left `n`-grams.

Why this is correct:
- this is the outer-loop lift of `runRound_closed_preserves_leftNGram_mem`.

Proof outline:
- induct over the outer-loop recursion;
- use the round-level preservation theorem in the closed branch and the induction
  hypothesis across restart states.

Proof complexity:
- medium; parallel to the partial-config version.
-/
lemma runSearchOuter_closed_preserves_leftNGram_mem
    {rounds remaining : ℕ} {state finalState : SearchState l s} {ng : NGram s}
    (hSearch : runSearchOuter M rounds remaining state = .closed finalState)
    (hng : ng ∈ state.leftNGrams) :
    ng ∈ finalState.leftNGrams := by
  revert remaining state finalState hSearch hng
  induction rounds with
  | zero =>
      intro remaining state finalState hSearch hng
      simp [runSearchOuter] at hSearch
  | succ rounds IH =>
      intro remaining state finalState hSearch hng
      unfold runSearchOuter at hSearch
      cases hRound : runRound M remaining state false with
      | closed roundState =>
          simp [hRound] at hSearch
          cases hSearch
          exact runRound_closed_preserves_leftNGram_mem (l := l) (s := s) (M := M) hRound hng
      | haltingEdge =>
          simp [hRound] at hSearch
      | timeout =>
          simp [hRound] at hSearch
      | restart remaining' restartState =>
          simp [hRound] at hSearch
          exact IH (remaining := remaining') (state := restartState) (finalState := finalState) hSearch
            (runRound_restart_preserves_leftNGram_mem (l := l) (s := s) (M := M) hRound hng)

/--
Successful `runSearchOuter` preserves previously known right `n`-grams.

Why this is correct:
- this is the outer-loop lift of `runRound_closed_preserves_rightNGram_mem`.

Proof outline:
- induct over the outer-loop recursion;
- use the round-level preservation theorem in the closed branch and the induction
  hypothesis across restart states.

Proof complexity:
- medium; parallel to the left-side version.
-/
lemma runSearchOuter_closed_preserves_rightNGram_mem
    {rounds remaining : ℕ} {state finalState : SearchState l s} {ng : NGram s}
    (hSearch : runSearchOuter M rounds remaining state = .closed finalState)
    (hng : ng ∈ state.rightNGrams) :
    ng ∈ finalState.rightNGrams := by
  revert remaining state finalState hSearch hng
  induction rounds with
  | zero =>
      intro remaining state finalState hSearch hng
      simp [runSearchOuter] at hSearch
  | succ rounds IH =>
      intro remaining state finalState hSearch hng
      unfold runSearchOuter at hSearch
      cases hRound : runRound M remaining state false with
      | closed roundState =>
          simp [hRound] at hSearch
          cases hSearch
          exact runRound_closed_preserves_rightNGram_mem (l := l) (s := s) (M := M) hRound hng
      | haltingEdge =>
          simp [hRound] at hSearch
      | timeout =>
          simp [hRound] at hSearch
      | restart remaining' restartState =>
          simp [hRound] at hSearch
          exact IH (remaining := remaining') (state := restartState) (finalState := finalState) hSearch
            (runRound_restart_preserves_rightNGram_mem (l := l) (s := s) (M := M) hRound hng)

/--
Successful `runSearch` preserves previously known partial configurations.

Why this is correct:
- `runSearch` is just repeated `runRound` calls through `runSearchOuter`;
- each successful closed result is reached through states that only grow their
  known partial configurations.

Proof outline:
- prove the analogous theorem for `runSearchOuter`;
- specialize it to `runSearch`.

Proof complexity:
- medium; depends on the `runRound` preservation theorem and the outer-loop
  control flow.
-/
lemma runSearch_closed_preserves_partialConfig_mem
    (cfg : NGramCPSConfig) {finalState : SearchState l s} {pc : PartialConfig l s}
    (hSearch : runSearch M cfg.bound (initialState cfg) = .closed finalState)
    (hpc : pc ∈ (initialState (l := l) (s := s) cfg).partialConfigs) :
    pc ∈ finalState.partialConfigs := by
  exact runSearchOuter_closed_preserves_partialConfig_mem (l := l) (s := s) (M := M)
    (state := initialState cfg) (remaining := cfg.bound) hSearch hpc

/--
Successful `runSearch` preserves previously known left `n`-grams.

Why this is correct:
- this is the outer-loop lift of `runRound_closed_preserves_leftNGram_mem`.

Proof outline:
- follow the outer-loop recursion through `runSearchOuter`;
- use the round-level preservation theorem in the closed branch.

Proof complexity:
- medium; algorithmic and parallel to the partial-config version.
-/
lemma runSearch_closed_preserves_leftNGram_mem
    (cfg : NGramCPSConfig) {finalState : SearchState l s} {ng : NGram s}
    (hSearch : runSearch M cfg.bound (initialState cfg) = .closed finalState)
    (hng : ng ∈ (initialState (l := l) (s := s) cfg).leftNGrams) :
    ng ∈ finalState.leftNGrams := by
  exact runSearchOuter_closed_preserves_leftNGram_mem (l := l) (s := s) (M := M)
    (state := initialState cfg) (remaining := cfg.bound) hSearch hng

/--
Successful `runSearch` preserves previously known right `n`-grams.

Why this is correct:
- this is the outer-loop lift of `runRound_closed_preserves_rightNGram_mem`.

Proof outline:
- follow the outer-loop recursion through `runSearchOuter`;
- use the round-level preservation theorem in the closed branch.

Proof complexity:
- medium; algorithmic and parallel to the left-side theorem.
-/
lemma runSearch_closed_preserves_rightNGram_mem
    (cfg : NGramCPSConfig) {finalState : SearchState l s} {ng : NGram s}
    (hSearch : runSearch M cfg.bound (initialState cfg) = .closed finalState)
    (hng : ng ∈ (initialState (l := l) (s := s) cfg).rightNGrams) :
    ng ∈ finalState.rightNGrams := by
  exact runSearchOuter_closed_preserves_rightNGram_mem (l := l) (s := s) (M := M)
    (state := initialState cfg) (remaining := cfg.bound) hSearch hng

end NGramCPS
