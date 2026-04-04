import Busybeaver.Deciders.NGramCPS.SearchMonotonicity

open TM

namespace NGramCPS

/--
`insertIfNew` can only keep the array size unchanged or increase it by one.

Why this is correct:
- the existing-membership branch leaves the array unchanged;
- the new-element branch uses `Array.push`.

Proof outline:
- unfold `insertIfNew`;
- split on membership and simplify.

Proof complexity:
- low; purely local to `insertIfNew`.
-/
lemma size_le_insertIfNew [DecidableEq α] (as : Array α) (a : α) :
    as.size ≤ (insertIfNew as a).size := by
  unfold insertIfNew
  by_cases h : a ∈ as <;> simp [h]

/--
`insertAllIfNew` only grows the base array; it never removes entries.

Why this is correct:
- it is a fold of `insertIfNew`;
- each fold step is size-monotone.

Proof outline:
- unfold `insertAllIfNew`;
- induct over the folded list and compose `size_le_insertIfNew`.

Proof complexity:
- low-medium; structural on the fold.
-/
lemma size_le_insertAllIfNew [DecidableEq α] (base extra : Array α) :
    base.size ≤ (insertAllIfNew base extra).size := by
  unfold insertAllIfNew
  let xs := extra.toList
  change base.size ≤ (xs.foldl insertIfNew base).size
  clear_value xs
  induction xs generalizing base with
  | nil =>
      simp
  | cons a xs IH =>
      exact le_trans (size_le_insertIfNew base a) (IH (base := insertIfNew base a))

/--
If `insertIfNew` does not change the size, it was in the no-op branch.

Why this is correct:
- the only size-preserving branch is the existing-membership branch;
- the `push` branch increases the size by one.

Proof outline:
- unfold `insertIfNew`;
- split on membership and discharge the impossible `push` branch by arithmetic.

Proof complexity:
- low.
-/
lemma insertIfNew_eq_of_size_eq [DecidableEq α] {as : Array α} {a : α}
    (hsize : (insertIfNew as a).size = as.size) :
    insertIfNew as a = as := by
  unfold insertIfNew at hsize ⊢
  by_cases h : a ∈ as
  · simp [h]
  · simp [h] at hsize

/--
If `insertAllIfNew` preserves the size, every fold step was a no-op.

Why this is correct:
- `insertAllIfNew` is a fold of size-monotone `insertIfNew` steps;
- if the final size is unchanged, no step can have performed a `push`.

Proof outline:
- unfold the fold and induct on the extra list;
- use size monotonicity to show the first step also preserves size;
- reduce to `insertIfNew_eq_of_size_eq` and the induction hypothesis.

Proof complexity:
- medium; this is the core equality lemma used to freeze the final n-gram sets.
-/
lemma insertAllIfNew_eq_of_size_eq [DecidableEq α] {base extra : Array α}
    (hsize : (insertAllIfNew base extra).size = base.size) :
    insertAllIfNew base extra = base := by
  unfold insertAllIfNew at hsize ⊢
  let xs := extra.toList
  change (xs.foldl insertIfNew base).size = base.size at hsize
  change xs.foldl insertIfNew base = base at ⊢
  clear_value xs
  induction xs generalizing base with
  | nil =>
      simp
  | cons a xs IH =>
      simp only [List.foldl_cons] at hsize ⊢
      have hsize' : (xs.foldl insertIfNew (insertIfNew base a)).size = base.size := hsize
      have hle₁ : base.size ≤ (insertIfNew base a).size := size_le_insertIfNew base a
      have hle₂ : (insertIfNew base a).size ≤ (xs.foldl insertIfNew (insertIfNew base a)).size := by
        simpa [insertAllIfNew] using size_le_insertAllIfNew (insertIfNew base a) xs.toArray
      have hsize₁ : (insertIfNew base a).size = base.size := by omega
      have hsize₂ :
          (xs.foldl insertIfNew (insertIfNew base a)).size = (insertIfNew base a).size := by
        omega
      have hfirst : insertIfNew base a = base := insertIfNew_eq_of_size_eq hsize₁
      have hrest : xs.foldl insertIfNew (insertIfNew base a) = insertIfNew base a := by
        exact IH (base := insertIfNew base a) hsize₂
      simpa [insertAllIfNew, hfirst] using hrest

/--
Every element listed in `extra` ends up present in `insertAllIfNew base extra`.

Why this is correct:
- `insertAllIfNew` explicitly folds over the `extra` array and inserts each entry;
- later steps preserve everything already inserted.

Proof outline:
- unfold the fold over `extra.toList`;
- induct on that list;
- in the head case, insert the head and then use preservation on the remaining fold.

Proof complexity:
- medium; a direct fold-membership argument.
-/
lemma mem_insertAllIfNew_of_mem_extra [DecidableEq α] {base extra : Array α} {x : α}
    (hx : x ∈ extra) :
    x ∈ insertAllIfNew base extra := by
  unfold insertAllIfNew
  let xs := extra.toList
  have hx' : x ∈ xs := by
    simpa [xs] using hx
  change x ∈ xs.foldl insertIfNew base
  clear_value xs
  induction xs generalizing base with
  | nil =>
      cases hx'
  | cons a xs IH =>
      simp at hx'
      cases hx' with
      | inl hxa =>
          subst x
          have hmem : a ∈ insertIfNew base a := by
            unfold insertIfNew
            by_cases ha : a ∈ base <;> simp [ha]
          simpa [insertAllIfNew] using
            mem_insertAllIfNew_of_mem (base := insertIfNew base a) (extra := xs.toArray) hmem
      | inr hxrest =>
          exact IH (base := insertIfNew base a) hxrest

/--
Every current-step successor is present in the updated known-partial-config array.

Why this is correct:
- `addSuccessors` folds over `successors`;
- each successor is either already known or pushed into the known array.

Proof outline:
- unfold the fold over `successors.toList`;
- induct on the list and split on whether the head successor was already known.

Proof complexity:
- medium; local to `addSuccessors`.
-/
lemma mem_addSuccessors_known_of_mem_successor
    {known : Array (PartialConfig l s)} {frontier : List (PartialConfig l s)}
    {successors : Array (PartialConfig l s)} {x : PartialConfig l s}
    (hx : x ∈ successors) :
    x ∈ (addSuccessors known frontier successors).1 := by
  unfold addSuccessors
  let xs := successors.toList
  have hx' : x ∈ xs := by
    simpa [xs] using hx
  change x ∈
    (xs.foldl
      (fun acc cfg =>
        let (knownAcc, frontierAcc) := acc
        if cfg ∈ knownAcc then
          acc
        else
          (knownAcc.push cfg, cfg :: frontierAcc))
      (known, frontier)).1
  clear_value xs
  induction xs generalizing known frontier with
  | nil =>
      cases hx'
  | cons cfg xs IH =>
      simp at hx'
      by_cases hcfg : cfg ∈ known
      · simp [hcfg]
        cases hx' with
        | inl hxcfg =>
            subst x
            simpa [addSuccessors] using
              mem_addSuccessors_known_of_mem (l := l) (s := s)
                (known := known) (frontier := frontier) (successors := xs.toArray) hcfg
        | inr hxrest =>
            exact IH (known := known) (frontier := frontier) hxrest
      · simp [hcfg]
        cases hx' with
        | inl hxcfg =>
            subst x
            have hcfg' : cfg ∈ known.push cfg := by simp
            simpa [addSuccessors] using
              mem_addSuccessors_known_of_mem (l := l) (s := s)
                (known := known.push cfg) (frontier := cfg :: frontier) (successors := xs.toArray)
                hcfg'
        | inr hxrest =>
            exact IH (known := known.push cfg) (frontier := cfg :: frontier) hxrest

/--
Anything that was not previously known but appears in the updated known array is
also present in the updated frontier.

Why this is correct:
- `addSuccessors` adds genuinely new successors to both components at the same time;
- the only way to enter the known array without being known already is via that
  shared insertion path.

Proof outline:
- unfold the fold over `successors.toList`;
- induct on the list and split on whether the current head successor was already
  known;
- in the new-head branch, handle the head element directly and recurse on the
  tail for everything else.

Proof complexity:
- medium; this is the key bridge from “newly known” to “will be processed”.
-/
lemma mem_addSuccessors_frontier_of_not_mem_known_of_mem_knownResult
    {known : Array (PartialConfig l s)} {frontier : List (PartialConfig l s)}
    {successors : Array (PartialConfig l s)} {x : PartialConfig l s}
    (hxnot : x ∉ known)
    (hx : x ∈ (addSuccessors known frontier successors).1) :
    x ∈ (addSuccessors known frontier successors).2 := by
  unfold addSuccessors at hx ⊢
  let xs := successors.toList
  change x ∈
      (xs.foldl
        (fun acc cfg =>
          let (knownAcc, frontierAcc) := acc
          if cfg ∈ knownAcc then
            acc
          else
            (knownAcc.push cfg, cfg :: frontierAcc))
        (known, frontier)).1 at hx
  change x ∈
      (xs.foldl
        (fun acc cfg =>
          let (knownAcc, frontierAcc) := acc
          if cfg ∈ knownAcc then
            acc
          else
            (knownAcc.push cfg, cfg :: frontierAcc))
        (known, frontier)).2
  clear_value xs
  induction xs generalizing known frontier with
  | nil =>
      simpa using hxnot hx
  | cons cfg xs IH =>
      by_cases hcfg : cfg ∈ known
      · simp [hcfg] at hx ⊢
        exact IH (known := known) (frontier := frontier) hxnot hx
      · simp [hcfg] at hx ⊢
        by_cases hxcfg : x = cfg
        · subst x
          simpa [addSuccessors] using
            mem_addSuccessors_frontier_of_mem (l := l) (s := s)
              (known := known.push cfg) (frontier := cfg :: frontier) (successors := xs.toArray)
              (by simp)
        · have hxnot' : x ∉ known.push cfg := by
            simp [Array.mem_push, hxnot, hxcfg]
          exact IH (known := known.push cfg) (frontier := cfg :: frontier) hxnot' hx

/--
A `runRound` result can only be `.closed` if its `changed` flag is false.

Why this is correct:
- the empty-frontier branch returns `.restart` whenever `changed = true`;
- recursive branches only forward the recursive result, so the same restriction
  propagates inductively.

Proof outline:
- induct on the recursive structure of `runRound`;
- inspect the empty-frontier branch directly;
- in the recursive branch, apply the induction hypothesis to the recursive call.

Proof complexity:
- medium; structural on `runRound`.
-/
lemma runRound_closed_changed_false
    {remaining : ℕ} {state finalState : SearchState l s} {changed : Bool}
    (hRound : runRound M remaining state changed = .closed finalState) :
    changed = false := by
  induction remaining generalizing state changed finalState with
  | zero =>
      cases hfrontier : state.frontier with
      | nil =>
          cases hchanged : changed with
          | false =>
              rfl
          | true =>
              simp [runRound, hfrontier, hchanged] at hRound
      | cons hd tl =>
          simp [runRound, hfrontier] at hRound
  | succ remaining IH =>
      cases hfrontier : state.frontier with
      | nil =>
          cases hchanged : changed with
          | false =>
              rfl
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
              have hRound' : runRound M remaining nextState changed' = .closed finalState := by
                simpa [nextLeft, nextRight, nextConfigs, nextFrontier, changed', nextState, hstep]
                  using hRound
              have hchanged'False : changed' = false := IH hRound'
              cases changed with
              | false =>
                  rfl
              | true =>
                  simp [changed'] at hchanged'False

/--
Closed rounds do not change the left `n`-gram set.

Why this is correct:
- a closed round starting from `changed = false` can never encounter a genuine
  left-side insertion, otherwise `changed` would become true and the round would
  restart instead of closing.

Proof outline:
- induct over the recursive execution of `runRound`;
- use `runRound_closed_changed_false` on the recursive call to read back that the
  current `changed'` is false;
- convert the resulting size equality into `insertAllIfNew ... = ...`.

Proof complexity:
- medium-high; this packages the no-growth consequence of a closed round.
-/
lemma runRound_closed_leftNGrams_eq
    {remaining : ℕ} {state finalState : SearchState l s} {changed : Bool}
    (hRound : runRound M remaining state changed = .closed finalState) :
    state.leftNGrams = finalState.leftNGrams := by
  induction remaining generalizing state changed finalState with
  | zero =>
      cases hfrontier : state.frontier with
      | nil =>
          cases hchanged : changed with
          | false =>
              simp [runRound, hfrontier, hchanged] at hRound
              cases hRound
              rfl
          | true =>
              simp [runRound, hfrontier, hchanged] at hRound
      | cons hd tl =>
          simp [runRound, hfrontier] at hRound
  | succ remaining IH =>
      cases hfrontier : state.frontier with
      | nil =>
          cases hchanged : changed with
          | false =>
              simp [runRound, hfrontier, hchanged] at hRound
              cases hRound
              rfl
          | true =>
              simp [runRound, hfrontier, hchanged] at hRound
      | cons hd tl =>
          have hchangedFalse : changed = false :=
            runRound_closed_changed_false (l := l) (s := s) (M := M) hRound
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
              have hRound' : runRound M remaining nextState changed' = .closed finalState := by
                simpa [nextLeft, nextRight, nextConfigs, nextFrontier, changed', nextState, hstep]
                  using hRound
              have hstable :
                  nextLeft.size = state.leftNGrams.size ∧
                    nextRight.size = state.rightNGrams.size := by
                have hchanged'False : changed' = false :=
                  runRound_closed_changed_false (l := l) (s := s) (M := M) hRound'
                simpa [changed', hchangedFalse] using hchanged'False
              have hsize : nextLeft.size = state.leftNGrams.size := hstable.1
              have hnextLeft : nextLeft = state.leftNGrams :=
                insertAllIfNew_eq_of_size_eq hsize
              have hrec : nextLeft = finalState.leftNGrams := by
                simpa [nextState] using IH hRound'
              exact hnextLeft.symm.trans hrec

/--
Closed rounds do not change the right `n`-gram set.

Why this is correct:
- this is the right-side mirror of `runRound_closed_leftNGrams_eq`.

Proof outline:
- follow the same argument as for the left side, extracting from the closed
  recursive call that `changed' = false` and therefore no right insertion
  occurred.

Proof complexity:
- medium-high; symmetric to the left-side theorem.
-/
lemma runRound_closed_rightNGrams_eq
    {remaining : ℕ} {state finalState : SearchState l s} {changed : Bool}
    (hRound : runRound M remaining state changed = .closed finalState) :
    state.rightNGrams = finalState.rightNGrams := by
  induction remaining generalizing state changed finalState with
  | zero =>
      cases hfrontier : state.frontier with
      | nil =>
          cases hchanged : changed with
          | false =>
              simp [runRound, hfrontier, hchanged] at hRound
              cases hRound
              rfl
          | true =>
              simp [runRound, hfrontier, hchanged] at hRound
      | cons hd tl =>
          simp [runRound, hfrontier] at hRound
  | succ remaining IH =>
      cases hfrontier : state.frontier with
      | nil =>
          cases hchanged : changed with
          | false =>
              simp [runRound, hfrontier, hchanged] at hRound
              cases hRound
              rfl
          | true =>
              simp [runRound, hfrontier, hchanged] at hRound
      | cons hd tl =>
          have hchangedFalse : changed = false :=
            runRound_closed_changed_false (l := l) (s := s) (M := M) hRound
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
              have hRound' : runRound M remaining nextState changed' = .closed finalState := by
                simpa [nextLeft, nextRight, nextConfigs, nextFrontier, changed', nextState, hstep]
                  using hRound
              have hstable :
                  nextLeft.size = state.leftNGrams.size ∧
                    nextRight.size = state.rightNGrams.size := by
                have hchanged'False : changed' = false :=
                  runRound_closed_changed_false (l := l) (s := s) (M := M) hRound'
                simpa [changed', hchangedFalse] using hchanged'False
              have hsize : nextRight.size = state.rightNGrams.size := hstable.2
              have hnextRight : nextRight = state.rightNGrams :=
                insertAllIfNew_eq_of_size_eq hsize
              have hrec : nextRight = finalState.rightNGrams := by
                simpa [nextState] using IH hRound'
              exact hnextRight.symm.trans hrec

/--
Any restart state returned by `runRound` has its frontier reset to all known
partial configurations.

Why this is correct:
- the only place `runRound` constructs `.restart` explicitly is the empty-frontier
  case, where it sets `frontier := partialConfigs.toList`;
- in recursive branches, a restart result is simply forwarded from the recursive
  call, so the same property holds by induction.

Proof outline:
- induct on the recursive structure of `runRound`;
- check the empty-frontier branch directly;
- in the recursive expansion branch, apply the induction hypothesis to the
  recursive restart result.

Proof complexity:
- medium; purely structural on `runRound`.
-/
lemma runRound_restart_has_fullFrontier
    {bound remaining : ℕ} {state restartState : SearchState l s} {changed : Bool}
    (hRound : runRound M bound state changed = .restart remaining restartState) :
    restartState.frontier = restartState.partialConfigs.toList := by
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
              simp
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
              simp
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
              have hRound' : runRound M bound nextState changed' = .restart remaining restartState := by
                simpa [nextLeft, nextRight, nextConfigs, nextFrontier, changed', nextState, hstep]
                  using hRound
              exact IH hRound'

/--
Any successful closed `runSearch` result comes from a final `runRound` call whose
frontier initially contains all currently known partial configurations.

Why this is correct:
- `runSearch` delegates to `runSearchOuter`;
- every `.restart` branch resets the frontier to `partialConfigs.toList`;
- the initial state already satisfies `frontier = partialConfigs.toList`.

Proof outline:
- induct through the outer-loop recursion of `runSearchOuter`;
- in the direct closed branch, use the current round;
- in the restart branch, apply the induction hypothesis to the recursive call.

Proof complexity:
- medium; algorithmic, depending only on the structure of `runSearchOuter`.
-/
lemma runSearchOuter_closed_extract_finalRound
    {rounds remaining : ℕ} {state finalState : SearchState l s}
    (hfrontier : state.frontier = state.partialConfigs.toList)
    (hSearch : runSearchOuter M rounds remaining state = .closed finalState) :
    ∃ remaining' state',
      runRound M remaining' state' false = .closed finalState ∧
      state'.frontier = state'.partialConfigs.toList := by
  revert remaining state finalState hfrontier hSearch
  induction rounds with
  | zero =>
      intro remaining state finalState hfrontier hSearch
      simp [runSearchOuter] at hSearch
  | succ rounds IH =>
      intro remaining state finalState hfrontier hSearch
      unfold runSearchOuter at hSearch
      cases hRound : runRound M remaining state false with
      | closed roundState =>
          simp [hRound] at hSearch
          cases hSearch
          exact ⟨remaining, state, hRound, hfrontier⟩
      | haltingEdge =>
          simp [hRound] at hSearch
      | timeout =>
          simp [hRound] at hSearch
      | restart remaining' restartState =>
          simp [hRound] at hSearch
          exact IH (remaining := remaining') (state := restartState) (finalState := finalState)
            (runRound_restart_has_fullFrontier (l := l) (s := s) (M := M) hRound)
            hSearch

/--
Any successful closed `runSearch` result comes from a final `runRound` call whose
frontier initially contains all currently known partial configurations.

Why this is correct:
- this is just the specialization of the `runSearchOuter` extraction theorem to
  the initial search state;
- `initialState cfg` already satisfies `frontier = partialConfigs.toList`.

Proof outline:
- unfold `runSearch`;
- apply `runSearchOuter_closed_extract_finalRound` to `initialState cfg`.

Proof complexity:
- low; all the real work is in the outer-loop extraction theorem.
-/
lemma runSearch_closed_extract_finalRound (cfg : NGramCPSConfig) {finalState : SearchState l s}
    (hSearch : runSearch M cfg.bound (initialState cfg) = .closed finalState) :
    ∃ remaining state,
      runRound M remaining state false = .closed finalState ∧
      state.frontier = state.partialConfigs.toList := by
  exact runSearchOuter_closed_extract_finalRound (l := l) (s := s) (M := M)
    (state := initialState cfg) (remaining := cfg.bound)
    (by simp [initialState])
    hSearch

/--
A closed `runRound` processes every partial configuration that is either already
pending in the current frontier or will have to be added later as a genuinely
new successor.

Why this is correct:
- frontier elements are processed directly by the current pass;
- genuinely new successors are inserted into both `partialConfigs` and `frontier`,
  so they are forced to be processed before the round can close;
- closed rounds keep the final left/right `n`-gram sets fixed.

Proof outline:
- induct over the recursive execution of `runRound`;
- when the target configuration is the current frontier head, use the current
  `stepPartialConfig` result and monotonicity of the recursive tail;
- otherwise, push the obligation into the recursive call, using
  `addSuccessors` to show the target is either still pending or remains
  genuinely new there.

Proof complexity:
- high; this is the real inner-loop completeness theorem. The public
  full-frontier theorem below is just a corollary of it.
-/
lemma runRound_closed_fixpoint_of_frontier_or_new
    {remaining : ℕ} {state finalState : SearchState l s} {changed : Bool}
    (hRound : runRound M remaining state changed = .closed finalState)
    {pc : PartialConfig l s}
    (hpc : pc ∈ state.frontier ∨ (pc ∈ finalState.partialConfigs ∧ pc ∉ state.partialConfigs)) :
    ∃ expansion,
      stepPartialConfig M finalState.leftNGrams finalState.rightNGrams pc = .advanced expansion ∧
      (∀ ng ∈ expansion.leftNGrams, ng ∈ finalState.leftNGrams) ∧
      (∀ ng ∈ expansion.rightNGrams, ng ∈ finalState.rightNGrams) ∧
      (∀ pc' ∈ expansion.successors, pc' ∈ finalState.partialConfigs) := by
  induction remaining generalizing state changed finalState pc with
  | zero =>
      cases hfrontier : state.frontier with
      | nil =>
          cases hchanged : changed with
          | false =>
              simp [runRound, hfrontier, hchanged] at hRound
              cases hRound
              cases hpc with
              | inl hfront =>
                  exact False.elim (by simpa [hfrontier] using hfront)
              | inr hnew =>
                  exact False.elim (hnew.2 hnew.1)
          | true =>
              simp [runRound, hfrontier, hchanged] at hRound
      | cons hd tl =>
          simp [runRound, hfrontier] at hRound
  | succ remaining IH =>
      cases hfrontier : state.frontier with
      | nil =>
          cases hchanged : changed with
          | false =>
              simp [runRound, hfrontier, hchanged] at hRound
              cases hRound
              cases hpc with
              | inl hfront =>
                  exact False.elim (by simpa [hfrontier] using hfront)
              | inr hnew =>
                  exact False.elim (hnew.2 hnew.1)
          | true =>
              simp [runRound, hfrontier, hchanged] at hRound
      | cons hd tl =>
          have hleftEq : state.leftNGrams = finalState.leftNGrams :=
            runRound_closed_leftNGrams_eq (l := l) (s := s) (M := M) hRound
          have hrightEq : state.rightNGrams = finalState.rightNGrams :=
            runRound_closed_rightNGrams_eq (l := l) (s := s) (M := M) hRound
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
              have hRound' : runRound M remaining nextState changed' = .closed finalState := by
                simpa [nextLeft, nextRight, nextConfigs, nextFrontier, changed', nextState, hstep]
                  using hRound
              cases hpc with
              | inl hfront =>
                  have hfront' : pc = hd ∨ pc ∈ tl := by
                    simpa [hfrontier] using hfront
                  cases hfront' with
                  | inl hpc_hd =>
                      subst pc
                      refine ⟨expansion, ?_, ?_, ?_, ?_⟩
                      · simpa [hleftEq, hrightEq] using hstep
                      · intro ng hng
                        have hmemNext : ng ∈ nextState.leftNGrams := by
                          dsimp [nextState]
                          simpa [nextLeft] using
                            mem_insertAllIfNew_of_mem_extra (base := state.leftNGrams)
                              (extra := expansion.leftNGrams) hng
                        exact runRound_closed_preserves_leftNGram_mem
                          (l := l) (s := s) (M := M) hRound' hmemNext
                      · intro ng hng
                        have hmemNext : ng ∈ nextState.rightNGrams := by
                          dsimp [nextState]
                          simpa [nextRight] using
                            mem_insertAllIfNew_of_mem_extra (base := state.rightNGrams)
                              (extra := expansion.rightNGrams) hng
                        exact runRound_closed_preserves_rightNGram_mem
                          (l := l) (s := s) (M := M) hRound' hmemNext
                      · intro pc' hsucc
                        have hmemNext : pc' ∈ nextState.partialConfigs := by
                          dsimp [nextState]
                          simpa [nextConfigs] using
                            mem_addSuccessors_known_of_mem_successor (l := l) (s := s)
                              (known := state.partialConfigs) (frontier := tl)
                              (successors := expansion.successors) hsucc
                        exact runRound_closed_preserves_partialConfig_mem
                          (l := l) (s := s) (M := M) hRound' hmemNext
                  | inr hpc_tl =>
                      have hpcNext :
                          pc ∈ nextState.frontier ∨
                            (pc ∈ finalState.partialConfigs ∧ pc ∉ nextState.partialConfigs) := by
                        left
                        dsimp [nextState]
                        simpa [nextFrontier] using
                          mem_addSuccessors_frontier_of_mem (l := l) (s := s)
                            (known := state.partialConfigs) (frontier := tl)
                            (successors := expansion.successors) hpc_tl
                      exact IH hRound' hpcNext
              | inr hnew =>
                  by_cases hpcNext : pc ∈ nextState.partialConfigs
                  · have hpcFrontier : pc ∈ nextState.frontier := by
                      dsimp [nextState] at hpcNext ⊢
                      simpa [nextConfigs, nextFrontier] using
                        mem_addSuccessors_frontier_of_not_mem_known_of_mem_knownResult
                          (l := l) (s := s)
                          (known := state.partialConfigs) (frontier := tl)
                          (successors := expansion.successors) hnew.2
                          (by simpa [nextConfigs] using hpcNext)
                    exact IH hRound' (Or.inl hpcFrontier)
                  · exact IH hRound' (Or.inr ⟨hnew.1, hpcNext⟩)

/--
A closed `runRound` started from a state whose frontier is all known partial
configurations yields a genuine one-step fixpoint for every final partial
configuration.

Why this is correct:
- the round processes every configuration in the frontier;
- newly discovered successors are immediately enqueued and are therefore also
  processed before the round finishes;
- because the round returns `.closed`, no halting edge occurs and the left/right
  `n`-gram sets remain unchanged throughout the pass.

Proof outline:
- induct over the recursive execution of `runRound`;
- use the fact that `changed` stays `false` in a closed round to keep the final
  `n`-gram sets fixed;
- propagate the fixpoint property through `addSuccessors` and the recursive call.

Proof complexity:
- high; this is the main inner-loop completeness theorem.
-/
lemma runRound_closed_fixpoint_of_fullFrontier
    {remaining : ℕ} {state finalState : SearchState l s}
    (hRound : runRound M remaining state false = .closed finalState)
    (hfrontier : state.frontier = state.partialConfigs.toList)
    {pc : PartialConfig l s} (hpc : pc ∈ finalState.partialConfigs) :
    ∃ expansion,
      stepPartialConfig M finalState.leftNGrams finalState.rightNGrams pc = .advanced expansion ∧
      (∀ ng ∈ expansion.leftNGrams, ng ∈ finalState.leftNGrams) ∧
      (∀ ng ∈ expansion.rightNGrams, ng ∈ finalState.rightNGrams) ∧
      (∀ pc' ∈ expansion.successors, pc' ∈ finalState.partialConfigs) := by
  have hpc' :
      pc ∈ state.frontier ∨ (pc ∈ finalState.partialConfigs ∧ pc ∉ state.partialConfigs) := by
    by_cases hknown : pc ∈ state.partialConfigs
    · left
      rw [hfrontier]
      simpa using hknown
    · exact Or.inr ⟨hpc, hknown⟩
  exact runRound_closed_fixpoint_of_frontier_or_new (l := l) (s := s) (M := M) hRound hpc'

end NGramCPS
