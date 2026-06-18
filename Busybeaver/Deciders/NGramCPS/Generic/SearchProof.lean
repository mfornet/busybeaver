import Busybeaver.Deciders.NGramCPS.FixpointLemmas

/-!
Generic (alphabet-parametric) port of the `NGramCPS` search-algorithm lemmas.

The non-generic development in `SearchMonotonicity`/`FixpointLemmas`/`FinalStateLemmas`
proves monotonicity and fixpoint properties of `NGramCPS.runRound`/`runSearch`. This file
proves the analogous facts for `NGramCPS.Generic.runRound`/`runSearch`, which operate over an
arbitrary alphabet `α` and an abstract `Transition l α`.

The pure-array helper lemmas (`insertIfNew`, `insertAllIfNew`, ...) live in namespace
`NGramCPS` and are already alphabet-generic, so they are reused directly. Only the
`addSuccessors`/`runRound`/`runSearchOuter`/`runSearch`-level facts are re-proved, because the
generic versions differ in two ways:
- `Generic.addSuccessors` returns a `Bool` "changed" flag as a third component, and
- `Generic.runRound` folds that flag into its own `changed'` accumulator.
-/

open TM

namespace NGramCPS.Generic

variable {l : ℕ} {α : Type _} [DecidableEq α]

/-! ### `addSuccessors` fold helpers

`addSuccessors` is a `List.foldl` over `successors.toList` whose accumulator is a triple
`(known, frontier, changed)`. We first prove the relevant membership facts about the raw fold,
keeping the initial `changed` flag as an explicit parameter so the inductions go through (each
recursive step may flip it to `true`). The `addSuccessors`-level corollaries then follow by
definitional unfolding (`addSuccessors known frontier successors` is the fold with initial
flag `false`).
-/

lemma foldl_addStep_known_of_mem (xs : List (PartialConfig l α))
    (known : Array (PartialConfig l α)) (frontier : List (PartialConfig l α)) (b : Bool)
    {x : PartialConfig l α} (hx : x ∈ known) :
    x ∈ (xs.foldl (fun acc cfg =>
        if cfg ∈ acc.1 then acc else (acc.1.push cfg, cfg :: acc.2.1, true))
        (known, frontier, b)).1 := by
  induction xs generalizing known frontier b with
  | nil => simpa
  | cons cfg rest IH =>
      by_cases hcfg : cfg ∈ known
      · simpa [hcfg] using IH known frontier b hx
      · have hx' : x ∈ known.push cfg := by simp [Array.mem_push, hx]
        simpa [hcfg] using IH (known.push cfg) (cfg :: frontier) true hx'

lemma foldl_addStep_frontier_of_mem (xs : List (PartialConfig l α))
    (known : Array (PartialConfig l α)) (frontier : List (PartialConfig l α)) (b : Bool)
    {x : PartialConfig l α} (hx : x ∈ frontier) :
    x ∈ (xs.foldl (fun acc cfg =>
        if cfg ∈ acc.1 then acc else (acc.1.push cfg, cfg :: acc.2.1, true))
        (known, frontier, b)).2.1 := by
  induction xs generalizing known frontier b with
  | nil => simpa
  | cons cfg rest IH =>
      by_cases hcfg : cfg ∈ known
      · simpa [hcfg] using IH known frontier b hx
      · have hx' : x ∈ cfg :: frontier := by simp [hx]
        simpa [hcfg] using IH (known.push cfg) (cfg :: frontier) true hx'

lemma foldl_addStep_known_of_mem_list (xs : List (PartialConfig l α))
    (known : Array (PartialConfig l α)) (frontier : List (PartialConfig l α)) (b : Bool)
    {x : PartialConfig l α} (hx : x ∈ xs) :
    x ∈ (xs.foldl (fun acc cfg =>
        if cfg ∈ acc.1 then acc else (acc.1.push cfg, cfg :: acc.2.1, true))
        (known, frontier, b)).1 := by
  induction xs generalizing known frontier b with
  | nil => cases hx
  | cons cfg rest IH =>
      simp only [List.mem_cons] at hx
      by_cases hcfg : cfg ∈ known
      · rcases hx with rfl | hx
        · simpa [hcfg] using foldl_addStep_known_of_mem rest known frontier b hcfg
        · simpa [hcfg] using IH known frontier b hx
      · rcases hx with rfl | hx
        · have hmem : x ∈ known.push x := by simp
          simpa [hcfg] using
            foldl_addStep_known_of_mem rest (known.push x) (x :: frontier) true hmem
        · simpa [hcfg] using IH (known.push cfg) (cfg :: frontier) true hx

lemma foldl_addStep_frontier_of_not_mem_known (xs : List (PartialConfig l α))
    (known : Array (PartialConfig l α)) (frontier : List (PartialConfig l α)) (b : Bool)
    {x : PartialConfig l α} (hxnot : x ∉ known)
    (hx : x ∈ (xs.foldl (fun acc cfg =>
        if cfg ∈ acc.1 then acc else (acc.1.push cfg, cfg :: acc.2.1, true))
        (known, frontier, b)).1) :
    x ∈ (xs.foldl (fun acc cfg =>
        if cfg ∈ acc.1 then acc else (acc.1.push cfg, cfg :: acc.2.1, true))
        (known, frontier, b)).2.1 := by
  induction xs generalizing known frontier b with
  | nil =>
      simp only [List.foldl_nil] at hx
      exact absurd hx hxnot
  | cons cfg rest IH =>
      by_cases hcfg : cfg ∈ known
      · simpa [hcfg] using IH known frontier b hxnot (by simpa [hcfg] using hx)
      · simp only [List.foldl_cons, hcfg, if_neg, not_false_iff] at hx ⊢
        by_cases hxcfg : x = cfg
        · subst x
          exact foldl_addStep_frontier_of_mem rest (known.push cfg) (cfg :: frontier) true (by simp)
        · have hxnot' : x ∉ known.push cfg := by simp [Array.mem_push, hxnot, hxcfg]
          exact IH (known.push cfg) (cfg :: frontier) true hxnot' hx

/-- `addSuccessors` never removes a partial configuration that was already known. -/
lemma mem_addSuccessors_known_of_mem {known : Array (PartialConfig l α)}
    {frontier : List (PartialConfig l α)} {successors : Array (PartialConfig l α)}
    {x : PartialConfig l α} (hx : x ∈ known) :
    x ∈ (addSuccessors known frontier successors).1 :=
  foldl_addStep_known_of_mem successors.toList known frontier false hx

/-- `addSuccessors` never removes an element already present in the frontier list. -/
lemma mem_addSuccessors_frontier_of_mem {known : Array (PartialConfig l α)}
    {frontier : List (PartialConfig l α)} {successors : Array (PartialConfig l α)}
    {x : PartialConfig l α} (hx : x ∈ frontier) :
    x ∈ (addSuccessors known frontier successors).2.1 :=
  foldl_addStep_frontier_of_mem successors.toList known frontier false hx

/-- Every current-step successor is present in the updated known-partial-config array. -/
lemma mem_addSuccessors_known_of_mem_successor
    {known : Array (PartialConfig l α)} {frontier : List (PartialConfig l α)}
    {successors : Array (PartialConfig l α)} {x : PartialConfig l α}
    (hx : x ∈ successors) :
    x ∈ (addSuccessors known frontier successors).1 :=
  foldl_addStep_known_of_mem_list successors.toList known frontier false (by simpa using hx)

/-- Anything newly known but not previously known is also present in the updated frontier. -/
lemma mem_addSuccessors_frontier_of_not_mem_known_of_mem_knownResult
    {known : Array (PartialConfig l α)} {frontier : List (PartialConfig l α)}
    {successors : Array (PartialConfig l α)} {x : PartialConfig l α}
    (hxnot : x ∉ known)
    (hx : x ∈ (addSuccessors known frontier successors).1) :
    x ∈ (addSuccessors known frontier successors).2.1 :=
  foldl_addStep_frontier_of_not_mem_known successors.toList known frontier false hxnot hx

/-! ### `runRound` monotonicity (closed results) -/

variable [Inhabited α] {tm : Transition l α}

/-- A closed `runRound` preserves previously known partial configurations. -/
lemma runRound_closed_preserves_partialConfig_mem
    {bound : ℕ} {state finalState : SearchState l α} {changed : Bool}
    {pc : PartialConfig l α}
    (hRound : runRound tm bound state changed = .closed finalState)
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
          cases hstep : stepPartialConfig tm state.leftNGrams state.rightNGrams hd with
          | haltingEdge =>
              simp [hstep] at hRound
          | advanced expansion =>
              set nextLeft := insertAllIfNew state.leftNGrams expansion.leftNGrams with hnextLeft
              set nextRight := insertAllIfNew state.rightNGrams expansion.rightNGrams with hnextRight
              set nextConfigs := (addSuccessors state.partialConfigs tl expansion.successors).1
                with hnextConfigs
              set nextFrontier := (addSuccessors state.partialConfigs tl expansion.successors).2.1
                with hnextFrontier
              set configsChanged := (addSuccessors state.partialConfigs tl expansion.successors).2.2
                with hconfigsChanged
              set changed' :=
                changed || configsChanged ||
                nextLeft.size ≠ state.leftNGrams.size ||
                nextRight.size ≠ state.rightNGrams.size with hchanged'
              let nextState : SearchState l α := {
                leftNGrams := nextLeft
                rightNGrams := nextRight
                partialConfigs := nextConfigs
                frontier := nextFrontier
              }
              have hpc' : pc ∈ nextState.partialConfigs := by
                dsimp [nextState]
                simpa [nextConfigs] using mem_addSuccessors_known_of_mem
                  (known := state.partialConfigs) (frontier := tl)
                  (successors := expansion.successors) hpc
              have hRound' : runRound tm bound nextState changed' = .closed finalState := by
                simpa [nextLeft, nextRight, nextConfigs, nextFrontier, configsChanged, changed',
                  nextState, hstep] using hRound
              exact IH hRound' hpc'

/-- A closed `runRound` preserves previously known left `n`-grams. -/
lemma runRound_closed_preserves_leftNGram_mem
    {bound : ℕ} {state finalState : SearchState l α} {changed : Bool}
    {ng : Array α}
    (hRound : runRound tm bound state changed = .closed finalState)
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
          cases hstep : stepPartialConfig tm state.leftNGrams state.rightNGrams hd with
          | haltingEdge =>
              simp [hstep] at hRound
          | advanced expansion =>
              set nextLeft := insertAllIfNew state.leftNGrams expansion.leftNGrams with hnextLeft
              set nextRight := insertAllIfNew state.rightNGrams expansion.rightNGrams with hnextRight
              set nextConfigs := (addSuccessors state.partialConfigs tl expansion.successors).1
                with hnextConfigs
              set nextFrontier := (addSuccessors state.partialConfigs tl expansion.successors).2.1
                with hnextFrontier
              set configsChanged := (addSuccessors state.partialConfigs tl expansion.successors).2.2
                with hconfigsChanged
              set changed' :=
                changed || configsChanged ||
                nextLeft.size ≠ state.leftNGrams.size ||
                nextRight.size ≠ state.rightNGrams.size with hchanged'
              let nextState : SearchState l α := {
                leftNGrams := nextLeft
                rightNGrams := nextRight
                partialConfigs := nextConfigs
                frontier := nextFrontier
              }
              have hng' : ng ∈ nextState.leftNGrams := by
                dsimp [nextState]
                simpa [nextLeft] using mem_insertAllIfNew_of_mem (base := state.leftNGrams)
                  (extra := expansion.leftNGrams) hng
              have hRound' : runRound tm bound nextState changed' = .closed finalState := by
                simpa [nextLeft, nextRight, nextConfigs, nextFrontier, configsChanged, changed',
                  nextState, hstep] using hRound
              exact IH hRound' hng'

/-- A closed `runRound` preserves previously known right `n`-grams. -/
lemma runRound_closed_preserves_rightNGram_mem
    {bound : ℕ} {state finalState : SearchState l α} {changed : Bool}
    {ng : Array α}
    (hRound : runRound tm bound state changed = .closed finalState)
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
          cases hstep : stepPartialConfig tm state.leftNGrams state.rightNGrams hd with
          | haltingEdge =>
              simp [hstep] at hRound
          | advanced expansion =>
              set nextLeft := insertAllIfNew state.leftNGrams expansion.leftNGrams with hnextLeft
              set nextRight := insertAllIfNew state.rightNGrams expansion.rightNGrams with hnextRight
              set nextConfigs := (addSuccessors state.partialConfigs tl expansion.successors).1
                with hnextConfigs
              set nextFrontier := (addSuccessors state.partialConfigs tl expansion.successors).2.1
                with hnextFrontier
              set configsChanged := (addSuccessors state.partialConfigs tl expansion.successors).2.2
                with hconfigsChanged
              set changed' :=
                changed || configsChanged ||
                nextLeft.size ≠ state.leftNGrams.size ||
                nextRight.size ≠ state.rightNGrams.size with hchanged'
              let nextState : SearchState l α := {
                leftNGrams := nextLeft
                rightNGrams := nextRight
                partialConfigs := nextConfigs
                frontier := nextFrontier
              }
              have hng' : ng ∈ nextState.rightNGrams := by
                dsimp [nextState]
                simpa [nextRight] using mem_insertAllIfNew_of_mem (base := state.rightNGrams)
                  (extra := expansion.rightNGrams) hng
              have hRound' : runRound tm bound nextState changed' = .closed finalState := by
                simpa [nextLeft, nextRight, nextConfigs, nextFrontier, configsChanged, changed',
                  nextState, hstep] using hRound
              exact IH hRound' hng'

/-- A restarting `runRound` preserves previously known partial configurations. -/
lemma runRound_restart_preserves_partialConfig_mem
    {bound remaining : ℕ} {state restartState : SearchState l α} {changed : Bool}
    {pc : PartialConfig l α}
    (hRound : runRound tm bound state changed = .restart remaining restartState)
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
          cases hstep : stepPartialConfig tm state.leftNGrams state.rightNGrams hd with
          | haltingEdge =>
              simp [hstep] at hRound
          | advanced expansion =>
              set nextLeft := insertAllIfNew state.leftNGrams expansion.leftNGrams with hnextLeft
              set nextRight := insertAllIfNew state.rightNGrams expansion.rightNGrams with hnextRight
              set nextConfigs := (addSuccessors state.partialConfigs tl expansion.successors).1
                with hnextConfigs
              set nextFrontier := (addSuccessors state.partialConfigs tl expansion.successors).2.1
                with hnextFrontier
              set configsChanged := (addSuccessors state.partialConfigs tl expansion.successors).2.2
                with hconfigsChanged
              set changed' :=
                changed || configsChanged ||
                nextLeft.size ≠ state.leftNGrams.size ||
                nextRight.size ≠ state.rightNGrams.size with hchanged'
              let nextState : SearchState l α := {
                leftNGrams := nextLeft
                rightNGrams := nextRight
                partialConfigs := nextConfigs
                frontier := nextFrontier
              }
              have hpc' : pc ∈ nextState.partialConfigs := by
                dsimp [nextState]
                simpa [nextConfigs] using mem_addSuccessors_known_of_mem
                  (known := state.partialConfigs) (frontier := tl)
                  (successors := expansion.successors) hpc
              have hRound' : runRound tm bound nextState changed' = .restart remaining restartState := by
                simpa [nextLeft, nextRight, nextConfigs, nextFrontier, configsChanged, changed',
                  nextState, hstep] using hRound
              exact IH hRound' hpc'

/-- A restarting `runRound` preserves previously known left `n`-grams. -/
lemma runRound_restart_preserves_leftNGram_mem
    {bound remaining : ℕ} {state restartState : SearchState l α} {changed : Bool}
    {ng : Array α}
    (hRound : runRound tm bound state changed = .restart remaining restartState)
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
          cases hstep : stepPartialConfig tm state.leftNGrams state.rightNGrams hd with
          | haltingEdge =>
              simp [hstep] at hRound
          | advanced expansion =>
              set nextLeft := insertAllIfNew state.leftNGrams expansion.leftNGrams with hnextLeft
              set nextRight := insertAllIfNew state.rightNGrams expansion.rightNGrams with hnextRight
              set nextConfigs := (addSuccessors state.partialConfigs tl expansion.successors).1
                with hnextConfigs
              set nextFrontier := (addSuccessors state.partialConfigs tl expansion.successors).2.1
                with hnextFrontier
              set configsChanged := (addSuccessors state.partialConfigs tl expansion.successors).2.2
                with hconfigsChanged
              set changed' :=
                changed || configsChanged ||
                nextLeft.size ≠ state.leftNGrams.size ||
                nextRight.size ≠ state.rightNGrams.size with hchanged'
              let nextState : SearchState l α := {
                leftNGrams := nextLeft
                rightNGrams := nextRight
                partialConfigs := nextConfigs
                frontier := nextFrontier
              }
              have hng' : ng ∈ nextState.leftNGrams := by
                dsimp [nextState]
                simpa [nextLeft] using mem_insertAllIfNew_of_mem (base := state.leftNGrams)
                  (extra := expansion.leftNGrams) hng
              have hRound' : runRound tm bound nextState changed' = .restart remaining restartState := by
                simpa [nextLeft, nextRight, nextConfigs, nextFrontier, configsChanged, changed',
                  nextState, hstep] using hRound
              exact IH hRound' hng'

/-- A restarting `runRound` preserves previously known right `n`-grams. -/
lemma runRound_restart_preserves_rightNGram_mem
    {bound remaining : ℕ} {state restartState : SearchState l α} {changed : Bool}
    {ng : Array α}
    (hRound : runRound tm bound state changed = .restart remaining restartState)
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
          cases hstep : stepPartialConfig tm state.leftNGrams state.rightNGrams hd with
          | haltingEdge =>
              simp [hstep] at hRound
          | advanced expansion =>
              set nextLeft := insertAllIfNew state.leftNGrams expansion.leftNGrams with hnextLeft
              set nextRight := insertAllIfNew state.rightNGrams expansion.rightNGrams with hnextRight
              set nextConfigs := (addSuccessors state.partialConfigs tl expansion.successors).1
                with hnextConfigs
              set nextFrontier := (addSuccessors state.partialConfigs tl expansion.successors).2.1
                with hnextFrontier
              set configsChanged := (addSuccessors state.partialConfigs tl expansion.successors).2.2
                with hconfigsChanged
              set changed' :=
                changed || configsChanged ||
                nextLeft.size ≠ state.leftNGrams.size ||
                nextRight.size ≠ state.rightNGrams.size with hchanged'
              let nextState : SearchState l α := {
                leftNGrams := nextLeft
                rightNGrams := nextRight
                partialConfigs := nextConfigs
                frontier := nextFrontier
              }
              have hng' : ng ∈ nextState.rightNGrams := by
                dsimp [nextState]
                simpa [nextRight] using mem_insertAllIfNew_of_mem (base := state.rightNGrams)
                  (extra := expansion.rightNGrams) hng
              have hRound' : runRound tm bound nextState changed' = .restart remaining restartState := by
                simpa [nextLeft, nextRight, nextConfigs, nextFrontier, configsChanged, changed',
                  nextState, hstep] using hRound
              exact IH hRound' hng'

/-- A `runRound` result can only be `.closed` if its `changed` flag is false. -/
lemma runRound_closed_changed_false
    {remaining : ℕ} {state finalState : SearchState l α} {changed : Bool}
    (hRound : runRound tm remaining state changed = .closed finalState) :
    changed = false := by
  induction remaining generalizing state changed finalState with
  | zero =>
      cases hfrontier : state.frontier with
      | nil =>
          cases hchanged : changed with
          | false => rfl
          | true => simp [runRound, hfrontier, hchanged] at hRound
      | cons hd tl =>
          simp [runRound, hfrontier] at hRound
  | succ remaining IH =>
      cases hfrontier : state.frontier with
      | nil =>
          cases hchanged : changed with
          | false => rfl
          | true => simp [runRound, hfrontier, hchanged] at hRound
      | cons hd tl =>
          unfold runRound at hRound
          rw [hfrontier] at hRound
          cases hstep : stepPartialConfig tm state.leftNGrams state.rightNGrams hd with
          | haltingEdge =>
              simp [hstep] at hRound
          | advanced expansion =>
              set nextLeft := insertAllIfNew state.leftNGrams expansion.leftNGrams with hnextLeft
              set nextRight := insertAllIfNew state.rightNGrams expansion.rightNGrams with hnextRight
              set nextConfigs := (addSuccessors state.partialConfigs tl expansion.successors).1
                with hnextConfigs
              set nextFrontier := (addSuccessors state.partialConfigs tl expansion.successors).2.1
                with hnextFrontier
              set configsChanged := (addSuccessors state.partialConfigs tl expansion.successors).2.2
                with hconfigsChanged
              set changed' :=
                changed || configsChanged ||
                nextLeft.size ≠ state.leftNGrams.size ||
                nextRight.size ≠ state.rightNGrams.size with hchanged'
              let nextState : SearchState l α := {
                leftNGrams := nextLeft
                rightNGrams := nextRight
                partialConfigs := nextConfigs
                frontier := nextFrontier
              }
              have hRound' : runRound tm remaining nextState changed' = .closed finalState := by
                simpa [nextLeft, nextRight, nextConfigs, nextFrontier, configsChanged, changed',
                  nextState, hstep] using hRound
              have hchanged'False : changed' = false := IH hRound'
              cases changed with
              | false => rfl
              | true => simp [changed'] at hchanged'False

/-- Closed rounds do not change the left `n`-gram set. -/
lemma runRound_closed_leftNGrams_eq
    {remaining : ℕ} {state finalState : SearchState l α} {changed : Bool}
    (hRound : runRound tm remaining state changed = .closed finalState) :
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
            runRound_closed_changed_false hRound
          unfold runRound at hRound
          rw [hfrontier] at hRound
          cases hstep : stepPartialConfig tm state.leftNGrams state.rightNGrams hd with
          | haltingEdge =>
              simp [hstep] at hRound
          | advanced expansion =>
              set nextLeft := insertAllIfNew state.leftNGrams expansion.leftNGrams with hnextLeft
              set nextRight := insertAllIfNew state.rightNGrams expansion.rightNGrams with hnextRight
              set nextConfigs := (addSuccessors state.partialConfigs tl expansion.successors).1
                with hnextConfigs
              set nextFrontier := (addSuccessors state.partialConfigs tl expansion.successors).2.1
                with hnextFrontier
              set configsChanged := (addSuccessors state.partialConfigs tl expansion.successors).2.2
                with hconfigsChanged
              set changed' :=
                changed || configsChanged ||
                nextLeft.size ≠ state.leftNGrams.size ||
                nextRight.size ≠ state.rightNGrams.size with hchanged'
              let nextState : SearchState l α := {
                leftNGrams := nextLeft
                rightNGrams := nextRight
                partialConfigs := nextConfigs
                frontier := nextFrontier
              }
              have hRound' : runRound tm remaining nextState changed' = .closed finalState := by
                simpa [nextLeft, nextRight, nextConfigs, nextFrontier, configsChanged, changed',
                  nextState, hstep] using hRound
              have hstable :
                  (configsChanged = false ∧
                    nextLeft.size = state.leftNGrams.size) ∧
                    nextRight.size = state.rightNGrams.size := by
                have hchanged'False : changed' = false :=
                  runRound_closed_changed_false hRound'
                simpa [changed', hchangedFalse] using hchanged'False
              have hsize : nextLeft.size = state.leftNGrams.size := hstable.1.2
              have hnextLeftEq : nextLeft = state.leftNGrams :=
                insertAllIfNew_eq_of_size_eq hsize
              have hrec : nextLeft = finalState.leftNGrams := by
                simpa [nextState] using IH hRound'
              exact hnextLeftEq.symm.trans hrec

/-- Closed rounds do not change the right `n`-gram set. -/
lemma runRound_closed_rightNGrams_eq
    {remaining : ℕ} {state finalState : SearchState l α} {changed : Bool}
    (hRound : runRound tm remaining state changed = .closed finalState) :
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
            runRound_closed_changed_false hRound
          unfold runRound at hRound
          rw [hfrontier] at hRound
          cases hstep : stepPartialConfig tm state.leftNGrams state.rightNGrams hd with
          | haltingEdge =>
              simp [hstep] at hRound
          | advanced expansion =>
              set nextLeft := insertAllIfNew state.leftNGrams expansion.leftNGrams with hnextLeft
              set nextRight := insertAllIfNew state.rightNGrams expansion.rightNGrams with hnextRight
              set nextConfigs := (addSuccessors state.partialConfigs tl expansion.successors).1
                with hnextConfigs
              set nextFrontier := (addSuccessors state.partialConfigs tl expansion.successors).2.1
                with hnextFrontier
              set configsChanged := (addSuccessors state.partialConfigs tl expansion.successors).2.2
                with hconfigsChanged
              set changed' :=
                changed || configsChanged ||
                nextLeft.size ≠ state.leftNGrams.size ||
                nextRight.size ≠ state.rightNGrams.size with hchanged'
              let nextState : SearchState l α := {
                leftNGrams := nextLeft
                rightNGrams := nextRight
                partialConfigs := nextConfigs
                frontier := nextFrontier
              }
              have hRound' : runRound tm remaining nextState changed' = .closed finalState := by
                simpa [nextLeft, nextRight, nextConfigs, nextFrontier, configsChanged, changed',
                  nextState, hstep] using hRound
              have hstable :
                  (configsChanged = false ∧
                    nextLeft.size = state.leftNGrams.size) ∧
                    nextRight.size = state.rightNGrams.size := by
                have hchanged'False : changed' = false :=
                  runRound_closed_changed_false hRound'
                simpa [changed', hchangedFalse] using hchanged'False
              have hsize : nextRight.size = state.rightNGrams.size := hstable.2
              have hnextRightEq : nextRight = state.rightNGrams :=
                insertAllIfNew_eq_of_size_eq hsize
              have hrec : nextRight = finalState.rightNGrams := by
                simpa [nextState] using IH hRound'
              exact hnextRightEq.symm.trans hrec

/-- Any restart state returned by `runRound` has a full frontier. -/
lemma runRound_restart_has_fullFrontier
    {bound remaining : ℕ} {state restartState : SearchState l α} {changed : Bool}
    (hRound : runRound tm bound state changed = .restart remaining restartState) :
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
          cases hstep : stepPartialConfig tm state.leftNGrams state.rightNGrams hd with
          | haltingEdge =>
              simp [hstep] at hRound
          | advanced expansion =>
              set nextLeft := insertAllIfNew state.leftNGrams expansion.leftNGrams with hnextLeft
              set nextRight := insertAllIfNew state.rightNGrams expansion.rightNGrams with hnextRight
              set nextConfigs := (addSuccessors state.partialConfigs tl expansion.successors).1
                with hnextConfigs
              set nextFrontier := (addSuccessors state.partialConfigs tl expansion.successors).2.1
                with hnextFrontier
              set configsChanged := (addSuccessors state.partialConfigs tl expansion.successors).2.2
                with hconfigsChanged
              set changed' :=
                changed || configsChanged ||
                nextLeft.size ≠ state.leftNGrams.size ||
                nextRight.size ≠ state.rightNGrams.size with hchanged'
              let nextState : SearchState l α := {
                leftNGrams := nextLeft
                rightNGrams := nextRight
                partialConfigs := nextConfigs
                frontier := nextFrontier
              }
              have hRound' : runRound tm bound nextState changed' = .restart remaining restartState := by
                simpa [nextLeft, nextRight, nextConfigs, nextFrontier, configsChanged, changed',
                  nextState, hstep] using hRound
              exact IH hRound'

/-! ### `runSearchOuter` / `runSearch` -/

/-- A closed `runSearchOuter` arises from a final round with full frontier. -/
lemma runSearchOuter_closed_extract_finalRound
    {rounds remaining : ℕ} {state finalState : SearchState l α}
    (hfrontier : state.frontier = state.partialConfigs.toList)
    (hSearch : runSearchOuter tm rounds remaining state = .closed finalState) :
    ∃ remaining' state',
      runRound tm remaining' state' false = .closed finalState ∧
      state'.frontier = state'.partialConfigs.toList := by
  revert remaining state finalState hfrontier hSearch
  induction rounds with
  | zero =>
      intro remaining state finalState hfrontier hSearch
      simp [runSearchOuter] at hSearch
  | succ rounds IH =>
      intro remaining state finalState hfrontier hSearch
      unfold runSearchOuter at hSearch
      cases hRound : runRound tm remaining state false with
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
            (runRound_restart_has_fullFrontier hRound) hSearch

/-- A closed `runSearchOuter` preserves previously known partial configurations. -/
lemma runSearchOuter_closed_preserves_partialConfig_mem
    {rounds remaining : ℕ} {state finalState : SearchState l α} {pc : PartialConfig l α}
    (hSearch : runSearchOuter tm rounds remaining state = .closed finalState)
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
      cases hRound : runRound tm remaining state false with
      | closed roundState =>
          simp [hRound] at hSearch
          cases hSearch
          exact runRound_closed_preserves_partialConfig_mem hRound hpc
      | haltingEdge =>
          simp [hRound] at hSearch
      | timeout =>
          simp [hRound] at hSearch
      | restart remaining' restartState =>
          simp [hRound] at hSearch
          exact IH (remaining := remaining') (state := restartState) (finalState := finalState) hSearch
            (runRound_restart_preserves_partialConfig_mem hRound hpc)

/-- A closed `runSearchOuter` preserves previously known left `n`-grams. -/
lemma runSearchOuter_closed_preserves_leftNGram_mem
    {rounds remaining : ℕ} {state finalState : SearchState l α} {ng : Array α}
    (hSearch : runSearchOuter tm rounds remaining state = .closed finalState)
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
      cases hRound : runRound tm remaining state false with
      | closed roundState =>
          simp [hRound] at hSearch
          cases hSearch
          exact runRound_closed_preserves_leftNGram_mem hRound hng
      | haltingEdge =>
          simp [hRound] at hSearch
      | timeout =>
          simp [hRound] at hSearch
      | restart remaining' restartState =>
          simp [hRound] at hSearch
          exact IH (remaining := remaining') (state := restartState) (finalState := finalState) hSearch
            (runRound_restart_preserves_leftNGram_mem hRound hng)

/-- A closed `runSearchOuter` preserves previously known right `n`-grams. -/
lemma runSearchOuter_closed_preserves_rightNGram_mem
    {rounds remaining : ℕ} {state finalState : SearchState l α} {ng : Array α}
    (hSearch : runSearchOuter tm rounds remaining state = .closed finalState)
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
      cases hRound : runRound tm remaining state false with
      | closed roundState =>
          simp [hRound] at hSearch
          cases hSearch
          exact runRound_closed_preserves_rightNGram_mem hRound hng
      | haltingEdge =>
          simp [hRound] at hSearch
      | timeout =>
          simp [hRound] at hSearch
      | restart remaining' restartState =>
          simp [hRound] at hSearch
          exact IH (remaining := remaining') (state := restartState) (finalState := finalState) hSearch
            (runRound_restart_preserves_rightNGram_mem hRound hng)

/-- A closed `runSearch` arises from a final round with full frontier. -/
lemma runSearch_closed_extract_finalRound
    {bound : ℕ} {state finalState : SearchState l α}
    (hfrontier : state.frontier = state.partialConfigs.toList)
    (hSearch : runSearch tm bound state = .closed finalState) :
    ∃ remaining state',
      runRound tm remaining state' false = .closed finalState ∧
      state'.frontier = state'.partialConfigs.toList :=
  runSearchOuter_closed_extract_finalRound hfrontier hSearch

/-- A closed `runSearch` preserves previously known partial configurations. -/
lemma runSearch_closed_preserves_partialConfig_mem
    {bound : ℕ} {state finalState : SearchState l α} {pc : PartialConfig l α}
    (hSearch : runSearch tm bound state = .closed finalState)
    (hpc : pc ∈ state.partialConfigs) :
    pc ∈ finalState.partialConfigs :=
  runSearchOuter_closed_preserves_partialConfig_mem hSearch hpc

/-- A closed `runSearch` preserves previously known left `n`-grams. -/
lemma runSearch_closed_preserves_leftNGram_mem
    {bound : ℕ} {state finalState : SearchState l α} {ng : Array α}
    (hSearch : runSearch tm bound state = .closed finalState)
    (hng : ng ∈ state.leftNGrams) :
    ng ∈ finalState.leftNGrams :=
  runSearchOuter_closed_preserves_leftNGram_mem hSearch hng

/-- A closed `runSearch` preserves previously known right `n`-grams. -/
lemma runSearch_closed_preserves_rightNGram_mem
    {bound : ℕ} {state finalState : SearchState l α} {ng : Array α}
    (hSearch : runSearch tm bound state = .closed finalState)
    (hng : ng ∈ state.rightNGrams) :
    ng ∈ finalState.rightNGrams :=
  runSearchOuter_closed_preserves_rightNGram_mem hSearch hng

/-! ### Fixpoint completeness of a closed round -/

/-- A closed round processes every configuration pending in the frontier or yet to be added. -/
lemma runRound_closed_fixpoint_of_frontier_or_new
    {remaining : ℕ} {state finalState : SearchState l α} {changed : Bool}
    (hRound : runRound tm remaining state changed = .closed finalState)
    {pc : PartialConfig l α}
    (hpc : pc ∈ state.frontier ∨ (pc ∈ finalState.partialConfigs ∧ pc ∉ state.partialConfigs)) :
    ∃ expansion,
      stepPartialConfig tm finalState.leftNGrams finalState.rightNGrams pc = .advanced expansion ∧
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
                  simp [hfrontier] at hfront
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
                  simp [hfrontier] at hfront
              | inr hnew =>
                  exact False.elim (hnew.2 hnew.1)
          | true =>
              simp [runRound, hfrontier, hchanged] at hRound
      | cons hd tl =>
          have hleftEq : state.leftNGrams = finalState.leftNGrams :=
            runRound_closed_leftNGrams_eq hRound
          have hrightEq : state.rightNGrams = finalState.rightNGrams :=
            runRound_closed_rightNGrams_eq hRound
          unfold runRound at hRound
          rw [hfrontier] at hRound
          cases hstep : stepPartialConfig tm state.leftNGrams state.rightNGrams hd with
          | haltingEdge =>
              simp [hstep] at hRound
          | advanced expansion =>
              set nextLeft := insertAllIfNew state.leftNGrams expansion.leftNGrams with hnextLeft
              set nextRight := insertAllIfNew state.rightNGrams expansion.rightNGrams with hnextRight
              set nextConfigs := (addSuccessors state.partialConfigs tl expansion.successors).1
                with hnextConfigs
              set nextFrontier := (addSuccessors state.partialConfigs tl expansion.successors).2.1
                with hnextFrontier
              set configsChanged := (addSuccessors state.partialConfigs tl expansion.successors).2.2
                with hconfigsChanged
              set changed' :=
                changed || configsChanged ||
                nextLeft.size ≠ state.leftNGrams.size ||
                nextRight.size ≠ state.rightNGrams.size with hchanged'
              let nextState : SearchState l α := {
                leftNGrams := nextLeft
                rightNGrams := nextRight
                partialConfigs := nextConfigs
                frontier := nextFrontier
              }
              have hRound' : runRound tm remaining nextState changed' = .closed finalState := by
                simpa [nextLeft, nextRight, nextConfigs, nextFrontier, configsChanged, changed',
                  nextState, hstep] using hRound
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
                        exact runRound_closed_preserves_leftNGram_mem hRound' hmemNext
                      · intro ng hng
                        have hmemNext : ng ∈ nextState.rightNGrams := by
                          dsimp [nextState]
                          simpa [nextRight] using
                            mem_insertAllIfNew_of_mem_extra (base := state.rightNGrams)
                              (extra := expansion.rightNGrams) hng
                        exact runRound_closed_preserves_rightNGram_mem hRound' hmemNext
                      · intro pc' hsucc
                        have hmemNext : pc' ∈ nextState.partialConfigs := by
                          dsimp [nextState]
                          simpa [nextConfigs] using
                            mem_addSuccessors_known_of_mem_successor
                              (known := state.partialConfigs) (frontier := tl)
                              (successors := expansion.successors) hsucc
                        exact runRound_closed_preserves_partialConfig_mem hRound' hmemNext
                  | inr hpc_tl =>
                      have hpcNext :
                          pc ∈ nextState.frontier ∨
                            (pc ∈ finalState.partialConfigs ∧ pc ∉ nextState.partialConfigs) := by
                        left
                        dsimp [nextState]
                        simpa [nextFrontier] using
                          mem_addSuccessors_frontier_of_mem
                            (known := state.partialConfigs) (frontier := tl)
                            (successors := expansion.successors) hpc_tl
                      exact IH hRound' hpcNext
              | inr hnew =>
                  by_cases hpcNext : pc ∈ nextState.partialConfigs
                  · have hpcFrontier : pc ∈ nextState.frontier := by
                      dsimp [nextState] at hpcNext ⊢
                      simpa [nextConfigs, nextFrontier] using
                        mem_addSuccessors_frontier_of_not_mem_known_of_mem_knownResult
                          (known := state.partialConfigs) (frontier := tl)
                          (successors := expansion.successors) hnew.2
                          (by simpa [nextConfigs] using hpcNext)
                    exact IH hRound' (Or.inl hpcFrontier)
                  · exact IH hRound' (Or.inr ⟨hnew.1, hpcNext⟩)

/-- A closed round started from a full frontier yields a fixpoint for every final config. -/
lemma runRound_closed_fixpoint_of_fullFrontier
    {remaining : ℕ} {state finalState : SearchState l α}
    (hRound : runRound tm remaining state false = .closed finalState)
    (hfrontier : state.frontier = state.partialConfigs.toList)
    {pc : PartialConfig l α} (hpc : pc ∈ finalState.partialConfigs) :
    ∃ expansion,
      stepPartialConfig tm finalState.leftNGrams finalState.rightNGrams pc = .advanced expansion ∧
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
  exact runRound_closed_fixpoint_of_frontier_or_new hRound hpc'

/-- Any stored partial configuration is a one-step fixpoint in the final closed search state. -/
lemma partialConfig_fixpoint_of_closedResult
    {bound : ℕ} {state finalState : SearchState l α}
    (hfrontier : state.frontier = state.partialConfigs.toList)
    (hSearch : runSearch tm bound state = .closed finalState)
    {pc : PartialConfig l α} (hpc : pc ∈ finalState.partialConfigs) :
    ∃ expansion,
      stepPartialConfig tm finalState.leftNGrams finalState.rightNGrams pc = .advanced expansion ∧
      (∀ ng ∈ expansion.leftNGrams, ng ∈ finalState.leftNGrams) ∧
      (∀ ng ∈ expansion.rightNGrams, ng ∈ finalState.rightNGrams) ∧
      (∀ pc' ∈ expansion.successors, pc' ∈ finalState.partialConfigs) := by
  obtain ⟨remaining, state', hRound, hfrontier'⟩ :=
    runSearch_closed_extract_finalRound hfrontier hSearch
  exact runRound_closed_fixpoint_of_fullFrontier hRound hfrontier' hpc

end NGramCPS.Generic
