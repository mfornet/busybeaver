import Busybeaver.Deciders.NGramCPS.MatchingLemmas

open TM

namespace NGramCPS

/--
For a right-moving real machine step, the concrete successor configuration has a
stored matching `PartialConfig` in the final search state.

Why this is correct:
- the visible part of the successor is one of the successors enumerated by
  `expandRight`;
- the actual far-right symbol is justified by the right-window invariant on the
  original configuration;
- the fixpoint theorem says every enumerated successor is already in
  `finalState.partialConfigs`.

Proof outline:
- use the right-side offset-1 window to identify the actual far symbol;
- show that symbol appears in `matchingLastSymbols`;
- conclude that the corresponding successor from `expansion.successors` is in the
  final partial-config array and matches the real successor.

Proof complexity:
- high; this is the main bridge between tape semantics and `expandRight`.
-/
lemma rightStep_has_matching_partialConfig (cfg : NGramCPSConfig) {finalState : SearchState l s}
    {A : Config l s} {pc : PartialConfig l s} {writeSym : Symbol s} {nextState : Label l}
    (hcfg : cfg.n ≠ 0)
    (hmatch : MatchesPartial cfg.n pc A)
    (hright : AllRightWindowsIn cfg.n finalState.rightNGrams A)
    (hfix :
      ∃ expansion,
        stepPartialConfig M finalState.leftNGrams finalState.rightNGrams pc = .advanced expansion ∧
        (∀ ng ∈ expansion.leftNGrams, ng ∈ finalState.leftNGrams) ∧
        (∀ ng ∈ expansion.rightNGrams, ng ∈ finalState.rightNGrams) ∧
        (∀ pc' ∈ expansion.successors, pc' ∈ finalState.partialConfigs))
    (hstmt : Machine.get M A.state A.tape.head = Stmt.next writeSym .right nextState) :
    ∃ pc',
      pc' ∈ finalState.partialConfigs ∧
      MatchesPartial cfg.n pc' { state := nextState, tape := (A.tape.write writeSym).move .right } := by
  obtain ⟨expansion, hstep, _hleftExp, _hrightExp, hsuccExp⟩ := hfix
  cases hcfgn : cfg.n with
  | zero =>
      exact (hcfg hcfgn).elim
  | succ n =>
      have hmatch' : MatchesPartial (n + 1) pc A := by
        simpa [hcfgn] using hmatch
      have hright' : AllRightWindowsIn (n + 1) finalState.rightNGrams A := by
        simpa [hcfgn] using hright
      have hstmt' : Machine.get M pc.state pc.head = Stmt.next writeSym .right nextState := by
        simpa [MatchesPartial_state hmatch', MatchesPartial_head hmatch'] using hstmt
      have hexp : expansion = expandRight finalState.rightNGrams pc writeSym nextState := by
        simpa [stepPartialConfig, hstmt'] using hstep.symm
      have hdrop : pc.right.drop 1 = rightWindowAt n 1 A := by
        exact rightVisibleDrop_eq_windowAt_one (l := l) (s := s) n hmatch'
      let farSym := (rightWindowAt (n + 1) 1 A).getD n default
      let pc' : PartialConfig l s := {
        left := shiftInNear writeSym pc.left
        head := pc.right.getD 0 default
        state := nextState
        right := appendFar (pc.right.drop 1) farSym
      }
      have hprefix :
          (rightWindowAt (n + 1) 1 A).take (pc.right.drop 1).size = pc.right.drop 1 := by
        rw [hdrop]
        simpa [rightWindowAt, Turing.ListBlank.take.length] using
          (rightWindowAt_one_take_succ (l := l) (s := s) n A)
      have hfarMem : farSym ∈ matchingLastSymbols (pc.right.drop 1) finalState.rightNGrams default := by
        have hmem :=
          mem_matchingLastSymbols_of_mem
            (pref := pc.right.drop 1)
            (ngrams := finalState.rightNGrams)
            (ngram := rightWindowAt (n + 1) 1 A)
            (fallback := default)
            (hmem := hright' 1)
            hprefix
        simpa [farSym, hdrop, rightWindowAt, Turing.ListBlank.take.length] using hmem
      have hpc'Succ : pc' ∈ expansion.successors := by
        rw [hexp, expandRight]
        refine Array.mem_map.2 ?_
        exact ⟨farSym, hfarMem, by rfl⟩
      refine ⟨pc', hsuccExp _ (by simpa [hexp] using hpc'Succ), ?_⟩
      constructor
      · rfl
      constructor
      · calc
          pc'.head = pc.right.getD 0 default := rfl
          _ = A.tape.right.head := matched_right_getD_zero_eq (l := l) (s := s) n hmatch'
          _ = ((A.tape.write writeSym).move .right).head := by simp [Turing.Tape.move, Turing.Tape.write]
      constructor
      · calc
          pc'.left = shiftInNear writeSym pc.left := rfl
          _ = shiftInNear writeSym (leftWindowAt (n + 1) 0 A) := by
                rw [MatchesPartial_left hmatch']
          _ = leftWindowAt (n + 1) 0 { state := nextState, tape := (A.tape.write writeSym).move .right } := by
                symm
                simpa using
                  (leftWindowAt_moveRight_zero_succ (l := l) (s := s) n A writeSym nextState)
      · calc
          pc'.right = appendFar (pc.right.drop 1) farSym := rfl
          _ = appendFar (rightWindowAt n 1 A) ((rightWindowAt (n + 1) 1 A).getD n default) := by
                simp [farSym, hdrop]
          _ = rightWindowAt (n + 1) 1 A := appendFar_rightWindowAt_one_succ (l := l) (s := s) n A
          _ = rightWindowAt (n + 1) 0 { state := nextState, tape := (A.tape.write writeSym).move .right } := by
                symm
                simpa using
                  (rightWindowAt_moveRight (l := l) (s := s) (n := n + 1) (k := 0)
                    A writeSym nextState)

/--
For a right-moving real machine step, all left windows of the successor remain in
the final left `n`-gram set.

Why this is correct:
- the visible left window is exactly the left `n`-gram emitted by `expandRight`;
- every farther-left window is just an older left window of the original
  configuration, shifted by one cell.

Proof outline:
- use the fixpoint witness to cover the new visible left window;
- reduce all offset `k + 1` windows of the successor to offset `k` windows of the
  original configuration and apply `hleft`.

Proof complexity:
- medium-high; this depends on the tape-window transition lemmas but not on the
  harder matching-enumeration argument.
-/
lemma allLeftWindowsIn_of_rightStep (cfg : NGramCPSConfig) {finalState : SearchState l s}
    {A : Config l s} {pc : PartialConfig l s} {writeSym : Symbol s} {nextState : Label l}
    (hmatch : MatchesPartial cfg.n pc A)
    (hleft : AllLeftWindowsIn cfg.n finalState.leftNGrams A)
    (hfix :
      ∃ expansion,
        stepPartialConfig M finalState.leftNGrams finalState.rightNGrams pc = .advanced expansion ∧
        (∀ ng ∈ expansion.leftNGrams, ng ∈ finalState.leftNGrams) ∧
        (∀ ng ∈ expansion.rightNGrams, ng ∈ finalState.rightNGrams) ∧
        (∀ pc' ∈ expansion.successors, pc' ∈ finalState.partialConfigs))
    (hstmt : Machine.get M A.state A.tape.head = Stmt.next writeSym .right nextState) :
    AllLeftWindowsIn cfg.n finalState.leftNGrams
      { state := nextState, tape := (A.tape.write writeSym).move .right } := by
  obtain ⟨expansion, hstep, hleftExp, _hrightExp, _hsuccExp⟩ := hfix
  have hstmt' : Machine.get M pc.state pc.head = Stmt.next writeSym .right nextState := by
    simpa [MatchesPartial_state hmatch, MatchesPartial_head hmatch] using hstmt
  have hexp : expansion = expandRight finalState.rightNGrams pc writeSym nextState := by
    simpa [stepPartialConfig, hstmt'] using hstep.symm
  intro k
  cases k with
  | zero =>
      cases hcfgn : cfg.n with
      | zero =>
          simpa [leftWindowAt, hcfgn] using hleft 0
      | succ n =>
          rw [leftWindowAt_moveRight_zero_succ (l := l) (s := s) n A writeSym nextState]
          have hmem : shiftInNear writeSym pc.left ∈ finalState.leftNGrams := by
            apply hleftExp
            rw [hexp]
            simp [expandRight]
          simpa [MatchesPartial_left hmatch, hcfgn]
            using hmem
  | succ k =>
      rw [leftWindowAt_moveRight_succ (l := l) (s := s) cfg.n k A writeSym nextState]
      exact hleft k

/--
For a right-moving real machine step, all right windows of the successor remain in
the final right `n`-gram set.

Why this is correct:
- every right window of the successor is just a one-cell shift of a right window
  of the original configuration.

Proof outline:
- rewrite successor right windows as offset windows of the original configuration;
- discharge them using `hright`.

Proof complexity:
- medium; this is mostly a tape-window transport lemma.
-/
lemma allRightWindowsIn_of_rightStep (cfg : NGramCPSConfig) {finalState : SearchState l s}
    {A : Config l s} {writeSym : Symbol s} {nextState : Label l}
    (hright : AllRightWindowsIn cfg.n finalState.rightNGrams A)
    (_hstmt : Machine.get M A.state A.tape.head = Stmt.next writeSym .right nextState) :
    AllRightWindowsIn cfg.n finalState.rightNGrams
      { state := nextState, tape := (A.tape.write writeSym).move .right } := by
  intro k
  rw [rightWindowAt_moveRight (l := l) (s := s) cfg.n k A writeSym nextState]
  exact hright (k + 1)

/--
For a left-moving real machine step, the concrete successor configuration has a
stored matching `PartialConfig` in the final search state.

Why this is correct:
- this is the mirror image of the right-moving matching theorem;
- the actual far-left symbol is justified by the left-window invariant on the
  original configuration.

Proof outline:
- use the left-side offset-1 window to identify the actual far symbol;
- show that symbol appears in the `expandLeft` successor list;
- conclude that the corresponding successor partial configuration is stored and
  matches the real successor.

Proof complexity:
- high; symmetric to the right-moving theorem.
-/
lemma leftStep_has_matching_partialConfig (cfg : NGramCPSConfig) {finalState : SearchState l s}
    {A : Config l s} {pc : PartialConfig l s} {writeSym : Symbol s} {nextState : Label l}
    (hcfg : cfg.n ≠ 0)
    (hmatch : MatchesPartial cfg.n pc A)
    (hleft : AllLeftWindowsIn cfg.n finalState.leftNGrams A)
    (hfix :
      ∃ expansion,
        stepPartialConfig M finalState.leftNGrams finalState.rightNGrams pc = .advanced expansion ∧
        (∀ ng ∈ expansion.leftNGrams, ng ∈ finalState.leftNGrams) ∧
        (∀ ng ∈ expansion.rightNGrams, ng ∈ finalState.rightNGrams) ∧
        (∀ pc' ∈ expansion.successors, pc' ∈ finalState.partialConfigs))
    (hstmt : Machine.get M A.state A.tape.head = Stmt.next writeSym .left nextState) :
    ∃ pc',
      pc' ∈ finalState.partialConfigs ∧
      MatchesPartial cfg.n pc' { state := nextState, tape := (A.tape.write writeSym).move .left } := by
  obtain ⟨expansion, hstep, _hleftExp, _hrightExp, hsuccExp⟩ := hfix
  cases hcfgn : cfg.n with
  | zero =>
      exact (hcfg hcfgn).elim
  | succ n =>
      have hmatch' : MatchesPartial (n + 1) pc A := by
        simpa [hcfgn] using hmatch
      have hleft' : AllLeftWindowsIn (n + 1) finalState.leftNGrams A := by
        simpa [hcfgn] using hleft
      have hstmt' : Machine.get M pc.state pc.head = Stmt.next writeSym .left nextState := by
        simpa [MatchesPartial_state hmatch', MatchesPartial_head hmatch'] using hstmt
      have hexp : expansion = expandLeft finalState.leftNGrams pc writeSym nextState := by
        simpa [stepPartialConfig, hstmt'] using hstep.symm
      have hdrop : pc.left.drop 1 = leftWindowAt n 1 A := by
        exact leftVisibleDrop_eq_windowAt_one (l := l) (s := s) n hmatch'
      let farSym := (leftWindowAt (n + 1) 1 A).getD n default
      let pc' : PartialConfig l s := {
        left := appendFar (pc.left.drop 1) farSym
        head := pc.left.getD 0 default
        state := nextState
        right := shiftInNear writeSym pc.right
      }
      have hprefix :
          (leftWindowAt (n + 1) 1 A).take (pc.left.drop 1).size = pc.left.drop 1 := by
        rw [hdrop]
        simpa [leftWindowAt, Turing.ListBlank.take.length] using
          (leftWindowAt_one_take_succ (l := l) (s := s) n A)
      have hfarMem : farSym ∈ matchingLastSymbols (pc.left.drop 1) finalState.leftNGrams default := by
        have hmem :=
          mem_matchingLastSymbols_of_mem
            (pref := pc.left.drop 1)
            (ngrams := finalState.leftNGrams)
            (ngram := leftWindowAt (n + 1) 1 A)
            (fallback := default)
            (hmem := hleft' 1)
            hprefix
        simpa [farSym, hdrop, leftWindowAt, Turing.ListBlank.take.length] using hmem
      have hpc'Succ : pc' ∈ expansion.successors := by
        rw [hexp, expandLeft]
        refine Array.mem_map.2 ?_
        exact ⟨farSym, hfarMem, by rfl⟩
      refine ⟨pc', hsuccExp _ (by simpa [hexp] using hpc'Succ), ?_⟩
      constructor
      · rfl
      constructor
      · calc
          pc'.head = pc.left.getD 0 default := rfl
          _ = A.tape.left.head := matched_left_getD_zero_eq (l := l) (s := s) n hmatch'
          _ = ((A.tape.write writeSym).move .left).head := by simp [Turing.Tape.move, Turing.Tape.write]
      constructor
      · calc
          pc'.left = appendFar (pc.left.drop 1) farSym := rfl
          _ = appendFar (leftWindowAt n 1 A) ((leftWindowAt (n + 1) 1 A).getD n default) := by
                simp [farSym, hdrop]
          _ = leftWindowAt (n + 1) 1 A := appendFar_leftWindowAt_one_succ (l := l) (s := s) n A
          _ = leftWindowAt (n + 1) 0 { state := nextState, tape := (A.tape.write writeSym).move .left } := by
                symm
                simpa using
                  (leftWindowAt_moveLeft (l := l) (s := s) (n := n + 1) (k := 0)
                    A writeSym nextState)
      · calc
          pc'.right = shiftInNear writeSym pc.right := rfl
          _ = shiftInNear writeSym (rightWindowAt (n + 1) 0 A) := by
                rw [MatchesPartial_right hmatch']
          _ = rightWindowAt (n + 1) 0 { state := nextState, tape := (A.tape.write writeSym).move .left } := by
                symm
                simpa using
                  (rightWindowAt_moveLeft_zero_succ (l := l) (s := s) n A writeSym nextState)

/--
For a left-moving real machine step, all left windows of the successor remain in
the final left `n`-gram set.

Why this is correct:
- every left window of the successor is just a one-cell shift of a left window of
  the original configuration.

Proof outline:
- rewrite successor left windows as offset windows of the original configuration;
- discharge them using `hleft`.

Proof complexity:
- medium; this is mostly a tape-window transport lemma.
-/
lemma allLeftWindowsIn_of_leftStep (cfg : NGramCPSConfig) {finalState : SearchState l s}
    {A : Config l s} {writeSym : Symbol s} {nextState : Label l}
    (hleft : AllLeftWindowsIn cfg.n finalState.leftNGrams A)
    (_hstmt : Machine.get M A.state A.tape.head = Stmt.next writeSym .left nextState) :
    AllLeftWindowsIn cfg.n finalState.leftNGrams
      { state := nextState, tape := (A.tape.write writeSym).move .left } := by
  intro k
  rw [leftWindowAt_moveLeft (l := l) (s := s) cfg.n k A writeSym nextState]
  exact hleft (k + 1)

/--
For a left-moving real machine step, all right windows of the successor remain in
the final right `n`-gram set.

Why this is correct:
- the visible right window is exactly the right `n`-gram emitted by `expandLeft`;
- every farther-right window is an older right window of the original
  configuration, shifted by one cell.

Proof outline:
- use the fixpoint witness to cover the new visible right window;
- reduce all offset `k + 1` windows of the successor to offset `k` windows of the
  original configuration and apply `hright`.

Proof complexity:
- medium-high; this depends on the tape-window transition lemmas.
-/
lemma allRightWindowsIn_of_leftStep (cfg : NGramCPSConfig) {finalState : SearchState l s}
    {A : Config l s} {pc : PartialConfig l s} {writeSym : Symbol s} {nextState : Label l}
    (hmatch : MatchesPartial cfg.n pc A)
    (hright : AllRightWindowsIn cfg.n finalState.rightNGrams A)
    (hfix :
      ∃ expansion,
        stepPartialConfig M finalState.leftNGrams finalState.rightNGrams pc = .advanced expansion ∧
        (∀ ng ∈ expansion.leftNGrams, ng ∈ finalState.leftNGrams) ∧
        (∀ ng ∈ expansion.rightNGrams, ng ∈ finalState.rightNGrams) ∧
        (∀ pc' ∈ expansion.successors, pc' ∈ finalState.partialConfigs))
    (hstmt : Machine.get M A.state A.tape.head = Stmt.next writeSym .left nextState) :
    AllRightWindowsIn cfg.n finalState.rightNGrams
      { state := nextState, tape := (A.tape.write writeSym).move .left } := by
  obtain ⟨expansion, hstep, _hleftExp, hrightExp, _hsuccExp⟩ := hfix
  have hstmt' : Machine.get M pc.state pc.head = Stmt.next writeSym .left nextState := by
    simpa [MatchesPartial_state hmatch, MatchesPartial_head hmatch] using hstmt
  have hexp : expansion = expandLeft finalState.leftNGrams pc writeSym nextState := by
    simpa [stepPartialConfig, hstmt'] using hstep.symm
  intro k
  cases k with
  | zero =>
      cases hcfgn : cfg.n with
      | zero =>
          simpa [rightWindowAt, hcfgn] using hright 0
      | succ n =>
          rw [rightWindowAt_moveLeft_zero_succ (l := l) (s := s) n A writeSym nextState]
          have hmem : shiftInNear writeSym pc.right ∈ finalState.rightNGrams := by
            apply hrightExp
            rw [hexp]
            simp [expandLeft]
          simpa [MatchesPartial_right hmatch, hcfgn]
            using hmem
  | succ k =>
      rw [rightWindowAt_moveLeft_succ (l := l) (s := s) cfg.n k A writeSym nextState]
      exact hright k

end NGramCPS
