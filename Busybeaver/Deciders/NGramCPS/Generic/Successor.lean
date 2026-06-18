import Busybeaver.Deciders.NGramCPS.Generic.Matching

/-!
Generic port of `NGramCPS.SuccessorBaseLemmas`: for a single `gstep` move, the concrete
successor configuration stays inside the final `Base` predicate.

Window sizes are tracked separately (`nl` on the left, `nr` on the right). Both are assumed
nonzero, which is exactly what a successful generic search guarantees (the search returns
`.timeout` whenever `left = 0` or `right = 0`).
-/

open TM.Table

namespace NGramCPS.Generic

variable {l : ℕ} {α : Type _} [Inhabited α] [DecidableEq α] {tm : Transition l α}

/-- For a right move, the concrete successor has a stored matching `PartialConfig`. -/
lemma rightStep_has_matching_partialConfig {nl nr : ℕ} {finalState : SearchState l α}
    {A : GConfig l α} {pc : PartialConfig l α} {writeSym : α} {nextState : Label l}
    (hnl : nl ≠ 0) (hnr : nr ≠ 0)
    (hmatch : MatchesPartial nl nr pc A)
    (hright : AllRightWindowsIn nr finalState.rightNGrams A)
    (hfix :
      ∃ expansion,
        stepPartialConfig tm finalState.leftNGrams finalState.rightNGrams pc = .advanced expansion ∧
        (∀ ng ∈ expansion.leftNGrams, ng ∈ finalState.leftNGrams) ∧
        (∀ ng ∈ expansion.rightNGrams, ng ∈ finalState.rightNGrams) ∧
        (∀ pc' ∈ expansion.successors, pc' ∈ finalState.partialConfigs))
    (hstmt : tm A.state A.tape.head = some (writeSym, .right, nextState)) :
    ∃ pc',
      pc' ∈ finalState.partialConfigs ∧
      MatchesPartial nl nr pc'
        { state := nextState, tape := (A.tape.write writeSym).move .right } := by
  obtain ⟨expansion, hstep, _hleftExp, _hrightExp, hsuccExp⟩ := hfix
  obtain ⟨nl', rfl⟩ := Nat.exists_eq_succ_of_ne_zero hnl
  obtain ⟨nr', rfl⟩ := Nat.exists_eq_succ_of_ne_zero hnr
  have hstmt' : tm pc.state pc.head = some (writeSym, .right, nextState) := by
    rw [MatchesPartial_state hmatch, MatchesPartial_head hmatch]; exact hstmt
  have hexp : expansion = expandRight finalState.rightNGrams pc writeSym nextState := by
    simpa [stepPartialConfig, hstmt'] using hstep.symm
  have hdrop : pc.right.drop 1 = rightWindowAt nr' 1 A :=
    rightVisibleDrop_eq_windowAt_one nr' hmatch
  let farSym := (rightWindowAt (nr' + 1) 1 A).getD nr' default
  let pc' : PartialConfig l α := {
    left := NGramCPS.shiftInNear writeSym pc.left
    head := pc.right.getD 0 default
    state := nextState
    right := NGramCPS.appendFar (pc.right.drop 1) farSym
  }
  have hprefix :
      (rightWindowAt (nr' + 1) 1 A).take (pc.right.drop 1).size = pc.right.drop 1 := by
    rw [hdrop]
    simpa [rightWindowAt, Turing.ListBlank.take.length] using
      (rightWindowAt_one_take_succ nr' A)
  have hfarMem :
      farSym ∈ NGramCPS.matchingLastSymbols (pc.right.drop 1) finalState.rightNGrams default := by
    have hmem :=
      NGramCPS.mem_matchingLastSymbols_of_mem
        (pref := pc.right.drop 1) (ngrams := finalState.rightNGrams)
        (ngram := rightWindowAt (nr' + 1) 1 A) (fallback := default)
        (hmem := hright 1) hprefix
    simpa [farSym, hdrop, rightWindowAt, Turing.ListBlank.take.length] using hmem
  have hpc'Succ : pc' ∈ expansion.successors := by
    rw [hexp, expandRight]
    refine Array.mem_map.2 ?_
    exact ⟨farSym, hfarMem, by rfl⟩
  refine ⟨pc', hsuccExp _ (by simpa [hexp] using hpc'Succ), ?_, ?_, ?_, ?_⟩
  · rfl
  · calc
      pc'.head = pc.right.getD 0 default := rfl
      _ = A.tape.right.head := matched_right_getD_zero_eq nr' hmatch
      _ = ((A.tape.write writeSym).move .right).head := by
            simp [Turing.Tape.move, Turing.Tape.write]
  · calc
      pc'.left = NGramCPS.shiftInNear writeSym pc.left := rfl
      _ = NGramCPS.shiftInNear writeSym (leftWindowAt (nl' + 1) 0 A) := by
            rw [MatchesPartial_left hmatch]
      _ = leftWindowAt (nl' + 1) 0
            { state := nextState, tape := (A.tape.write writeSym).move .right } := by
            symm
            simpa using (leftWindowAt_moveRight_zero_succ nl' A writeSym nextState)
  · calc
      pc'.right = NGramCPS.appendFar (pc.right.drop 1) farSym := rfl
      _ = NGramCPS.appendFar (rightWindowAt nr' 1 A)
            ((rightWindowAt (nr' + 1) 1 A).getD nr' default) := by simp [farSym, hdrop]
      _ = rightWindowAt (nr' + 1) 1 A := appendFar_rightWindowAt_one_succ nr' A
      _ = rightWindowAt (nr' + 1) 0
            { state := nextState, tape := (A.tape.write writeSym).move .right } := by
            symm
            simpa using (rightWindowAt_moveRight (n := nr' + 1) (k := 0) A writeSym nextState)

/-- For a right move, all left windows of the successor remain in the final left set. -/
lemma allLeftWindowsIn_of_rightStep {nl nr : ℕ} {finalState : SearchState l α}
    {A : GConfig l α} {pc : PartialConfig l α} {writeSym : α} {nextState : Label l}
    (hnl : nl ≠ 0)
    (hmatch : MatchesPartial nl nr pc A)
    (hleft : AllLeftWindowsIn nl finalState.leftNGrams A)
    (hfix :
      ∃ expansion,
        stepPartialConfig tm finalState.leftNGrams finalState.rightNGrams pc = .advanced expansion ∧
        (∀ ng ∈ expansion.leftNGrams, ng ∈ finalState.leftNGrams) ∧
        (∀ ng ∈ expansion.rightNGrams, ng ∈ finalState.rightNGrams) ∧
        (∀ pc' ∈ expansion.successors, pc' ∈ finalState.partialConfigs))
    (hstmt : tm A.state A.tape.head = some (writeSym, .right, nextState)) :
    AllLeftWindowsIn nl finalState.leftNGrams
      { state := nextState, tape := (A.tape.write writeSym).move .right } := by
  obtain ⟨expansion, hstep, hleftExp, _hrightExp, _hsuccExp⟩ := hfix
  have hstmt' : tm pc.state pc.head = some (writeSym, .right, nextState) := by
    rw [MatchesPartial_state hmatch, MatchesPartial_head hmatch]; exact hstmt
  have hexp : expansion = expandRight finalState.rightNGrams pc writeSym nextState := by
    simpa [stepPartialConfig, hstmt'] using hstep.symm
  obtain ⟨nl', rfl⟩ := Nat.exists_eq_succ_of_ne_zero hnl
  intro k
  cases k with
  | zero =>
      rw [leftWindowAt_moveRight_zero_succ nl' A writeSym nextState]
      have hmem : NGramCPS.shiftInNear writeSym pc.left ∈ finalState.leftNGrams := by
        apply hleftExp
        rw [hexp]
        simp [expandRight]
      simpa [MatchesPartial_left hmatch] using hmem
  | succ k =>
      rw [leftWindowAt_moveRight_succ (nl' + 1) k A writeSym nextState]
      exact hleft k

omit [DecidableEq α] in
/-- For a right move, all right windows of the successor remain in the final right set. -/
lemma allRightWindowsIn_of_rightStep {nr : ℕ} {finalState : SearchState l α}
    {A : GConfig l α} {writeSym : α} {nextState : Label l}
    (hright : AllRightWindowsIn nr finalState.rightNGrams A)
    (_hstmt : tm A.state A.tape.head = some (writeSym, .right, nextState)) :
    AllRightWindowsIn nr finalState.rightNGrams
      { state := nextState, tape := (A.tape.write writeSym).move .right } := by
  intro k
  rw [rightWindowAt_moveRight nr k A writeSym nextState]
  exact hright (k + 1)

/-- For a left move, the concrete successor has a stored matching `PartialConfig`. -/
lemma leftStep_has_matching_partialConfig {nl nr : ℕ} {finalState : SearchState l α}
    {A : GConfig l α} {pc : PartialConfig l α} {writeSym : α} {nextState : Label l}
    (hnl : nl ≠ 0) (hnr : nr ≠ 0)
    (hmatch : MatchesPartial nl nr pc A)
    (hleft : AllLeftWindowsIn nl finalState.leftNGrams A)
    (hfix :
      ∃ expansion,
        stepPartialConfig tm finalState.leftNGrams finalState.rightNGrams pc = .advanced expansion ∧
        (∀ ng ∈ expansion.leftNGrams, ng ∈ finalState.leftNGrams) ∧
        (∀ ng ∈ expansion.rightNGrams, ng ∈ finalState.rightNGrams) ∧
        (∀ pc' ∈ expansion.successors, pc' ∈ finalState.partialConfigs))
    (hstmt : tm A.state A.tape.head = some (writeSym, .left, nextState)) :
    ∃ pc',
      pc' ∈ finalState.partialConfigs ∧
      MatchesPartial nl nr pc'
        { state := nextState, tape := (A.tape.write writeSym).move .left } := by
  obtain ⟨expansion, hstep, _hleftExp, _hrightExp, hsuccExp⟩ := hfix
  obtain ⟨nl', rfl⟩ := Nat.exists_eq_succ_of_ne_zero hnl
  obtain ⟨nr', rfl⟩ := Nat.exists_eq_succ_of_ne_zero hnr
  have hstmt' : tm pc.state pc.head = some (writeSym, .left, nextState) := by
    rw [MatchesPartial_state hmatch, MatchesPartial_head hmatch]; exact hstmt
  have hexp : expansion = expandLeft finalState.leftNGrams pc writeSym nextState := by
    simpa [stepPartialConfig, hstmt'] using hstep.symm
  have hdrop : pc.left.drop 1 = leftWindowAt nl' 1 A :=
    leftVisibleDrop_eq_windowAt_one nl' hmatch
  let farSym := (leftWindowAt (nl' + 1) 1 A).getD nl' default
  let pc' : PartialConfig l α := {
    left := NGramCPS.appendFar (pc.left.drop 1) farSym
    head := pc.left.getD 0 default
    state := nextState
    right := NGramCPS.shiftInNear writeSym pc.right
  }
  have hprefix :
      (leftWindowAt (nl' + 1) 1 A).take (pc.left.drop 1).size = pc.left.drop 1 := by
    rw [hdrop]
    simpa [leftWindowAt, Turing.ListBlank.take.length] using
      (leftWindowAt_one_take_succ nl' A)
  have hfarMem :
      farSym ∈ NGramCPS.matchingLastSymbols (pc.left.drop 1) finalState.leftNGrams default := by
    have hmem :=
      NGramCPS.mem_matchingLastSymbols_of_mem
        (pref := pc.left.drop 1) (ngrams := finalState.leftNGrams)
        (ngram := leftWindowAt (nl' + 1) 1 A) (fallback := default)
        (hmem := hleft 1) hprefix
    simpa [farSym, hdrop, leftWindowAt, Turing.ListBlank.take.length] using hmem
  have hpc'Succ : pc' ∈ expansion.successors := by
    rw [hexp, expandLeft]
    refine Array.mem_map.2 ?_
    exact ⟨farSym, hfarMem, by rfl⟩
  refine ⟨pc', hsuccExp _ (by simpa [hexp] using hpc'Succ), ?_, ?_, ?_, ?_⟩
  · rfl
  · calc
      pc'.head = pc.left.getD 0 default := rfl
      _ = A.tape.left.head := matched_left_getD_zero_eq nl' hmatch
      _ = ((A.tape.write writeSym).move .left).head := by
            simp [Turing.Tape.move, Turing.Tape.write]
  · calc
      pc'.left = NGramCPS.appendFar (pc.left.drop 1) farSym := rfl
      _ = NGramCPS.appendFar (leftWindowAt nl' 1 A)
            ((leftWindowAt (nl' + 1) 1 A).getD nl' default) := by simp [farSym, hdrop]
      _ = leftWindowAt (nl' + 1) 1 A := appendFar_leftWindowAt_one_succ nl' A
      _ = leftWindowAt (nl' + 1) 0
            { state := nextState, tape := (A.tape.write writeSym).move .left } := by
            symm
            simpa using (leftWindowAt_moveLeft (n := nl' + 1) (k := 0) A writeSym nextState)
  · calc
      pc'.right = NGramCPS.shiftInNear writeSym pc.right := rfl
      _ = NGramCPS.shiftInNear writeSym (rightWindowAt (nr' + 1) 0 A) := by
            rw [MatchesPartial_right hmatch]
      _ = rightWindowAt (nr' + 1) 0
            { state := nextState, tape := (A.tape.write writeSym).move .left } := by
            symm
            simpa using (rightWindowAt_moveLeft_zero_succ nr' A writeSym nextState)

omit [DecidableEq α] in
/-- For a left move, all left windows of the successor remain in the final left set. -/
lemma allLeftWindowsIn_of_leftStep {nl : ℕ} {finalState : SearchState l α}
    {A : GConfig l α} {writeSym : α} {nextState : Label l}
    (hleft : AllLeftWindowsIn nl finalState.leftNGrams A)
    (_hstmt : tm A.state A.tape.head = some (writeSym, .left, nextState)) :
    AllLeftWindowsIn nl finalState.leftNGrams
      { state := nextState, tape := (A.tape.write writeSym).move .left } := by
  intro k
  rw [leftWindowAt_moveLeft nl k A writeSym nextState]
  exact hleft (k + 1)

/-- For a left move, all right windows of the successor remain in the final right set. -/
lemma allRightWindowsIn_of_leftStep {nl nr : ℕ} {finalState : SearchState l α}
    {A : GConfig l α} {pc : PartialConfig l α} {writeSym : α} {nextState : Label l}
    (hnr : nr ≠ 0)
    (hmatch : MatchesPartial nl nr pc A)
    (hright : AllRightWindowsIn nr finalState.rightNGrams A)
    (hfix :
      ∃ expansion,
        stepPartialConfig tm finalState.leftNGrams finalState.rightNGrams pc = .advanced expansion ∧
        (∀ ng ∈ expansion.leftNGrams, ng ∈ finalState.leftNGrams) ∧
        (∀ ng ∈ expansion.rightNGrams, ng ∈ finalState.rightNGrams) ∧
        (∀ pc' ∈ expansion.successors, pc' ∈ finalState.partialConfigs))
    (hstmt : tm A.state A.tape.head = some (writeSym, .left, nextState)) :
    AllRightWindowsIn nr finalState.rightNGrams
      { state := nextState, tape := (A.tape.write writeSym).move .left } := by
  obtain ⟨expansion, hstep, _hleftExp, hrightExp, _hsuccExp⟩ := hfix
  have hstmt' : tm pc.state pc.head = some (writeSym, .left, nextState) := by
    rw [MatchesPartial_state hmatch, MatchesPartial_head hmatch]; exact hstmt
  have hexp : expansion = expandLeft finalState.leftNGrams pc writeSym nextState := by
    simpa [stepPartialConfig, hstmt'] using hstep.symm
  obtain ⟨nr', rfl⟩ := Nat.exists_eq_succ_of_ne_zero hnr
  intro k
  cases k with
  | zero =>
      rw [rightWindowAt_moveLeft_zero_succ nr' A writeSym nextState]
      have hmem : NGramCPS.shiftInNear writeSym pc.right ∈ finalState.rightNGrams := by
        apply hrightExp
        rw [hexp]
        simp [expandLeft]
      simpa [MatchesPartial_right hmatch] using hmem
  | succ k =>
      rw [rightWindowAt_moveLeft_succ (nr' + 1) k A writeSym nextState]
      exact hright k

end NGramCPS.Generic
