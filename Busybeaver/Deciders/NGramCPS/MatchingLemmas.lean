import Busybeaver.Deciders.NGramCPS.StepWindowLemmas

open TM

namespace NGramCPS

/--
If a concrete `n`-gram is present in the known set and has the requested prefix,
its last symbol is one of the candidates returned by `matchingLastSymbols`.

Why this is correct:
- `matchingLastSymbols` is just `filterMap` over the known `n`-grams;
- the witness `ngram` survives the filter because its prefix matches.

Proof complexity:
- low; a direct unfolding of `matchingLastSymbols`.
-/
lemma mem_matchingLastSymbols_of_mem [DecidableEq α]
    {pref : Array α} {ngrams : Array (Array α)} {ngram : Array α} {fallback : α}
    (hmem : ngram ∈ ngrams)
    (hprefix : ngram.take pref.size = pref) :
    ngram.getD pref.size fallback ∈ matchingLastSymbols pref ngrams fallback := by
  unfold matchingLastSymbols
  exact Array.mem_filterMap.2 ⟨ngram, hmem, by simp [hprefix]⟩

/--
For an array of size `n + 1`, popping its last element agrees with taking its
length-`n` prefix.

Why this is correct:
- both arrays have size `n`;
- on indices `< n`, both operations simply return the original array entry.

Proof complexity:
- medium; a direct array-extensionality argument.
-/
lemma pop_eq_take_of_size_eq_succ (xs : Array α) (n : ℕ) (hsize : xs.size = n + 1) :
    xs.pop = xs.take n := by
  apply Array.ext
  · simp [hsize]
  · intro i hi1 hi2
    have hix : i < xs.size := by
      simpa [hsize] using Nat.lt_succ_of_lt (by simpa [hsize] using hi1)
    have hpop : xs.pop[i]'hi1 = xs[i]'hix := by
      rw [Array.getElem_pop]
    have htake : (xs.take n)[i]'hi2 = xs[i]'hix := by
      simpa [Array.take_eq_extract] using
        (Array.getElem_extract (xs := xs) (start := 0) (stop := n) (i := i)
          (h := by simpa [Array.take_eq_extract] using hi2))
    exact hpop.trans htake.symm

/--
Appending the element read at index `n` reconstructs any array of size `n + 1`
from its length-`n` prefix.

Why this is correct:
- `appendFar` is array append with a singleton;
- the left branch covers indices `< n`, and the last index is exactly `n`.

Proof complexity:
- medium; a reusable array-extensionality fact.
-/
lemma appendFar_take_getD_succ (xs : Array α) (n : ℕ) (fallback : α)
    (hsize : xs.size = n + 1) :
    appendFar (xs.take n) (xs.getD n fallback) = xs := by
  have hne : xs.size ≠ 0 := by
    simp [hsize]
  letI : Inhabited α := ⟨fallback⟩
  calc
    appendFar (xs.take n) (xs.getD n fallback)
        = (xs.take n).push (xs.getD n fallback) := by
            rw [appendFar]
            symm
            exact List.push_toArray (xs.take n).toList (xs.getD n fallback)
    _ = xs.pop.push xs.back! := by
          rw [pop_eq_take_of_size_eq_succ xs n hsize]
          have hback : xs.back! = xs.getD n fallback := by
            rw [Array.back!_eq_back?, Array.back?_eq_getElem?]
            simpa [hsize]
          rw [hback]
    _ = xs := by
          simpa using (Array.eq_push_pop_back!_of_size_ne_zero (α := α) hne).symm

lemma rightWindowAt_one_take_succ (n : ℕ) (A : Config l s) :
    (rightWindowAt (n + 1) 1 A).take n = rightWindowAt n 1 A := by
  apply Array.ext
  · simp [rightWindowAt, Turing.ListBlank.take.length]
  · intro i hi1 hi2
    have hi : i < n := by
      simpa [rightWindowAt, Turing.ListBlank.take.length] using hi1
    have hi' : i < n + 1 := Nat.lt_succ_of_lt hi
    have hlarge :
        (A.tape.right.tail.take (n + 1))[i]'(by simpa using hi') = A.tape.right.tail.nth i := by
      simpa using
        (Turing.ListBlank.take_nth (Γ := Symbol s) (Lb := A.tape.right.tail) (n := n + 1) (i := i)
          hi')
    have hsmall :
        (A.tape.right.tail.take n)[i]'(by simpa using hi) = A.tape.right.tail.nth i := by
      simpa using
        (Turing.ListBlank.take_nth (Γ := Symbol s) (Lb := A.tape.right.tail) (n := n) (i := i) hi)
    simpa [rightWindowAt, Array.take_eq_extract] using hlarge.trans hsmall.symm

lemma leftWindowAt_one_take_succ (n : ℕ) (A : Config l s) :
    (leftWindowAt (n + 1) 1 A).take n = leftWindowAt n 1 A := by
  apply Array.ext
  · simp [leftWindowAt, Turing.ListBlank.take.length]
  · intro i hi1 hi2
    have hi : i < n := by
      simpa [leftWindowAt, Turing.ListBlank.take.length] using hi1
    have hi' : i < n + 1 := Nat.lt_succ_of_lt hi
    have hlarge :
        (A.tape.left.tail.take (n + 1))[i]'(by simpa using hi') = A.tape.left.tail.nth i := by
      simpa using
        (Turing.ListBlank.take_nth (Γ := Symbol s) (Lb := A.tape.left.tail) (n := n + 1) (i := i)
          hi')
    have hsmall :
        (A.tape.left.tail.take n)[i]'(by simpa using hi) = A.tape.left.tail.nth i := by
      simpa using
        (Turing.ListBlank.take_nth (Γ := Symbol s) (Lb := A.tape.left.tail) (n := n) (i := i) hi)
    simpa [leftWindowAt, Array.take_eq_extract] using hlarge.trans hsmall.symm

/--
For a positive visible window, dropping the nearest right symbol from the current
visible window exposes exactly the length-`n` right window at offset `1`.
-/
lemma rightVisibleDrop_eq_windowAt_one (n : ℕ) {A : Config l s} {pc : PartialConfig l s}
    (hmatch : MatchesPartial (n + 1) pc A) :
    pc.right.drop 1 = rightWindowAt n 1 A := by
  rw [MatchesPartial_right hmatch]
  apply Array.ext
  · simp [rightWindowAt, Array.drop_eq_extract, Turing.ListBlank.take.length]
  · intro i hi1 hi2
    have hi : i < n := by
      simpa [rightWindowAt, Array.drop_eq_extract, Turing.ListBlank.take.length] using hi1
    simp [rightWindowAt, Array.drop_eq_extract, Array.getElem_extract, hi,
      Turing.ListBlank.take_nth, Turing.ListBlank.drop_nth]

/--
For a positive visible window, dropping the nearest left symbol from the current
visible window exposes exactly the length-`n` left window at offset `1`.
-/
lemma leftVisibleDrop_eq_windowAt_one (n : ℕ) {A : Config l s} {pc : PartialConfig l s}
    (hmatch : MatchesPartial (n + 1) pc A) :
    pc.left.drop 1 = leftWindowAt n 1 A := by
  rw [MatchesPartial_left hmatch]
  apply Array.ext
  · simp [leftWindowAt, Array.drop_eq_extract, Turing.ListBlank.take.length]
  · intro i hi1 hi2
    have hi : i < n := by
      simpa [leftWindowAt, Array.drop_eq_extract, Turing.ListBlank.take.length] using hi1
    simp [leftWindowAt, Array.drop_eq_extract, Array.getElem_extract, hi,
      Turing.ListBlank.take_nth, Turing.ListBlank.drop_nth]

/--
For a positive matched window, the nearest visible symbol on the right agrees with
the real right-side tape symbol adjacent to the head.

Why this is correct:
- `MatchesPartial` identifies `pc.right` with the visible right window;
- at width `n + 1`, index `0` of that window is exactly the nearest right symbol.

Proof complexity:
- low-medium; a direct calculation with `rightWindowAt` and `ListBlank.take_nth`.
-/
lemma matched_right_getD_zero_eq (n : ℕ) {A : Config l s} {pc : PartialConfig l s}
    (hmatch : MatchesPartial (n + 1) pc A) :
    pc.right.getD 0 default = A.tape.right.head := by
  rw [MatchesPartial_right hmatch, Array.getD_eq_getD_getElem?]
  rw [Array.getElem?_eq_getElem]
  · simpa [rightWindowAt, Turing.ListBlank.take_nth, Turing.ListBlank.drop_nth,
      Turing.ListBlank.nth_zero]
  · simp [rightWindowAt, Turing.ListBlank.take.length]

/--
For a positive matched window, the nearest visible symbol on the left agrees with
the real left-side tape symbol adjacent to the head.

Why this is correct:
- this is the left/right mirror of `matched_right_getD_zero_eq`;
- `MatchesPartial` identifies `pc.left` with the visible left window.

Proof complexity:
- low-medium; symmetric to the right-side version.
-/
lemma matched_left_getD_zero_eq (n : ℕ) {A : Config l s} {pc : PartialConfig l s}
    (hmatch : MatchesPartial (n + 1) pc A) :
    pc.left.getD 0 default = A.tape.left.head := by
  rw [MatchesPartial_left hmatch, Array.getD_eq_getD_getElem?]
  rw [Array.getElem?_eq_getElem]
  · simpa [leftWindowAt, Turing.ListBlank.take_nth, Turing.ListBlank.drop_nth,
      Turing.ListBlank.nth_zero]
  · simp [leftWindowAt, Turing.ListBlank.take.length]

lemma appendFar_rightWindowAt_one_succ (n : ℕ) (A : Config l s) :
    appendFar (rightWindowAt n 1 A) ((rightWindowAt (n + 1) 1 A).getD n default) =
      rightWindowAt (n + 1) 1 A := by
  have hbase :=
    appendFar_take_getD_succ (xs := rightWindowAt (n + 1) 1 A) (n := n) (fallback := default)
      (by simp [rightWindowAt, Turing.ListBlank.take.length])
  simpa [rightWindowAt_one_take_succ (l := l) (s := s) n A] using hbase

lemma appendFar_leftWindowAt_one_succ (n : ℕ) (A : Config l s) :
    appendFar (leftWindowAt n 1 A) ((leftWindowAt (n + 1) 1 A).getD n default) =
      leftWindowAt (n + 1) 1 A := by
  have hbase :=
    appendFar_take_getD_succ (xs := leftWindowAt (n + 1) 1 A) (n := n) (fallback := default)
      (by simp [leftWindowAt, Turing.ListBlank.take.length])
  simpa [leftWindowAt_one_take_succ (l := l) (s := s) n A] using hbase

end NGramCPS
