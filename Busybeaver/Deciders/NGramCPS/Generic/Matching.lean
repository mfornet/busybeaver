import Busybeaver.Deciders.NGramCPS.Generic.StepWindow
import Busybeaver.Deciders.NGramCPS.MatchingLemmas

/-!
Generic port of the window-specific lemmas in `NGramCPS.MatchingLemmas`.

The pure-array helper lemmas (`mem_matchingLastSymbols_of_mem`, `appendFar_take_getD_succ`,
`pop_eq_take_of_size_eq_succ`) are already alphabet-generic and live in namespace `NGramCPS`, so
they are reused directly; only the `leftWindowAt`/`rightWindowAt`-specific facts are re-proved
over `GConfig`.
-/

open TM.Table

namespace NGramCPS.Generic

variable {l : ℕ} {α : Type _} [Inhabited α]

lemma rightWindowAt_one_take_succ (n : ℕ) (A : GConfig l α) :
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
        (Turing.ListBlank.take_nth (Γ := α) (Lb := A.tape.right.tail) (n := n + 1) (i := i) hi')
    have hsmall :
        (A.tape.right.tail.take n)[i]'(by simpa using hi) = A.tape.right.tail.nth i := by
      simpa using
        (Turing.ListBlank.take_nth (Γ := α) (Lb := A.tape.right.tail) (n := n) (i := i) hi)
    simpa [rightWindowAt, Array.take_eq_extract] using hlarge.trans hsmall.symm

lemma leftWindowAt_one_take_succ (n : ℕ) (A : GConfig l α) :
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
        (Turing.ListBlank.take_nth (Γ := α) (Lb := A.tape.left.tail) (n := n + 1) (i := i) hi')
    have hsmall :
        (A.tape.left.tail.take n)[i]'(by simpa using hi) = A.tape.left.tail.nth i := by
      simpa using
        (Turing.ListBlank.take_nth (Γ := α) (Lb := A.tape.left.tail) (n := n) (i := i) hi)
    simpa [leftWindowAt, Array.take_eq_extract] using hlarge.trans hsmall.symm

lemma rightVisibleDrop_eq_windowAt_one (n : ℕ) {nl : ℕ} {A : GConfig l α} {pc : PartialConfig l α}
    (hmatch : MatchesPartial nl (n + 1) pc A) :
    pc.right.drop 1 = rightWindowAt n 1 A := by
  rw [MatchesPartial_right hmatch]
  apply Array.ext
  · simp [rightWindowAt, Array.drop_eq_extract, Turing.ListBlank.take.length]
  · intro i hi1 hi2
    have hi : i < n := by
      simpa [rightWindowAt, Array.drop_eq_extract, Turing.ListBlank.take.length] using hi1
    simp [rightWindowAt, Array.drop_eq_extract, hi, Turing.ListBlank.take_nth]

lemma leftVisibleDrop_eq_windowAt_one (n : ℕ) {nr : ℕ} {A : GConfig l α} {pc : PartialConfig l α}
    (hmatch : MatchesPartial (n + 1) nr pc A) :
    pc.left.drop 1 = leftWindowAt n 1 A := by
  rw [MatchesPartial_left hmatch]
  apply Array.ext
  · simp [leftWindowAt, Array.drop_eq_extract, Turing.ListBlank.take.length]
  · intro i hi1 hi2
    have hi : i < n := by
      simpa [leftWindowAt, Array.drop_eq_extract, Turing.ListBlank.take.length] using hi1
    simp [leftWindowAt, Array.drop_eq_extract, hi, Turing.ListBlank.take_nth]

lemma matched_right_getD_zero_eq (n : ℕ) {nl : ℕ} {A : GConfig l α} {pc : PartialConfig l α}
    (hmatch : MatchesPartial nl (n + 1) pc A) :
    pc.right.getD 0 default = A.tape.right.head := by
  rw [MatchesPartial_right hmatch, Array.getD_eq_getD_getElem?]
  rw [Array.getElem?_eq_getElem]
  · simp [rightWindowAt]
  · simp [rightWindowAt, Turing.ListBlank.take.length]

lemma matched_left_getD_zero_eq (n : ℕ) {nr : ℕ} {A : GConfig l α} {pc : PartialConfig l α}
    (hmatch : MatchesPartial (n + 1) nr pc A) :
    pc.left.getD 0 default = A.tape.left.head := by
  rw [MatchesPartial_left hmatch, Array.getD_eq_getD_getElem?]
  rw [Array.getElem?_eq_getElem]
  · simp [leftWindowAt]
  · simp [leftWindowAt, Turing.ListBlank.take.length]

lemma appendFar_rightWindowAt_one_succ (n : ℕ) (A : GConfig l α) :
    NGramCPS.appendFar (rightWindowAt n 1 A) ((rightWindowAt (n + 1) 1 A).getD n default) =
      rightWindowAt (n + 1) 1 A := by
  have hbase :=
    NGramCPS.appendFar_take_getD_succ (xs := rightWindowAt (n + 1) 1 A) (n := n)
      (fallback := default)
      (by simp [rightWindowAt, Turing.ListBlank.take.length])
  rw [rightWindowAt_one_take_succ n A] at hbase
  exact hbase

lemma appendFar_leftWindowAt_one_succ (n : ℕ) (A : GConfig l α) :
    NGramCPS.appendFar (leftWindowAt n 1 A) ((leftWindowAt (n + 1) 1 A).getD n default) =
      leftWindowAt (n + 1) 1 A := by
  have hbase :=
    NGramCPS.appendFar_take_getD_succ (xs := leftWindowAt (n + 1) 1 A) (n := n)
      (fallback := default)
      (by simp [leftWindowAt, Turing.ListBlank.take.length])
  rw [leftWindowAt_one_take_succ n A] at hbase
  exact hbase

end NGramCPS.Generic
