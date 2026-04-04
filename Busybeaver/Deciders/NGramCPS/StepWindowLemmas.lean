import Busybeaver.Deciders.NGramCPS.Windows

open TM

namespace NGramCPS

/--
When the machine writes and moves right, every right-side length-`n` window of the
successor is exactly the next right-side window of the original configuration.

Why this is correct:
- moving right shifts the head one cell to the right;
- the right tape suffix of the successor is the old right suffix with its nearest
  element removed, so all right windows shift by one offset.

Proof outline:
- unfold `rightWindowAt`;
- compare both arrays entrywise using `ListBlank.take_nth` and `ListBlank.drop_nth`.

Proof complexity:
- low-medium; a direct tape/window calculation.
-/
lemma rightWindowAt_moveRight (n k : ℕ) (A : Config l s) (writeSym : Symbol s) (nextState : Label l) :
    rightWindowAt n k { state := nextState, tape := (A.tape.write writeSym).move .right } =
      rightWindowAt n (k + 1) A := by
  apply Array.ext
  · simp [rightWindowAt, Turing.ListBlank.take.length]
  · intro i hi1 hi2
    have hi : i < n := by
      simpa [rightWindowAt, Turing.ListBlank.take.length] using hi1
    simp [rightWindowAt, Turing.Tape.move, Turing.Tape.write, Turing.ListBlank.take_nth, hi,
      Turing.ListBlank.drop_nth]

/--
When the machine writes and moves left, every left-side length-`n` window of the
successor is exactly the next left-side window of the original configuration.

Why this is correct:
- moving left shifts the head one cell to the left;
- the left tape suffix of the successor is the old left suffix with its nearest
  element removed, so all left windows shift by one offset.

Proof outline:
- unfold `leftWindowAt`;
- compare both arrays entrywise using `ListBlank.take_nth` and `ListBlank.drop_nth`.

Proof complexity:
- low-medium; a direct tape/window calculation.
-/
lemma leftWindowAt_moveLeft (n k : ℕ) (A : Config l s) (writeSym : Symbol s) (nextState : Label l) :
    leftWindowAt n k { state := nextState, tape := (A.tape.write writeSym).move .left } =
      leftWindowAt n (k + 1) A := by
  apply Array.ext
  · simp [leftWindowAt, Turing.ListBlank.take.length]
  · intro i hi1 hi2
    have hi : i < n := by
      simpa [leftWindowAt, Turing.ListBlank.take.length] using hi1
    simp [leftWindowAt, Turing.Tape.move, Turing.Tape.write, Turing.ListBlank.take_nth, hi,
      Turing.ListBlank.drop_nth]

/--
For positive window width, the visible left window after a right move is obtained
by inserting the written symbol next to the head and dropping the farthest old
left symbol.
-/
lemma leftWindowAt_moveRight_zero_succ (n : ℕ) (A : Config l s) (writeSym : Symbol s)
    (nextState : Label l) :
    leftWindowAt (n + 1) 0 { state := nextState, tape := (A.tape.write writeSym).move .right } =
      shiftInNear writeSym (leftWindowAt (n + 1) 0 A) := by
  apply Array.ext
  · simp [leftWindowAt, shiftInNear, Turing.ListBlank.take.length]
  · intro i hi1 hi2
    cases i with
    | zero =>
        simp [leftWindowAt, shiftInNear, Turing.Tape.move, Turing.Tape.write]
    | succ j =>
        have hj : j < n := by
          simpa [leftWindowAt, Turing.ListBlank.take.length] using hi1
        have hj' : j < n + 1 := Nat.lt_succ_of_lt hj
        have hpopBound : j < (leftWindowAt (n + 1) 0 A).pop.size := by
          simpa [leftWindowAt, Turing.ListBlank.take.length] using hj
        have hlhs :
            (leftWindowAt (n + 1) 0
              { state := nextState, tape := (A.tape.write writeSym).move .right })[j + 1]'hi1 =
              A.tape.left.nth j := by
          simp [leftWindowAt, Turing.Tape.move, Turing.Tape.write, Turing.ListBlank.take_nth, hj]
        have hpop :
            (leftWindowAt (n + 1) 0 A).pop[j]'hpopBound = A.tape.left.nth j := by
          rw [Array.getElem_pop]
          simpa [leftWindowAt, Turing.ListBlank.take.length] using
            (Turing.ListBlank.take_nth (Γ := Symbol s) (Lb := A.tape.left) (n := n + 1) (i := j) hj')
        have happend :
            (leftWindowAt (n + 1) 0 A).pop[j]'hpopBound =
              (shiftInNear writeSym (leftWindowAt (n + 1) 0 A))[j + 1]'hi2 := by
          change (leftWindowAt (n + 1) 0 A).pop[j]'hpopBound =
            (#[writeSym] ++ (leftWindowAt (n + 1) 0 A).pop)[j + 1]'hi2
          exact Array.getElem_append_right' #[writeSym] (ys := (leftWindowAt (n + 1) 0 A).pop)
            (i := j) hpopBound
        exact hlhs.trans (hpop.symm.trans happend)

/--
For positive window width, the visible right window after a left move is obtained
by inserting the written symbol next to the head and dropping the farthest old
right symbol.
-/
lemma rightWindowAt_moveLeft_zero_succ (n : ℕ) (A : Config l s) (writeSym : Symbol s)
    (nextState : Label l) :
    rightWindowAt (n + 1) 0 { state := nextState, tape := (A.tape.write writeSym).move .left } =
      shiftInNear writeSym (rightWindowAt (n + 1) 0 A) := by
  apply Array.ext
  · simp [rightWindowAt, shiftInNear, Turing.ListBlank.take.length]
  · intro i hi1 hi2
    cases i with
    | zero =>
        simp [rightWindowAt, shiftInNear, Turing.Tape.move, Turing.Tape.write]
    | succ j =>
        have hj : j < n := by
          simpa [rightWindowAt, Turing.ListBlank.take.length] using hi1
        have hj' : j < n + 1 := Nat.lt_succ_of_lt hj
        have hpopBound : j < (rightWindowAt (n + 1) 0 A).pop.size := by
          simpa [rightWindowAt, Turing.ListBlank.take.length] using hj
        have hlhs :
            (rightWindowAt (n + 1) 0
              { state := nextState, tape := (A.tape.write writeSym).move .left })[j + 1]'hi1 =
              A.tape.right.nth j := by
          simp [rightWindowAt, Turing.Tape.move, Turing.Tape.write, Turing.ListBlank.take_nth, hj]
        have hpop :
            (rightWindowAt (n + 1) 0 A).pop[j]'hpopBound = A.tape.right.nth j := by
          rw [Array.getElem_pop]
          simpa [rightWindowAt, Turing.ListBlank.take.length] using
            (Turing.ListBlank.take_nth (Γ := Symbol s) (Lb := A.tape.right) (n := n + 1) (i := j) hj')
        have happend :
            (rightWindowAt (n + 1) 0 A).pop[j]'hpopBound =
              (shiftInNear writeSym (rightWindowAt (n + 1) 0 A))[j + 1]'hi2 := by
          change (rightWindowAt (n + 1) 0 A).pop[j]'hpopBound =
            (#[writeSym] ++ (rightWindowAt (n + 1) 0 A).pop)[j + 1]'hi2
          exact Array.getElem_append_right' #[writeSym] (ys := (rightWindowAt (n + 1) 0 A).pop)
            (i := j) hpopBound
        exact hlhs.trans (hpop.symm.trans happend)

/--
After a right move, every non-visible left window of the successor is a one-cell
shift of a left window of the original configuration.
-/
lemma leftWindowAt_moveRight_succ (n k : ℕ) (A : Config l s) (writeSym : Symbol s)
    (nextState : Label l) :
    leftWindowAt n (k + 1) { state := nextState, tape := (A.tape.write writeSym).move .right } =
      leftWindowAt n k A := by
  apply Array.ext
  · simp [leftWindowAt, Turing.ListBlank.take.length]
  · intro i hi1 hi2
    have hi : i < n := by
      simpa [leftWindowAt, Turing.ListBlank.take.length] using hi1
    simp [leftWindowAt, Turing.Tape.move, Turing.Tape.write, Turing.ListBlank.take_nth, hi,
      Turing.ListBlank.drop_nth]

/--
After a left move, every non-visible right window of the successor is a one-cell
shift of a right window of the original configuration.
-/
lemma rightWindowAt_moveLeft_succ (n k : ℕ) (A : Config l s) (writeSym : Symbol s)
    (nextState : Label l) :
    rightWindowAt n (k + 1) { state := nextState, tape := (A.tape.write writeSym).move .left } =
      rightWindowAt n k A := by
  apply Array.ext
  · simp [rightWindowAt, Turing.ListBlank.take.length]
  · intro i hi1 hi2
    have hi : i < n := by
      simpa [rightWindowAt, Turing.ListBlank.take.length] using hi1
    simp [rightWindowAt, Turing.Tape.move, Turing.Tape.write, Turing.ListBlank.take_nth, hi,
      Turing.ListBlank.drop_nth]

end NGramCPS
