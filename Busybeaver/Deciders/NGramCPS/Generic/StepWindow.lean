import Busybeaver.Deciders.NGramCPS.Generic.Windows

/-!
Generic port of `NGramCPS.StepWindowLemmas`: how tape windows transform under a single
`gstep`-style move, over an arbitrary alphabet `α`.
-/

open TM.Table

namespace NGramCPS.Generic

variable {l : ℕ} {α : Type _} [Inhabited α]

lemma rightWindowAt_moveRight (n k : ℕ) (A : GConfig l α) (writeSym : α) (nextState : Label l) :
    rightWindowAt n k { state := nextState, tape := (A.tape.write writeSym).move .right } =
      rightWindowAt n (k + 1) A := by
  apply Array.ext
  · simp [rightWindowAt, Turing.ListBlank.take.length]
  · intro i hi1 hi2
    have hi : i < n := by
      simpa [rightWindowAt, Turing.ListBlank.take.length] using hi1
    simp [rightWindowAt, Turing.Tape.move, Turing.Tape.write, Turing.ListBlank.take_nth, hi,
      Turing.ListBlank.drop_nth]

lemma leftWindowAt_moveLeft (n k : ℕ) (A : GConfig l α) (writeSym : α) (nextState : Label l) :
    leftWindowAt n k { state := nextState, tape := (A.tape.write writeSym).move .left } =
      leftWindowAt n (k + 1) A := by
  apply Array.ext
  · simp [leftWindowAt, Turing.ListBlank.take.length]
  · intro i hi1 hi2
    have hi : i < n := by
      simpa [leftWindowAt, Turing.ListBlank.take.length] using hi1
    simp [leftWindowAt, Turing.Tape.move, Turing.Tape.write, Turing.ListBlank.take_nth, hi,
      Turing.ListBlank.drop_nth]

lemma leftWindowAt_moveRight_zero_succ (n : ℕ) (A : GConfig l α) (writeSym : α)
    (nextState : Label l) :
    leftWindowAt (n + 1) 0 { state := nextState, tape := (A.tape.write writeSym).move .right } =
      NGramCPS.shiftInNear writeSym (leftWindowAt (n + 1) 0 A) := by
  apply Array.ext
  · simp [leftWindowAt, NGramCPS.shiftInNear, Turing.ListBlank.take.length]
  · intro i hi1 hi2
    cases i with
    | zero =>
        simp [leftWindowAt, NGramCPS.shiftInNear, Turing.Tape.move, Turing.Tape.write]
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
            (Turing.ListBlank.take_nth (Γ := α) (Lb := A.tape.left) (n := n + 1) (i := j) hj')
        have happend :
            (leftWindowAt (n + 1) 0 A).pop[j]'hpopBound =
              (NGramCPS.shiftInNear writeSym (leftWindowAt (n + 1) 0 A))[j + 1]'hi2 := by
          change (leftWindowAt (n + 1) 0 A).pop[j]'hpopBound =
            (#[writeSym] ++ (leftWindowAt (n + 1) 0 A).pop)[j + 1]'hi2
          exact Array.getElem_append_right' #[writeSym] (ys := (leftWindowAt (n + 1) 0 A).pop)
            (i := j) hpopBound
        exact hlhs.trans (hpop.symm.trans happend)

lemma rightWindowAt_moveLeft_zero_succ (n : ℕ) (A : GConfig l α) (writeSym : α)
    (nextState : Label l) :
    rightWindowAt (n + 1) 0 { state := nextState, tape := (A.tape.write writeSym).move .left } =
      NGramCPS.shiftInNear writeSym (rightWindowAt (n + 1) 0 A) := by
  apply Array.ext
  · simp [rightWindowAt, NGramCPS.shiftInNear, Turing.ListBlank.take.length]
  · intro i hi1 hi2
    cases i with
    | zero =>
        simp [rightWindowAt, NGramCPS.shiftInNear, Turing.Tape.move, Turing.Tape.write]
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
            (Turing.ListBlank.take_nth (Γ := α) (Lb := A.tape.right) (n := n + 1) (i := j) hj')
        have happend :
            (rightWindowAt (n + 1) 0 A).pop[j]'hpopBound =
              (NGramCPS.shiftInNear writeSym (rightWindowAt (n + 1) 0 A))[j + 1]'hi2 := by
          change (rightWindowAt (n + 1) 0 A).pop[j]'hpopBound =
            (#[writeSym] ++ (rightWindowAt (n + 1) 0 A).pop)[j + 1]'hi2
          exact Array.getElem_append_right' #[writeSym] (ys := (rightWindowAt (n + 1) 0 A).pop)
            (i := j) hpopBound
        exact hlhs.trans (hpop.symm.trans happend)

lemma leftWindowAt_moveRight_succ (n k : ℕ) (A : GConfig l α) (writeSym : α)
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

lemma rightWindowAt_moveLeft_succ (n k : ℕ) (A : GConfig l α) (writeSym : α)
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

end NGramCPS.Generic
