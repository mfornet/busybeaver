import Busybeaver.Deciders.NGramCPS.Basic

open TM

namespace NGramCPS

/--
Length-`n` left-side window at offset `k`, stored in the same head-facing
convention as `PartialConfig.left`.
-/
def leftWindowAt (n k : ℕ) (C : Config l s) : NGram s :=
  ((C.tape.left.drop k).take n).toArray

/--
Length-`n` right-side window at offset `k`, stored in the same head-facing
convention as `PartialConfig.right`.
-/
def rightWindowAt (n k : ℕ) (C : Config l s) : NGram s :=
  ((C.tape.right.drop k).take n).toArray

/-- `pc` matches the currently visible centered window of `C`. -/
def MatchesPartial (n : ℕ) (pc : PartialConfig l s) (C : Config l s) : Prop :=
  pc.state = C.state ∧
  pc.head = C.tape.head ∧
  pc.left = leftWindowAt n 0 C ∧
  pc.right = rightWindowAt n 0 C

def AllLeftWindowsIn (n : ℕ) (ngrams : Array (NGram s)) (C : Config l s) : Prop :=
  ∀ k, leftWindowAt n k C ∈ ngrams

def AllRightWindowsIn (n : ℕ) (ngrams : Array (NGram s)) (C : Config l s) : Prop :=
  ∀ k, rightWindowAt n k C ∈ ngrams

def Base (n : ℕ) (finalState : SearchState l s) (C : Config l s) : Prop :=
  (∃ pc, pc ∈ finalState.partialConfigs ∧ MatchesPartial n pc C) ∧
  AllLeftWindowsIn n finalState.leftNGrams C ∧
  AllRightWindowsIn n finalState.rightNGrams C

@[simp] lemma blank_leftWindowAt (n k : ℕ) :
    leftWindowAt (l := l) (s := s) n k init = Array.replicate n (default : Symbol s) := by
  let C : Config l s := init
  apply Array.ext
  · simp [leftWindowAt, Turing.ListBlank.take.length]
  · intro i hi1 hi2
    have hi : i < n := by
      simpa [leftWindowAt, Turing.ListBlank.take.length] using hi1
    simpa [leftWindowAt, Turing.ListBlank.drop_nth] using
      (Turing.ListBlank.take_nth (Γ := Symbol s) (Lb := C.tape.left.drop k) (n := n) (i := i) hi)

@[simp] lemma blank_rightWindowAt (n k : ℕ) :
    rightWindowAt (l := l) (s := s) n k init = Array.replicate n (default : Symbol s) := by
  let C : Config l s := init
  apply Array.ext
  · simp [rightWindowAt, Turing.ListBlank.take.length]
  · intro i hi1 hi2
    have hi : i < n := by
      simpa [rightWindowAt, Turing.ListBlank.take.length] using hi1
    simpa [rightWindowAt, Turing.ListBlank.drop_nth] using
      (Turing.ListBlank.take_nth (Γ := Symbol s) (Lb := C.tape.right.drop k) (n := n) (i := i) hi)

@[simp] lemma MatchesPartial_state {n : ℕ} {pc : PartialConfig l s} {C : Config l s}
    (h : MatchesPartial n pc C) : pc.state = C.state := h.1

@[simp] lemma MatchesPartial_head {n : ℕ} {pc : PartialConfig l s} {C : Config l s}
    (h : MatchesPartial n pc C) : pc.head = C.tape.head := h.2.1

@[simp] lemma MatchesPartial_left {n : ℕ} {pc : PartialConfig l s} {C : Config l s}
    (h : MatchesPartial n pc C) : pc.left = leftWindowAt n 0 C := h.2.2.1

@[simp] lemma MatchesPartial_right {n : ℕ} {pc : PartialConfig l s} {C : Config l s}
    (h : MatchesPartial n pc C) : pc.right = rightWindowAt n 0 C := h.2.2.2

end NGramCPS
