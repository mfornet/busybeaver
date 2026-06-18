import Busybeaver.Deciders.NGramCPS.Basic

/-!
Generic (alphabet-parametric) tape windows and the `Base` closure predicate.

This mirrors `NGramCPS.Windows` but over an arbitrary alphabet `α` and the abstract one-step
relation `gstep tm` induced by a `Transition l α`. Window sizes are tracked separately on the
left (`nl`) and right (`nr`), matching the generic search's `initialState left right`.
-/

open TM.Table

namespace NGramCPS.Generic

variable {l : ℕ} {α : Type _} [Inhabited α]

/-- A full configuration over the augmented alphabet `α`. -/
structure GConfig (l : ℕ) (α : Type _) [Inhabited α] where
  state : Label l
  tape : Turing.Tape α

instance : Inhabited (GConfig l α) := ⟨⟨default, default⟩⟩

/-- The blank initial configuration over `α`. -/
def ginit : GConfig l α := ⟨default, default⟩

/-- One abstract machine step driven by `tm`. -/
def gstep (tm : Transition l α) (C : GConfig l α) : Option (GConfig l α) :=
  match tm C.state C.tape.head with
  | none => none
  | some (writeSym, dir, nextState) =>
      some { state := nextState, tape := (C.tape.write writeSym).move dir }

/-- Length-`n` left-side window at offset `k`, head-facing order. -/
def leftWindowAt (n k : ℕ) (C : GConfig l α) : Array α :=
  ((C.tape.left.drop k).take n).toArray

/-- Length-`n` right-side window at offset `k`, head-facing order. -/
def rightWindowAt (n k : ℕ) (C : GConfig l α) : Array α :=
  ((C.tape.right.drop k).take n).toArray

/-- `pc` matches the currently visible centered windows of `C`. -/
def MatchesPartial (nl nr : ℕ) (pc : PartialConfig l α) (C : GConfig l α) : Prop :=
  pc.state = C.state ∧
  pc.head = C.tape.head ∧
  pc.left = leftWindowAt nl 0 C ∧
  pc.right = rightWindowAt nr 0 C

def AllLeftWindowsIn (n : ℕ) (ngrams : Array (Array α)) (C : GConfig l α) : Prop :=
  ∀ k, leftWindowAt n k C ∈ ngrams

def AllRightWindowsIn (n : ℕ) (ngrams : Array (Array α)) (C : GConfig l α) : Prop :=
  ∀ k, rightWindowAt n k C ∈ ngrams

/-- The closure predicate certified by a successful generic search. -/
def Base (nl nr : ℕ) (finalState : SearchState l α) (C : GConfig l α) : Prop :=
  (∃ pc, pc ∈ finalState.partialConfigs ∧ MatchesPartial nl nr pc C) ∧
  AllLeftWindowsIn nl finalState.leftNGrams C ∧
  AllRightWindowsIn nr finalState.rightNGrams C

@[simp] lemma blank_leftWindowAt (n k : ℕ) :
    leftWindowAt n k (ginit : GConfig l α) = Array.replicate n (default : α) := by
  apply Array.ext
  · simp [leftWindowAt, ginit, Turing.ListBlank.take.length]
  · intro i hi1 hi2
    have hi : i < n := by
      simpa [leftWindowAt, ginit, Turing.ListBlank.take.length] using hi1
    simpa [leftWindowAt, ginit, Turing.ListBlank.drop_nth] using
      (Turing.ListBlank.take_nth (Γ := α)
        (Lb := (ginit : GConfig l α).tape.left.drop k) (n := n) (i := i) hi)

@[simp] lemma blank_rightWindowAt (n k : ℕ) :
    rightWindowAt n k (ginit : GConfig l α) = Array.replicate n (default : α) := by
  apply Array.ext
  · simp [rightWindowAt, ginit, Turing.ListBlank.take.length]
  · intro i hi1 hi2
    have hi : i < n := by
      simpa [rightWindowAt, ginit, Turing.ListBlank.take.length] using hi1
    simpa [rightWindowAt, ginit, Turing.ListBlank.drop_nth] using
      (Turing.ListBlank.take_nth (Γ := α)
        (Lb := (ginit : GConfig l α).tape.right.drop k) (n := n) (i := i) hi)

@[simp] lemma MatchesPartial_state {nl nr : ℕ} {pc : PartialConfig l α} {C : GConfig l α}
    (h : MatchesPartial nl nr pc C) : pc.state = C.state := h.1

@[simp] lemma MatchesPartial_head {nl nr : ℕ} {pc : PartialConfig l α} {C : GConfig l α}
    (h : MatchesPartial nl nr pc C) : pc.head = C.tape.head := h.2.1

@[simp] lemma MatchesPartial_left {nl nr : ℕ} {pc : PartialConfig l α} {C : GConfig l α}
    (h : MatchesPartial nl nr pc C) : pc.left = leftWindowAt nl 0 C := h.2.2.1

@[simp] lemma MatchesPartial_right {nl nr : ℕ} {pc : PartialConfig l α} {C : GConfig l α}
    (h : MatchesPartial nl nr pc C) : pc.right = rightWindowAt nr 0 C := h.2.2.2

end NGramCPS.Generic
