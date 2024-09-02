/-
Definitions for "partial tapes" and tape patterns.

Here, we use directed head notation for convenience.
-/
import Busybeaver.Basic

namespace TM

inductive PartialHTape (Γ) [Inhabited Γ] where
| finite : List Γ → PartialHTape Γ
| infinite : Turing.ListBlank Γ → PartialHTape Γ

structure PartialTape (Γ) [Inhabited Γ] where
  dir: Turing.Dir
  left: PartialHTape Γ
  right: PartialHTape Γ

variable {Γ} [Inhabited Γ]

namespace PartialHTape

def is_infinite: PartialHTape Γ → Prop
| finite _ => False
| infinite _ => True

/-
Coercion and lifting operations on partial half tapes for convenience.
-/
instance: Coe (List Γ) (PartialHTape Γ) := ⟨PartialHTape.finite⟩
instance: Coe (Turing.ListBlank Γ) (PartialHTape Γ) := ⟨PartialHTape.infinite⟩

def to_blank (T: PartialHTape Γ) (hT: T.is_infinite): Turing.ListBlank Γ := match T with
| finite _ => by simp [is_infinite] at hT
| infinite L => L

@[simp]
lemma coe.blank_infinite {L: Turing.ListBlank Γ}: is_infinite (Γ:=Γ) ↑L :=
  by simp [is_infinite]

@[simp]
lemma coe.to_blank {L: Turing.ListBlank Γ}: to_blank ↑L coe.blank_infinite = L :=
  by simp [TM.PartialHTape.to_blank]

@[simp]
lemma coe.infinite {L: PartialHTape Γ} (hL: L.is_infinite): (PartialHTape.to_blank L hL) = L :=
by {
  simp [PartialHTape.to_blank]
  simp [is_infinite] at hL
  split at hL <;> {
    simp at hL
    try simp
  }
}

instance: CanLift (PartialHTape Γ) (Turing.ListBlank Γ) (↑) PartialHTape.is_infinite where
  prf T hT := by {
    use T.to_blank hT
    simp
  }

instance: CanLift (PartialHTape Γ) (List Γ) (↑) (¬PartialHTape.is_infinite ·) where
  prf T hT := by cases T with simp [is_infinite] at hT
    | finite L => use L

end PartialHTape

namespace PartialTape

def directize (T: Turing.Tape Γ) (dir: Turing.Dir := .right): {T : PartialTape Γ // T.dir = dir} := match dir with
| .left => ⟨{ dir := .left, left := Turing.ListBlank.cons T.head T.left, right := T.right }, rfl⟩
| .right => ⟨{ dir := .right, left := T.left, right := Turing.ListBlank.cons T.head T.right }, rfl⟩

def is_infinite (T: PartialTape Γ): Prop := T.left.is_infinite ∧ T.right.is_infinite

lemma directize.infinite {T: Turing.Tape Γ} {dir: Turing.Dir}: (directize T dir).val.is_infinite :=
  by cases dir <;> simp [directize, is_infinite]

def undirectize (T: PartialTape Γ) (hT: T.is_infinite): Turing.Tape Γ :=
  let left: Turing.ListBlank Γ := T.left.to_blank (by {
    simp [is_infinite] at hT
    exact hT.left
  })
  let right: Turing.ListBlank Γ := T.right.to_blank (by {
    simp [is_infinite] at hT
    exact hT.right
  })
  match T.dir with
  | .left => { head := left.head, left := left.tail, right }
  | .right => { head := right.head, left, right := right.tail }

@[simp]
lemma directize.undirectize {dir: Turing.Dir} {T: Turing.Tape Γ}: (directize T dir).val.undirectize directize.infinite = T :=
  by cases dir <;> simp [TM.PartialTape.undirectize, directize]

@[simp]
lemma undirectize.directize {T: PartialTape Γ} (hT: T.is_infinite): directize (undirectize T hT) T.dir = ⟨T, rfl⟩ :=
by {
  simp [undirectize]
  obtain ⟨Td, Tl, Tr⟩ := T
  simp [is_infinite] at hT
  split <;> {
    rename_i heq
    cases heq
    simp [PartialTape.directize]
  }
}

instance {dir: Turing.Dir}: CanLift {T: PartialTape Γ // T.dir = dir} (Turing.Tape Γ) (λ T ↦ directize T dir) (λ T ↦ T.val.is_infinite) where
  prf T hT := by {
    obtain ⟨T, hTdir⟩ := T
    simp_all
    use T.undirectize hT
    cases hTdir
    simp
  }

end PartialTape
