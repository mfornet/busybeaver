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
lemma coe.list_infinite {L: List Γ}: ¬(is_infinite (Γ:=Γ) ↑L) :=
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

def nonempty: PartialHTape Γ → Prop
| .finite L => L ≠ []
| .infinite _ => True

def is_infinite.nonempty {T: PartialHTape Γ} (hT: T.is_infinite): T.nonempty :=
by {
  cases T
  · simp at hT
  · simp [PartialHTape.nonempty]
}

def head?: PartialHTape Γ → Option Γ
| .finite L => L.head?
| .infinite L => L.head

def head (T: PartialHTape Γ) (hT: T.nonempty): Γ := match T with
| .finite L => L.head (by {
  simp [nonempty] at hT
  exact hT
})
| .infinite L => L.head

def cons (A: Γ) (L: PartialHTape Γ): PartialHTape Γ := match L with
| .finite L => A :: L
| .infinite L => Turing.ListBlank.cons A L

lemma cons.nonempty {L: PartialHTape Γ}: (PartialHTape.cons A L).nonempty :=
  by cases L <;> simp [cons, PartialHTape.nonempty]

def cons.infinite_iff {L: PartialHTape Γ}: (PartialHTape.cons A L).is_infinite ↔ L.is_infinite :=
  by cases L <;> simp [cons]

@[simp]
def cons.head {L: PartialHTape Γ}: (cons A L).head cons.nonempty = A :=
  by cases L <;> simp [cons, PartialHTape.head]

def tail: PartialHTape Γ → PartialHTape Γ
| .finite L => L.tail
| .infinite L => L.tail

@[simp]
def cons.tail {L: PartialHTape Γ}: (cons A L).tail = L :=
  by cases L <;> simp [cons, PartialHTape.tail]

@[simp]
lemma cons_head_tail {L: PartialHTape Γ} (hT: L.nonempty): cons (L.head hT) L.tail = L :=
  by cases L <;> simp [head, tail, cons]

end PartialHTape

namespace PartialTape

def directize (T: Turing.Tape Γ) (dir: Turing.Dir := .right): {T : PartialTape Γ // T.dir = dir} := match dir with
| .left => ⟨{ dir := .left, left := Turing.ListBlank.cons T.head T.left, right := T.right }, rfl⟩
| .right => ⟨{ dir := .right, left := T.left, right := Turing.ListBlank.cons T.head T.right }, rfl⟩

def is_infinite (T: PartialTape Γ): Prop := T.left.is_infinite ∧ T.right.is_infinite

def is_infinite.left {T: PartialTape Γ} (hT: T.is_infinite): T.left.is_infinite := by {
  unfold is_infinite at hT
  exact hT.left
}

def is_infinite.right {T: PartialTape Γ} (hT: T.is_infinite): T.right.is_infinite := by {
  unfold is_infinite at hT
  exact hT.right
}

lemma directize.infinite {T: Turing.Tape Γ} {dir: Turing.Dir}: (directize T dir).val.is_infinite :=
  by cases dir <;> simp [directize, is_infinite]

def undirectize (T: PartialTape Γ) (hT: T.is_infinite): Turing.Tape Γ :=
  let left: Turing.ListBlank Γ := T.left.to_blank hT.left
  let right: Turing.ListBlank Γ := T.right.to_blank hT.right
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

def pointed (T: PartialTape Γ): PartialHTape Γ := match T.dir with
| .left => T.left
| .right => T.right

def head? (T: PartialTape Γ): Option Γ := T.pointed.head?

def head (T: PartialTape Γ) (hT: T.pointed.nonempty): Γ := T.pointed.head hT

def move? (T: PartialTape Γ) (dir: Turing.Dir): Option (PartialTape Γ) :=
  match T.dir, dir with
  | .left, .right | .right, .left => .some {T with dir := dir}
  | .right, .right => match T.right.head? with
    | .none => .none
    | .some he => .some { dir := .right, left := PartialHTape.cons he T.left, right := T.right.tail }
  | .left, .left => match T.left.head? with
    | .none => .none
    | .some he => .some { dir := .left, left := T.left.tail, right := PartialHTape.cons he T.right }

def move (T: PartialTape Γ) (hT: T.is_infinite) (dir: Turing.Dir): PartialTape Γ :=
  match T.dir, dir with
  | .left, .right | .right, .left => {T with dir := dir}
  | .right, .right => { dir := .right, left := PartialHTape.cons (T.right.head hT.right.nonempty) T.left, right := T.right.tail }
  | .left, .left => { dir := .left, left := T.left.tail, right := PartialHTape.cons (T.left.head hT.left.nonempty) T.right }

/--
This is mainly a sanity check: moving an Turing.Tape hidden as a PartialTape is the same as moving
the original tape.
-/
lemma move.directize {dir dir': Turing.Dir} {T: Turing.Tape Γ}:
  (PartialTape.directize T dir').val.move directize.infinite dir = (PartialTape.directize (T.move dir) dir).val :=
by {
 match dir', dir with
 | .left, .right | .right, .left => {
  simp [PartialTape.directize, PartialTape.move, Turing.Tape.move]
 }
 | .right, .right | .left, .left => {
  simp [PartialTape.directize, PartialTape.move, Turing.Tape.move, PartialHTape.head, PartialHTape.cons, PartialHTape.tail]
 }
}

def write (T: PartialTape Γ) (sym: Γ): PartialTape Γ := match T.dir with
| .left => { T with left := PartialHTape.cons sym T.left.tail }
| .right => { T with right := PartialHTape.cons sym T.right.tail }

lemma write.directize {T: Turing.Tape Γ}:
  (PartialTape.directize T dir').val.write sym = (PartialTape.directize (T.write sym) dir').val :=
by {
  cases dir' <;> {
    simp [PartialTape.directize, PartialTape.write, PartialHTape.tail]
    simp [Turing.Tape.write, PartialHTape.cons]
  }
}

end PartialTape

structure PartialConfig (l s) where
  state: Label l
  tape: PartialTape (Symbol s)

namespace Machine

variable {M: Machine l s}

def peval (M: Machine l s) (C: PartialConfig l s): Option (PartialConfig l s) := do
  let Chead ← C.tape.head?
  match M C.state Chead with
  | .halt => .none
  | .next sym' dir lab' => .some { state := lab', tape := (← C.tape.move? dir).write sym' }
