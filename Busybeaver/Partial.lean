/-
Definitions for "partial tapes" and tape patterns.

Here, we use directed head notation for convenience.
-/
import Busybeaver.Basic

namespace TM

inductive PartialHTape (Γ) [Inhabited Γ] where
| finite : List Γ → PartialHTape Γ
| infinite : Turing.ListBlank Γ → PartialHTape Γ
deriving DecidableEq

structure PartialTape (Γ) [Inhabited Γ] where
  dir: Turing.Dir
  left: PartialHTape Γ
  right: PartialHTape Γ
deriving DecidableEq

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

lemma nonempty.of_some_head {T: PartialHTape Γ} (h: T.head? = some g): T.nonempty :=
by cases T with
| finite L => {
  simp [nonempty]
  cases L with simp [head?] at h
  | cons head tail => simp
}
| infinite L => simp [nonempty]

lemma nonempty.head?_eq_some_heqd {T: PartialHTape Γ} (h: T.nonempty): T.head? = some (T.head h) :=
by cases T with simp [head?, head]
| finite L => exact List.head?_eq_head h

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

@[simp]
instance: EmptyCollection (PartialHTape Γ) := ⟨.finite []⟩

@[simp]
def append (L: List Γ): PartialHTape Γ → PartialHTape Γ
| .finite L' => L ++ L'
| .infinite L' => L ++ L'

@[simp]
instance: HAppend (List Γ) (PartialHTape Γ) (PartialHTape Γ) := ⟨append⟩

@[simp]
lemma append_nil {T: PartialHTape Γ}: ([]: List Γ) ++ T = T :=
by induction T with simp [instHAppendList, append]
| infinite L => simp [Turing.ListBlank.instHAppend]


def infty: PartialHTape Γ := PartialHTape.infinite (default: Turing.ListBlank Γ)

@[simp]
lemma infinite_mk_eq_apend {L: List Γ}: PartialHTape.infinite (Turing.ListBlank.mk L) = L ++ (infty (Γ:=Γ)) :=
by {
  simp [instHAppendList, append, infty]
  apply Turing.ListBlank.ext
  intro n
  simp
  split
  · rename_i heq
    rw [List.getI_eq_getElem L heq]
  · apply List.getI_eq_default
    simp at *
    trivial
}

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
deriving DecidableEq

notation L " {" C ":" D "} " R => PartialConfig.mk C (PartialTape.mk D L R)
notation L " <{" C "} " R => PartialConfig.mk C (PartialTape.mk Turing.Dir.left L R)
notation L " {" C "}> " R => PartialConfig.mk C (PartialTape.mk Turing.Dir.right L R)

namespace Machine

variable {M: Machine l s}

def pstep (M: Machine l s) (C: PartialConfig l s): Option (PartialConfig l s) := do
  let Chead ← C.tape.head?
  match M C.state Chead with
  | .halt => .none
  | .next sym' dir lab' => .some { state := lab', tape := (← (C.tape.write sym').move? dir) }

notation A " p-["M"]-> " B => Machine.pstep M A = Option.some B

inductive MultiPStep (M: Machine l s): ℕ → PartialConfig l s → PartialConfig l s → Prop where
| refl (C: PartialConfig l s): MultiPStep M 0 C C
| step A B C n: (A p-[M]-> B) → MultiPStep M n B C → MultiPStep M n.succ A C

notation A " p-[" M "]{" n "}-> " B => MultiPStep M n A B

def MultiPStep.refl' (hAB: A = B): A p-[M]{0}-> B :=
by {
  rw [hAB]
  exact .refl _
}

instance MultiPStep.instTrans: Trans (MultiPStep M n) (MultiPStep M n') (MultiPStep M (n + n')) :=
by {
  constructor
  intro A B C hAB hBC
  induction hAB with
  | refl => {
    simp
    exact hBC
  }
  | step A B' C' n hAB' _ IH => {
    specialize IH hBC
    conv in n.succ + n' =>
      simp
      rw [Nat.add_assoc, Nat.add_comm 1, ← Nat.add_assoc, ← Nat.succ_eq_add_one]
    apply MultiPStep.step A B' C (n + n') hAB' IH
  }
}

lemma MultiPStep.single (h: A p-[M]-> B): A p-[M]{1}-> B := by {
  apply MultiPStep.step A B B
  · exact h
  · exact .refl B
}

lemma step.pointed_valid (h: A p-[M]-> B): A.tape.pointed.nonempty :=
by {
  simp [pstep, Option.bind] at h
  split at h
  · cases h
  rename_i heq
  exact PartialHTape.nonempty.of_some_head heq
}

/-
lemma MultiPStep.locality_left_empty {L R L' R': List (Symbol s)} {T: PartialHTape (Symbol s)}
  (h: ({} {q:dir} R) p-[M]{n}-> (L' {q':dir'} R')):
  ((L ++ T) {q:dir} R) p-[M]{n}-> ((L' ++ T) {q':dir'} R') :=
by induction L with
| nil => {
  cases T with
  | finite L => {
    induction L with
    | nil => {
      simp
      exact h
    }
    | cons head tail IH => {
      
    }
  }
}
-/

lemma step.finiteness_left
  (h: A p-[M]-> B):
    A.tape.left.is_infinite ↔ B.tape.left.is_infinite := sorry

lemma step.finiteness_right
  (h: A p-[M]-> B):
    A.tape.right.is_infinite ↔ B.tape.right.is_infinite := sorry

lemma step.locality {L R L' R': List (Symbol s)} {T T': PartialHTape (Symbol s)}
  (h: (L {q:dir} R) p-[M]-> (L' {q':dir'} R')):
  ((L ++ T) {q:dir} R ++ T') p-[M]-> ((L' ++ T) {q':dir'} R' ++ T') :=
by {
  sorry
}

/--
A "locality" lemma for transitions on partial configurations.

If we can step from a given partial configuration to another, expanding this configuration on either
sides does not matter.

This is the key lemma to build inductive proofs about TMs, reasonning on incresingly complex
patterns of partial configurations.
-/
lemma MultiPStep.locality {L R L' R': List (Symbol s)} {T T': PartialHTape (Symbol s)} {q: Label l} {dir dir': Turing.Dir}
  (h: (L {q:dir} R) p-[M]{n}-> (L' {q':dir'} R')):
    ((L ++ T) {q:dir} R ++ T') p-[M]{n}-> ((L' ++ T) {q':dir'} R' ++ T') :=
by induction n generalizing L R L' R' q q' dir dir' with
| zero => {
  cases h
  exact .refl _
}
| succ n IH => {
  cases h
  rename_i I hI hIn
  obtain ⟨q'', dir'', L'', R''⟩ := I
  have hL'': ¬L''.is_infinite := by {
    have hI' := step.finiteness_left hI
    simp at hI'
    exact hI'
  }

  have hR'': ¬R''.is_infinite := by {
    have hI' := step.finiteness_right hI
    simp at hI'
    exact hI'
  }

  cases L''
  swap
  · simp at hL''
  rename_i Li
  cases R''
  swap
  · simp at hR''
  rename_i Ri

  apply MultiPStep.step _ _ _ _ (step.locality hI) (IH hIn)
}

section Example

def tmpMach: Machine 4 2
| 0, 0 => .next 1 .right 1
| 0, 1 => .next 0 .right 2
| 1, 0 => .next 0 .left 2
| 1, 1 => .halt
| 2, 0 => .next 1 .right 3
| 2, 1 => .next 1 .right 2
| 3, 0 => .next 0 .left 4
| 3, 1 => .next 1 .right 0
| 4, 0 => .next 1 .right 3
| 4, 1 => .next 1 .left 4
| _, _ => sorry

lemma onestep: ({} {2}> [(1: Symbol 2)]) p-[tmpMach]-> ([(1: Symbol 2)] {2}> {}) :=
by decide

example: ({} {2}> List.replicate n (1: Symbol 2)) p-[tmpMach]{n}-> ((List.replicate n (1: Symbol 2)) {2}> {}) :=
by induction n with
| zero => {
  simp
  exact .refl _
}
| succ n IH => {
  have htmp := by {
  calc ({} {2}> List.replicate (n+1) (1: Symbol 2))
    _ p-[tmpMach]{0}-> ({} {2}> ([(1: Symbol 2)] ++ List.replicate n (1: Symbol 2))) := by {
      apply MultiPStep.refl'
      simp
      rfl
    }
    _ p-[tmpMach]{1}-> ([(1: Symbol 2)] {2}> (List.replicate n (1: Symbol 2))) := by {
      have htmp := step.locality onestep (T:=PartialHTape.finite []) (T':=(List.replicate n (1: Symbol 2)))
      simp at htmp
      simp
      exact MultiPStep.single htmp
    }
    _ p-[tmpMach]{n}-> ((List.replicate n (1: Symbol 2) ++ [(1: Symbol 2)]) {2}> {}) := by {
      have htmp := MultiPStep.locality IH (T:=[(1:Symbol 2)]) (T':={})
      simp at htmp
      simp
      exact htmp
    }
    _ p-[tmpMach]{0}-> ((List.replicate (n+1) (1: Symbol 2)) {2}> {}) := by {
      apply MultiPStep.refl'
      simp
      symm
      exact List.replicate_succ' n 1
    }
  }
  simp at htmp
  simp
  rw [Nat.add_comm n] at *
  exact htmp
}

end Example

