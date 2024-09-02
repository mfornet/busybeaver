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

def is_infinite: PartialHTape Γ → Bool
| finite _ => false
| infinite _ => true

attribute [coe] PartialHTape.finite
attribute [coe] PartialHTape.infinite

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

instance: CanLift (PartialHTape Γ) (Turing.ListBlank Γ) (↑) (λ T ↦ PartialHTape.is_infinite T) where
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

def is_infinite.nonempty {T: PartialHTape Γ} (hT: T.is_infinite = true): T.nonempty :=
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

lemma nonempty.head?_eq_some_head {T: PartialHTape Γ} (h: T.nonempty): T.head? = some (T.head h) :=
by cases T with simp [head?, head]
| finite L => exact List.head?_eq_head h

def cons (A: Γ) (L: PartialHTape Γ): PartialHTape Γ := match L with
| .finite L => A :: L
| .infinite L => Turing.ListBlank.cons A L

@[simp]
lemma cons.nonempty {L: PartialHTape Γ}: (PartialHTape.cons A L).nonempty :=
  by cases L <;> simp [cons, PartialHTape.nonempty]

@[simp]
def cons.infinite_iff {L: PartialHTape Γ}: (PartialHTape.cons A L).is_infinite = L.is_infinite :=
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
def tail.infinite {L: PartialHTape Γ}: L.tail.is_infinite = L.is_infinite :=
by cases L <;> simp [tail]

@[simp]
instance: EmptyCollection (PartialHTape Γ) := ⟨.finite []⟩

def append (L: List Γ): PartialHTape Γ → PartialHTape Γ
| .finite L' => L ++ L'
| .infinite L' => L ++ L'

instance: HAppend (List Γ) (PartialHTape Γ) (PartialHTape Γ) := ⟨append⟩

@[simp]
lemma append_nil {T: PartialHTape Γ}: ([]: List Γ) ++ T = T :=
by induction T with simp [instHAppendList, append]
| infinite L => simp [Turing.ListBlank.instHAppend]

@[simp]
lemma append_nil_end {L: List Γ}: L ++ (.finite []: PartialHTape Γ) = L :=
by simp [instHAppendList, append]

@[simp]
lemma append_empty_end {L: List Γ}: L ++ ({}: PartialHTape Γ) = L :=
  by simp

@[simp]
lemma append_lists {L R: List Γ}: PartialHTape.finite (L ++ R) = L ++ (PartialHTape.finite R) :=
  by simp [instHAppendList, append]

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

inductive Finiteness where
| finite
| half
| infinite

def finiteness (T: PartialTape Γ): Finiteness :=
  match T.left.is_infinite, T.right.is_infinite with
  | true, true => .infinite
  | false, false => .finite
  | false, true | true, false => .half

def is_infinite (T: PartialTape Γ): Prop := T.finiteness = .infinite

@[simp]
lemma finiteness.eq_finite {T: PartialTape Γ}: (T.finiteness = .finite) ↔ (¬T.left.is_infinite ∧ ¬T.right.is_infinite) :=
by {
  simp [finiteness]
  split <;> simp_all
}

@[simp]
lemma finiteness.eq_infinite {T: PartialTape Γ}: (T.finiteness = .infinite) ↔ (T.left.is_infinite ∧ T.right.is_infinite) :=
by {
  simp [finiteness]
  split <;> simp_all
}

def is_infinite.left {T: PartialTape Γ} (hT: T.is_infinite): T.left.is_infinite := by {
  unfold is_infinite at hT
  simp [finiteness] at hT
  split at hT <;> simp_all
}

def is_infinite.right {T: PartialTape Γ} (hT: T.is_infinite): T.right.is_infinite := by {
  unfold is_infinite at hT
  simp [finiteness] at hT
  split at hT <;> simp_all
}

lemma directize.infinite {T: Turing.Tape Γ} {dir: Turing.Dir}: (directize T dir).val.is_infinite :=
  by cases dir <;> simp [directize, finiteness, is_infinite]

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

def well_formed (T: PartialTape Γ): Prop := T.pointed.nonempty


def infinite.well_formed {T: PartialTape Γ} (hT: T.is_infinite): T.well_formed :=
by {
  cases hT': T.dir <;> {
    simp [PartialTape.well_formed, pointed, hT']
    first
    | exact PartialHTape.is_infinite.nonempty hT.left
    | exact PartialHTape.is_infinite.nonempty hT.right
  }
}

lemma directize.well_formed {T: Turing.Tape Γ} {dir: Turing.Dir}: (directize T dir).val.well_formed :=
by {
  apply infinite.well_formed
  exact infinite
}

def head? (T: PartialTape Γ): Option Γ := T.pointed.head?

def head (T: PartialTape Γ) (hT: T.well_formed): Γ := T.pointed.head hT

lemma head?.wf_eq_some_head {T: PartialTape Γ} (hT: T.well_formed): T.head? = some (T.head hT) :=
by {
  simp [head?, head]
  simp [well_formed] at hT
  exact PartialHTape.nonempty.head?_eq_some_head hT
}

def move? (T: PartialTape Γ) (dir: Turing.Dir): Option (PartialTape Γ) :=
  match T.dir, dir with
  | .left, .right | .right, .left => .some {T with dir := dir}
  | .right, .right => match T.right.head? with
    | .none => .none
    | .some he => .some { dir := .right, left := PartialHTape.cons he T.left, right := T.right.tail }
  | .left, .left => match T.left.head? with
    | .none => .none
    | .some he => .some { dir := .left, left := T.left.tail, right := PartialHTape.cons he T.right }

def move (T: PartialTape Γ) (hT: T.well_formed) (dir: Turing.Dir): PartialTape Γ :=
  match T.dir, dir with
  | .left, .right | .right, .left => {T with dir := dir}
  | .right, .right => { dir := .right, left := PartialHTape.cons (T.head hT) T.left, right := T.right.tail }
  | .left, .left => { dir := .left, left := T.left.tail, right := PartialHTape.cons (T.head hT) T.right }

/--
This is mainly a sanity check: moving an Turing.Tape hidden as a PartialTape is the same as moving
the original tape.
-/
lemma move.directize {dir dir': Turing.Dir} {T: Turing.Tape Γ}:
  (PartialTape.directize T dir').val.move directize.well_formed dir = (PartialTape.directize (T.move dir) dir).val :=
by {
 match dir', dir with
 | .left, .right | .right, .left => {
  simp [PartialTape.directize, PartialTape.move, Turing.Tape.move]
 }
 | .right, .right | .left, .left => {
  simp [PartialTape.directize, PartialTape.move, Turing.Tape.move, PartialTape.head, PartialTape.pointed, PartialHTape.head, PartialHTape.cons, PartialHTape.tail]
 }
}

lemma move?.well_formed_eq_move {dir: Turing.Dir} {T: PartialTape Γ} (hT: T.well_formed): T.move? dir = some (T.move hT dir) :=
by {
  simp [move?]
  split <;> {
    simp [move, *]
    try {
      rename_i heq
      simp [well_formed, pointed, heq] at hT
      rw [PartialHTape.nonempty.head?_eq_some_head hT]
      simp [PartialTape.head, pointed, heq]
    }
  }
}

@[simp]
def move.infinite {T: PartialTape Γ} {hT: T.well_formed} {dir: Turing.Dir}: (T.move hT dir).finiteness = T.finiteness :=
by {
  simp [move]
  split <;> simp [finiteness]
}

def write (T: PartialTape Γ) (sym: Γ): PartialTape Γ := match T.dir with
| .left => { T with left := PartialHTape.cons sym T.left.tail }
| .right => { T with right := PartialHTape.cons sym T.right.tail }

lemma write.well_formed {T: PartialTape Γ} (hT: T.well_formed): (T.write sym).well_formed :=
by {
  simp [PartialTape.write]
  split <;> {
    rename_i heq
    simp [PartialTape.well_formed, pointed, heq] at hT
    simp [PartialTape.well_formed, pointed, heq]
  }
}

lemma write.directize {T: Turing.Tape Γ}:
  (PartialTape.directize T dir').val.write sym = (PartialTape.directize (T.write sym) dir').val :=
by {
  cases dir' <;> {
    simp [PartialTape.directize, PartialTape.write, PartialHTape.tail]
    simp [Turing.Tape.write, PartialHTape.cons]
  }
}

@[simp]
lemma write.dir {T: PartialTape Γ}: (T.write sym).dir = T.dir :=
by {
  simp [PartialTape.write]
  split <;> rfl
}

@[simp]
lemma write.infinite {T: PartialTape Γ}: (T.write sym).finiteness = T.finiteness :=
by {
  simp [write]
  split <;> simp [finiteness]
}

end PartialTape

structure PartialConfig (l s) where
  state: Label l
  tape: PartialTape (Symbol s)
deriving DecidableEq

section Delab

notation L " {" C ";" D "} " R => PartialConfig.mk C (PartialTape.mk D L R)
notation L " <{" C "} " R => PartialConfig.mk C (PartialTape.mk Turing.Dir.left L R)
notation L " {" C "}> " R => PartialConfig.mk C (PartialTape.mk Turing.Dir.right L R)

open Lean PrettyPrinter Delaborator SubExpr

@[app_unexpander PartialConfig.mk]
def PartialConfig.unexp : Unexpander
| `($_ $state { dir := Turing.Dir.left, left := $L, right := $R }) => `(($L) <{$state} ($R))
| `($_ $state { dir := Turing.Dir.right, left := $L, right := $R }) => `(($L) {$state}> ($R))
| `($_ $state { dir := $D, left := $L, right := $R }) => `(($L) {$state ; $D} ($R))
| _ => throw ()

end Delab

lemma PartialConfig.expand_well_formed {q: Label l} {dir: Turing.Dir} {L R: List (Symbol s)} {T T': PartialHTape (Symbol s)}
  (h: (L {q;dir} R : PartialConfig l s).tape.well_formed): ((L ++ T) {q;dir} (R ++ T')).tape.well_formed := sorry

namespace Machine

variable {M: Machine l s}

def pstep? (M: Machine l s) (C: PartialConfig l s): Option (PartialConfig l s) := do
  let Chead ← C.tape.head?
  match M C.state Chead with
  | .halt => .none
  | .next sym' dir lab' => .some { state := lab', tape := (← (C.tape.write sym').move? dir) }

def pstep (M: Machine l s) (C: PartialConfig l s) (hC: C.tape.well_formed): Option (PartialConfig l s) :=
  match M C.state (C.tape.head hC) with
  | .halt => .none
  | .next sym' dir lab' => .some { state := lab', tape := (C.tape.write sym').move (PartialTape.write.well_formed hC) dir}

notation A " p-["M"]-> " B => Machine.pstep? M A = Option.some B

lemma pstep.well_formed (_: M.pstep A hA = B): A.tape.well_formed := hA

lemma pstep?.well_formed (h: A p-[M]-> B): A.tape.well_formed :=
by {
  simp [pstep?, Option.bind, PartialTape.head?, PartialTape.pointed] at h
  split at h
  · cases h
  rename_i heq
  split at heq <;> {
    rename_i heq'
    simp [PartialTape.well_formed, PartialTape.pointed, heq']
    exact PartialHTape.nonempty.of_some_head heq
  }
}

lemma pstep?.to_pstep (h: A p-[M]-> B) (hAw: A.tape.well_formed): M.pstep A hAw = some B :=
by {
  simp [pstep?, Option.bind] at h
  split at h
  · cases h
  rename_i sym heq
  simp [pstep]

  simp [
    PartialTape.head?,
  ] at heq
  simp [
    PartialHTape.nonempty.head?_eq_some_head (T:=A.tape.pointed) (PartialHTape.nonempty.of_some_head heq)
  ] at heq
  simp [PartialTape.head, heq]

  simp at h
  split at h
  · cases h
  simp
  split at h
  · cases h
  rename_i heq'
  simp at h

  rw [
    PartialTape.move?.well_formed_eq_move (PartialTape.write.well_formed  hAw)
  ] at heq'
  simp at heq'
  rw [← heq'] at h
  exact h
}

lemma pstep?.none_wf_pstep (h: M.pstep? A = none) (hAw: A.tape.well_formed): M.pstep A hAw = none :=
by {
  simp [pstep?] at h
  specialize h _ (PartialTape.head?.wf_eq_some_head hAw)
  split at h
  · rename_i heq
    simp [pstep, heq]
  simp at h
  rename_i heq
  simp [pstep, heq]
  apply h
  exact PartialTape.move?.well_formed_eq_move (PartialTape.write.well_formed hAw)
}

lemma pstep?.to_pstep' {A: PartialConfig l s} (hAw: A.tape.well_formed): M.pstep? A = M.pstep A hAw :=
by {
  cases heq: M.pstep? A
  · symm
    exact pstep?.none_wf_pstep heq hAw
  · symm
    exact to_pstep heq hAw
}

lemma pstep?.simp {A: PartialConfig l s} (hAw: A.tape.well_formed): (A p-[M]-> B) ↔ (M.pstep A hAw = some B) :=
  by rw [pstep?.to_pstep' hAw]

inductive MultiPStep (M: Machine l s): ℕ → PartialConfig l s → PartialConfig l s → Prop where
| refl (C: PartialConfig l s): MultiPStep M 0 C C
| step A B C n: (A p-[M]-> B) → MultiPStep M n B C → MultiPStep M n.succ A C

notation A " p-[" M "]{" n "}-> " B => MultiPStep M n A B

instance MultiPStep.decidable: Decidable (A p-[M]{n}-> B) :=
by induction n generalizing A with
| zero => {
  by_cases hAB: A = B
  · rw [hAB]
    apply isTrue
    exact MultiPStep.refl B
  · apply isFalse
    intro hAB'
    cases hAB'
    simp at hAB
}
| succ n IH => {
  cases hAC: M.pstep? A
  · apply isFalse
    intro hAB
    cases hAB
    rename_i _ hAB' _
    rw [hAC] at hAB'
    cases hAB'
  · rename_i C
    specialize @IH C
    cases IH with
    | isFalse hCB => {
      apply isFalse
      intro hAB
      cases hAB
      rename_i _ hAC' hC'B
      rw [hAC] at hAC'
      cases hAC'
      contradiction
    }
    | isTrue hCB => {
      apply isTrue
      exact step A C B n hAC hCB
    }
}

@[simp]
def MultiPStep.refl': (A p-[M]{0}-> B) ↔ A = B :=
by {
  constructor
  · intro hAB
    cases hAB
    rfl
  · intro hAB
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

@[simp]
lemma MultiPStep.single: (A p-[M]{1}-> B) ↔ (A p-[M]-> B):= by {
  constructor
  · intro h
    cases h
    rename_i B' hAB' hBB'
    cases hBB'
    exact hAB'
  · intro h
    apply MultiPStep.step A B B
    · exact h
    · exact .refl B
}

lemma pstep?.pointed_valid (h: A p-[M]-> B): A.tape.pointed.nonempty :=
by {
  simp [pstep?, Option.bind] at h
  split at h
  · cases h
  rename_i heq
  exact PartialHTape.nonempty.of_some_head heq
}

@[simp]
lemma pstep?.all_empty_none: M.pstep? (([]: List (Symbol s)) {q;dir} ([]: List (Symbol s))) = none :=
by {
  simp [pstep?]
  intro a ha
  simp [PartialTape.head?, PartialTape.pointed] at ha
  split at ha <;> simp [PartialHTape.head?] at ha
}

lemma pstep.locality {L R L' R': List (Symbol s)} {T T': PartialHTape (Symbol s)}
  {hwf: (L {q;dir} R: PartialConfig l s).tape.well_formed}
  {hewf: ((L ++ T) {q;dir} (R ++ T'): PartialConfig l s).tape.well_formed}
  (h: M.pstep (L {q;dir} R: PartialConfig l s) hwf = some (L' {q';dir'} R': PartialConfig l s)):
    M.pstep ((L ++ T) {q;dir} (R ++ T')) hewf = some ((L' ++ T) {q';dir'} (R' ++ T')) :=
by {
  sorry
}

lemma pstep?.locality {L R L' R': List (Symbol s)} {T T': PartialHTape (Symbol s)}
  (h: (L {q;dir} R) p-[M]-> (L' {q';dir'} R')):
  ((L ++ T) {q;dir} R ++ T') p-[M]-> ((L' ++ T) {q';dir'} R' ++ T') :=
by {
  have origwf := pstep?.well_formed h
  rw [pstep?.simp origwf] at h
  have extwf: ((L ++ T) {q;dir} (R ++ T')).tape.well_formed := PartialConfig.expand_well_formed origwf
  rw [pstep?.simp extwf]
  exact pstep.locality h
}

lemma pstep?.locality' {L R L' R': List (Symbol s)} {T T' Tl Tr Tl' Tr': PartialHTape (Symbol s)}
  (h: (L {q;dir} R) p-[M]-> (L' {q';dir'} R'))
  (hTl: Tl = L ++ T)
  (hTr: Tr = R ++ T')
  (hTl': Tl' = L' ++ T)
  (hTr': Tr' = R' ++ T')
  :
  (Tl {q;dir} Tr) p-[M]-> (Tl' {q';dir'} Tr') :=
by {
  rw [hTl, hTr, hTl', hTr']
  exact locality h
}

lemma pstep?.locality_left₀ {R L' R': List (Symbol s)} {T T': PartialHTape (Symbol s)}
  (h: ({} {q;dir} R) p-[M]-> (L' {q';dir'} R')):
  (T {q;dir} R ++ T') p-[M]-> ((L' ++ T) {q';dir'} R' ++ T') :=
  by apply pstep?.locality' h (T:=T) (T':=T') <;> try simp

lemma pstep?.locality_left₁ {R L': List (Symbol s)} {T T': PartialHTape (Symbol s)}
  (h: ({} {q;dir} R) p-[M]-> (L' {q';dir'} {})):
  (T {q;dir} R ++ T') p-[M]-> ((L' ++ T) {q';dir'} T') :=
  by apply pstep?.locality' h (T:=T) (T':=T') <;> try simp

lemma pstep.finiteness {hwf: A.tape.well_formed} (h: M.pstep A hwf = some B):
  A.tape.finiteness = B.tape.finiteness :=
by {
  simp [pstep] at h
  split at h
  · cases h
  injection h with h
  rw [← h]
  simp
}

lemma pstep?.finiteness
  (h: A p-[M]-> B):
  A.tape.finiteness = B.tape.finiteness :=
by {
  have origwf := pstep?.well_formed h
  rw [pstep?.simp origwf] at h
  exact pstep.finiteness h
}

/--
A "locality" lemma for transitions on partial configurations.

If we can step from a given partial configuration to another, expanding this configuration on either
sides does not matter.

This is the key lemma to build inductive proofs about TMs, reasonning on incresingly complex
patterns of partial configurations.
-/
lemma MultiPStep.locality {L R L' R': List (Symbol s)} {T T': PartialHTape (Symbol s)} {q: Label l} {dir dir': Turing.Dir}
  (h: (L {q;dir} R) p-[M]{n}-> (L' {q';dir'} R')):
    ((L ++ T) {q;dir} R ++ T') p-[M]{n}-> ((L' ++ T) {q';dir'} R' ++ T') :=
by induction n generalizing L R L' R' q q' dir dir' with
| zero => {
  cases h
  exact .refl _
}
| succ n IH => {
  cases h
  rename_i I hI hIn
  have hIf: I.tape.finiteness = .finite := by {
    have htmp := pstep?.finiteness hI
    rw [← htmp]
    simp [PartialTape.finiteness]
  }
  obtain ⟨q'', dir'', L'', R''⟩ := I
  simp at hIf
  obtain ⟨hL'', hR''⟩ := hIf

  cases L''
  swap
  · simp at hL''
  rename_i Li
  cases R''
  swap
  · simp at hR''
  rename_i Ri

  apply MultiPStep.step _ _ _ _ (pstep?.locality hI) (IH hIn)
}

lemma MultiPStep.locality' {L R L' R': List (Symbol s)} {T T' Tl Tr Tl' Tr': PartialHTape (Symbol s)}
  (hTl: Tl = L ++ T)
  (hTr: Tr = R ++ T')
  (hTl': Tl' = L' ++ T)
  (hTr': Tr' = R' ++ T')
  (h: (L {q;dir} R) p-[M]{n}-> (L' {q';dir'} R'))
  :
  (Tl {q;dir} Tr) p-[M]{n}-> (Tl' {q';dir'} Tr') :=
by {
  rw [hTl, hTr, hTl', hTr']
  exact locality h
}

syntax "locality" (term)? "with" term "," term: tactic
macro_rules
| `(tactic| locality $h with $left, $right) => `(tactic| apply MultiPStep.locality' (h:=$h) (T:=$left) (T':=$right) <;> simp)
| `(tactic| locality with $left, $right) => `(tactic| apply MultiPStep.locality' (T:=$left) (T':=$right) (by simp) (by simp) (by simp) (by simp))

lemma MultiPStep.locality_left₀ {R L' R': List (Symbol s)} {T T': PartialHTape (Symbol s)} {q: Label l} {dir dir': Turing.Dir}
  (h: ({} {q;dir} R) p-[M]{n}-> (L' {q';dir'} R')): (T {q;dir} R ++ T') p-[M]{n}-> ((L' ++ T) {q';dir'} R' ++ T') :=
  by locality h with T, T'

lemma MultiPStep.locality_left₁ {R L': List (Symbol s)} {T T': PartialHTape (Symbol s)} {q: Label l} {dir dir': Turing.Dir}
  (h: ({} {q;dir} R) p-[M]{n}-> (L' {q';dir'} {})): (T {q;dir} R ++ T') p-[M]{n}-> ((L' ++ T) {q';dir'} T') :=
  by locality h with T, T'

lemma MultiPStep.locality_left₂ {R L': List (Symbol s)} {T: PartialHTape (Symbol s)} {q: Label l} {dir dir': Turing.Dir}
  (h: ({} {q;dir} R) p-[M]{n}-> (L' {q';dir'} {})): (T {q;dir} R) p-[M]{n}-> ((L' ++ T) {q';dir'} {}) :=
  by locality h with T, {}

lemma MultiPStep.locality_left₃ {R L': List (Symbol s)} {T: PartialHTape (Symbol s)} {q: Label l} {dir dir': Turing.Dir}
  (h: ({} {q;dir} R) p-[M]{n}-> (L' {q';dir'} {})): ({} {q;dir} R ++ T) p-[M]{n}-> (L' {q';dir'} T) :=
  by locality h with {}, T

lemma MultiPStep.locality_left₀_finite_left {R L' R' T: List (Symbol s)} {T': PartialHTape (Symbol s)} {q: Label l} {dir dir': Turing.Dir}
  (h: ({} {q;dir} R) p-[M]{n}-> (L' {q';dir'} R')): (T {q;dir} R ++ T') p-[M]{n}-> ((L' ++ T) {q';dir'} R' ++ T') :=
  by locality h with T, T'

lemma MultiPStep.locality_left₁_finite_left {R L' T: List (Symbol s)} {T': PartialHTape (Symbol s)} {q: Label l} {dir dir': Turing.Dir}
  (h: ({} {q;dir} R) p-[M]{n}-> (L' {q';dir'} {})): (T {q;dir} R ++ T') p-[M]{n}-> ((L' ++ T) {q';dir'} T') :=
  by locality h with T, T'

lemma MultiPStep.locality_left₂_finite {R L' T: List (Symbol s)} {q: Label l} {dir dir': Turing.Dir}
  (h: ({} {q;dir} R) p-[M]{n}-> (L' {q';dir'} {})): (T {q;dir} R) p-[M]{n}-> ((L' ++ T) {q';dir'} {}) :=
  by locality h with T, {}

lemma MultiPStep.locality_left₃_finite {R L' T: List (Symbol s)} {q: Label l} {dir dir': Turing.Dir}
  (h: ({} {q;dir} R) p-[M]{n}-> (L' {q';dir'} {})): ({} {q;dir} R ++ T) p-[M]{n}-> (L' {q';dir'} T) :=
  by locality h with {}, T

/--
The locality tactic tries to turn a proof of step of a complex tape into a "local step" on the edges
of the tape.

TODO: this is a very very crude implementation of a potentially very powerful tactic.
-/
syntax "locality" (term)?: tactic
syntax "locality!": tactic

macro_rules
| `(tactic| locality) => `(tactic|
    first
    | apply MultiPStep.locality_left₀
    | apply MultiPStep.locality_left₁
    | apply MultiPStep.locality_left₂
    | apply MultiPStep.locality_left₃
    | apply MultiPStep.locality_left₀_finite_left
    | apply MultiPStep.locality_left₁_finite_left
    | apply MultiPStep.locality_left₂_finite
    | apply MultiPStep.locality_left₃_finite
  )
| `(tactic| locality $h) => `(tactic|
    first
    | apply MultiPStep.locality_left₀ $h
    | apply MultiPStep.locality_left₁ $h
    | apply MultiPStep.locality_left₂ $h
    | apply MultiPStep.locality_left₃ $h
    | apply MultiPStep.locality_left₀_finite_left $h
    | apply MultiPStep.locality_left₁_finite_left $h
    | apply MultiPStep.locality_left₂_finite $h
    | apply MultiPStep.locality_left₃_finite $h
  )
| `(tactic| locality!) => `(tactic| locality; decide)

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
| _, _ => unreachable!

/-
Example of using the locality principle and decidable equality to perform actual computations
with partial states.

Note that in its current form, the proof is very verbose.
Having tactics to avoid such verbosity will be needed.
-/
example: ({} {2}> List.replicate n (1: Symbol 2)) p-[tmpMach]{n}-> ((List.replicate n (1: Symbol 2)) {2}> {}) :=
by induction n with
| zero => {
  simp
}
| succ n IH => {
  have htmp := calc ({} {2}> List.replicate (n+1) (1: Symbol 2))
    _ p-[tmpMach]{0}-> ({} {2}> ([(1: Symbol 2)] ++ List.replicate n (1: Symbol 2))) := by simp; rfl
    _ p-[tmpMach]{1}-> ([(1: Symbol 2)] {2}> (List.replicate n (1: Symbol 2))) := by locality!
    _ p-[tmpMach]{n}-> ((List.replicate n (1: Symbol 2) ++ [(1: Symbol 2)]) {2}> {}) := by locality IH
    _ p-[tmpMach]{0}-> ((List.replicate (n+1) (1: Symbol 2)) {2}> {}) := by {
      simp [-PartialHTape.append_lists]
      symm
      exact List.replicate_succ' n 1
    }

  simp at htmp
  simp
  rw [Nat.add_comm n] at *
  exact htmp
}

end Example

