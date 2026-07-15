import Mathlib.Data.List.Basic
import Mathlib.Algebra.Order.Group.Nat
import Mathlib.Algebra.Group.Even
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith

/-!
# Skelet #17 — abstract counter layer (levels 2½–5)

Lean port of the arithmetic half of `Coq-BB5/CoqBB5/BB5/BB5_Skelet17.v`: the
abstract state is `(a₀, [a₁, a₂, …]) : ℕ × List ℕ` (Chris Xu's exponent
notation; the tape exponent of the head block is `a₀ - 1`).  The four
operations `Increment`, `Halve`, `Zero`, `Overflow` rewrite abstract states;
their tape soundness is proven in `Tape.lean` via `toConfig`.

On top of these, the (mod 2) suffix-xor of the list is a Gray-code counter:
`toN` is its value, `toS` the direction bit, `toL` the digit count, `ai i` the
`i`-th exponent, and `divpow2r n i = (n + 2^i) / 2^(i+1)` counts how often
digit `i` flips during a run of `Increment`s.
-/

namespace Deciders.Skelet.Skelet17

/-- Abstract counter state `(a₀, [a₁, a₂, …])`. -/
abbrev S17 : Type := ℕ × List ℕ

/-- All entries nonzero (Coq `Forall Nonzero`). -/
def Nonzero (xs : List ℕ) : Prop := ∀ a ∈ xs, a ≠ 0

/-- All entries even (Coq `Forall Even`). -/
def AllEven (xs : List ℕ) : Prop := ∀ a ∈ xs, Even a

/-! ## The four operations (Chris Xu's rules) -/

/-- Coq `Increment`. -/
inductive Increment : S17 → S17 → Prop
  | even {x : ℕ} {xs : List ℕ} {y z : ℕ} {zs : List ℕ} :
      Even x → Nonzero xs → AllEven xs → Odd y →
      Increment (x + 1, xs ++ y :: z :: zs) (x, xs ++ y :: (z + 1) :: zs)
  | odd {x y : ℕ} {xs : List ℕ} :
      Odd x →
      Increment (x + 1, y :: xs) (x, (y + 1) :: xs)

/-- Coq `Halve`. -/
inductive Halve : S17 → S17 → Prop
  | intro (x : ℕ) (xs : List ℕ) : Halve (0, x :: xs) (x + 1, xs)

/-- Coq `Zero`. -/
inductive Zero : S17 → S17 → Prop
  | intro {x : ℕ} {xs : List ℕ} {y : ℕ} :
      Nonzero xs → AllEven xs → Even x → Even y →
      Zero (x + 1, xs ++ [y]) (x, xs ++ [y + 1, 0, 0])

/-- Coq `Overflow`. -/
inductive Overflow : S17 → S17 → Prop
  | intro {x : ℕ} {xs : List ℕ} {y : ℕ} :
      Nonzero xs → AllEven xs → Even x → Odd y →
      Overflow (x + 1, xs ++ [y]) (x + 1, xs ++ [y + 1, 0])

/-- Coq `TryHalve`: apply `Halve` if possible, else do nothing. -/
inductive TryHalve : S17 → S17 → Prop
  | one (x : ℕ) (xs : List ℕ) : TryHalve (0, x :: xs) (x + 1, xs)
  | zero (x : ℕ) (xs : List ℕ) : TryHalve (x + 1, xs) (x + 1, xs)

/-- Coq `Increments`: `n` consecutive `Increment`s. -/
inductive Increments : ℕ → S17 → S17 → Prop
  | zero (s : S17) : Increments 0 s s
  | succ {n : ℕ} {s1 s2 s3 : S17} :
      Increment s1 s2 → Increments n s2 s3 → Increments (n + 1) s1 s3

/-! ## Gray-code decoding -/

/-- Parity as a `Bool` (Coq `Nat.odd`). -/
def oddb (n : ℕ) : Bool := n % 2 == 1

@[simp] lemma oddb_eq_true_iff {n : ℕ} : oddb n = true ↔ Odd n := by
  simp [oddb, Nat.odd_iff]

@[simp] lemma oddb_eq_false_iff {n : ℕ} : oddb n = false ↔ Even n := by
  simp [oddb, Nat.even_iff]

/-- Coq `grey_to_binary`: suffix-xor decode of a Gray code, most significant
digit last. -/
def greyToBinary : List Bool → List Bool
  | [] => []
  | x :: xt => (xor x ((greyToBinary xt).headD false)) :: greyToBinary xt

/-- Coq `list_to_binary`. -/
def listToBinary (xs : List ℕ) : List Bool := greyToBinary (xs.map oddb)

/-- Coq `binary_to_nat`: little-endian binary value. -/
def binaryToNat : List Bool → ℕ
  | [] => 0
  | x :: xt => (if x then 1 else 0) + binaryToNat xt * 2

/-- Coq `to_n_binary`: the counter digits of a state. -/
def toNBinary (s : S17) : List Bool := listToBinary s.2

/-- Coq `to_n`: the counter value `n`. -/
def toN (s : S17) : ℕ := binaryToNat (toNBinary s)

/-- Coq `to_s`: the direction bit `s` (`true` = counting up). -/
def toS (s : S17) : Bool := xor (decide (Even s.1)) ((listToBinary s.2).headD false)

/-- Coq `to_l`: the number of digits `l`. -/
def toL (s : S17) : ℕ := (toNBinary s).length

/-- Coq `divpow2r n i = (n + 2^i) / 2^(i+1)`: how many of the first `n`
increments flip digit `i`. -/
def divpow2r (n i : ℕ) : ℕ := (n + 2 ^ i) / 2 ^ (i + 1)

/-- Coq `ai i s`: the `i`-th list entry (`a_{i+1}` in Xu's indexing). -/
def ai (i : ℕ) (s : S17) : ℕ := s.2.getD i 0

/-- Coq `ai'`: `ai' 0 = a₀` (the head counter), `ai' (i+1) = ai i`. -/
def ai' : ℕ → S17 → ℕ
  | 0, s => s.1
  | i + 1, s => ai i s

/-! ## Structural lemmas on the decoding -/

@[simp] lemma greyToBinary_length (xs : List Bool) :
    (greyToBinary xs).length = xs.length := by
  induction xs with
  | nil => rfl
  | cons x xt ih => simp [greyToBinary, ih]

@[simp] lemma listToBinary_length (xs : List ℕ) :
    (listToBinary xs).length = xs.length := by
  simp [listToBinary]

lemma toL_eq_length (s : S17) : toL s = s.2.length := by
  simp [toL, toNBinary]

/-! ## Well-formedness -/

/-- Coq `WF1`. -/
inductive WF1 : S17 → Prop
  | intro (x : ℕ) (xs : List ℕ) (y : ℕ) :
      Nonzero xs → WF1 (x, xs ++ [y])

/-- Coq `WF2`. -/
inductive WF2 : S17 → Prop
  | intro (x : ℕ) (xs : List ℕ) (y : ℕ) (zs : List ℕ) :
      Nonzero xs → AllEven xs → Odd y → Nonzero zs →
      WF2 (x, xs ++ y :: zs ++ [0, 0])

/-! ## Effect of the operations on `s`, `n`, `l`, `aᵢ` (Coq level 3)

These are stated now and proven in dependency order; each `sorry` is one Coq
lemma to port. -/

lemma Increment_sgn {s1 s2 : S17} (h : Increment s1 s2) : toS s1 = toS s2 := by
  sorry

lemma Halve_sgn {s1 s2 : S17} (h : Halve s1 s2) : !toS s1 = toS s2 := by
  sorry

lemma Zero_sgn {s1 s2 : S17} (h : Zero s1 s2) : toS s2 = false := by
  sorry

lemma Overflow_sgn {s1 s2 : S17} (h : Overflow s1 s2) : toS s2 = false := by
  sorry

lemma Increment_n {s1 s2 : S17} (h : Increment s1 s2) :
    if toS s1 then toN s1 + 1 = toN s2 else toN s1 = toN s2 + 1 := by
  sorry

lemma Halve_n {s1 s2 : S17} (h : Halve s1 s2) : toN s1 / 2 = toN s2 := by
  sorry

lemma Zero_n {s1 s2 : S17} (h : Zero s1 s2) : toN s2 = 2 ^ toL s1 - 1 := by
  sorry

lemma Overflow_n {s1 s2 : S17} (h : Overflow s1 s2) : toN s2 = 0 := by
  sorry

lemma Increment_len {s1 s2 : S17} (h : Increment s1 s2) : toL s1 = toL s2 := by
  sorry

lemma Halve_len {s1 s2 : S17} (h : Halve s1 s2) : toL s1 = toL s2 + 1 := by
  sorry

lemma Zero_len {s1 s2 : S17} (h : Zero s1 s2) : toL s2 = toL s1 + 2 := by
  sorry

lemma Overflow_len {s1 s2 : S17} (h : Overflow s1 s2) : toL s2 = toL s1 + 1 := by
  sorry

end Deciders.Skelet.Skelet17
