import Mathlib.Data.List.Basic
import Mathlib.Data.List.GetD
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

/-- Coq `WF2` (stated in cons-normal form). -/
inductive WF2 : S17 → Prop
  | intro (x : ℕ) (xs : List ℕ) (y : ℕ) (zs : List ℕ) :
      Nonzero xs → AllEven xs → Odd y → Nonzero zs →
      WF2 (x, xs ++ y :: (zs ++ [0, 0]))

/-! ## Effect of the operations on `s`, `n`, `l`, `aᵢ` (Coq level 3)

These are stated now and proven in dependency order; each `sorry` is one Coq
lemma to port. -/

/-! ### Inversion lemmas for the rules -/

lemma increment_inv {s1 s2 : S17} (h : Increment s1 s2) :
    (∃ x xs y z zs, Even x ∧ Nonzero xs ∧ AllEven xs ∧ Odd y ∧
      s1 = (x + 1, xs ++ y :: z :: zs) ∧ s2 = (x, xs ++ y :: (z + 1) :: zs)) ∨
    (∃ x y xs, Odd x ∧ s1 = (x + 1, y :: xs) ∧ s2 = (x, (y + 1) :: xs)) := by
  cases h with
  | even hx hnz hev hy => exact .inl ⟨_, _, _, _, _, hx, hnz, hev, hy, rfl, rfl⟩
  | odd hx => exact .inr ⟨_, _, _, hx, rfl, rfl⟩

lemma halve_inv {s1 s2 : S17} (h : Halve s1 s2) :
    ∃ x xs, s1 = (0, x :: xs) ∧ s2 = (x + 1, xs) := by
  cases h with | intro x xs => exact ⟨x, xs, rfl, rfl⟩

lemma zero_inv {s1 s2 : S17} (h : Zero s1 s2) :
    ∃ x xs y, Nonzero xs ∧ AllEven xs ∧ Even x ∧ Even y ∧
      s1 = (x + 1, xs ++ [y]) ∧ s2 = (x, xs ++ [y + 1, 0, 0]) := by
  cases h with
  | intro hnz hev hx hy => exact ⟨_, _, _, hnz, hev, hx, hy, rfl, rfl⟩

lemma overflow_inv {s1 s2 : S17} (h : Overflow s1 s2) :
    ∃ x xs y, Nonzero xs ∧ AllEven xs ∧ Even x ∧ Odd y ∧
      s1 = (x + 1, xs ++ [y]) ∧ s2 = (x + 1, xs ++ [y + 1, 0]) := by
  cases h with
  | intro hnz hev hx hy => exact ⟨_, _, _, hnz, hev, hx, hy, rfl, rfl⟩

lemma tryHalve_inv {s1 s2 : S17} (h : TryHalve s1 s2) :
    (s1.1 = 0 ∧ ∃ a as, s1.2 = a :: as ∧ s2 = (a + 1, as)) ∨
    (s1.1 ≠ 0 ∧ s2 = s1) := by
  cases h with
  | one a as => exact .inl ⟨rfl, a, as, rfl, rfl⟩
  | zero a as => exact .inr ⟨Nat.succ_ne_zero a, rfl⟩

/-! ### Bool and parity helpers -/

lemma xor_not_left (a b : Bool) : xor (!a) b = !(xor a b) := by
  cases a <;> cases b <;> rfl

lemma xor_not_right (a b : Bool) : xor a (!b) = !(xor a b) := by
  cases a <;> cases b <;> rfl

@[simp] lemma oddb_succ (n : ℕ) : oddb (n + 1) = !oddb n := by
  rcases Nat.even_or_odd n with h | h
  · have h1 : oddb n = false := oddb_eq_false_iff.2 h
    have h2 : oddb (n + 1) = true := oddb_eq_true_iff.2 (Even.add_one h)
    rw [h1, h2]; rfl
  · have h1 : oddb n = true := oddb_eq_true_iff.2 h
    have h2 : oddb (n + 1) = false := oddb_eq_false_iff.2 (Odd.add_one h)
    rw [h1, h2]; rfl

@[simp] lemma decide_even_succ (n : ℕ) : decide (Even (n + 1)) = !decide (Even n) := by
  rcases Nat.even_or_odd n with h | h
  · simp [h, Nat.even_add_one]
  · simp [Nat.not_even_iff_odd.2 h, Nat.even_add_one]

lemma decide_even_succ_eq_oddb (n : ℕ) : decide (Even (n + 1)) = oddb n := by
  rcases Nat.even_or_odd n with h | h
  · simp [Nat.even_add_one, h, oddb_eq_false_iff.2 h]
  · simp [oddb_eq_true_iff.2 h, h]

/-! ### `greyToBinary` and `binaryToNat` support -/

@[simp] lemma greyToBinary_nil : greyToBinary [] = [] := rfl

lemma greyToBinary_cons (x : Bool) (xt : List Bool) :
    greyToBinary (x :: xt) = xor x ((greyToBinary xt).headD false) :: greyToBinary xt := rfl

lemma listToBinary_nil : listToBinary [] = [] := rfl

lemma listToBinary_cons (a : ℕ) (xs : List ℕ) :
    listToBinary (a :: xs) =
      xor (oddb a) ((listToBinary xs).headD false) :: listToBinary xs := rfl

@[simp] lemma binaryToNat_nil : binaryToNat [] = 0 := rfl
@[simp] lemma binaryToNat_cons_true (xs : List Bool) :
    binaryToNat (true :: xs) = 1 + binaryToNat xs * 2 := rfl
@[simp] lemma binaryToNat_cons_false (xs : List Bool) :
    binaryToNat (false :: xs) = binaryToNat xs * 2 := by
  simp [binaryToNat]

/-- Coq `map_odd_Even`. -/
lemma map_oddb_allEven : ∀ {xs : List ℕ}, AllEven xs →
    xs.map oddb = List.replicate xs.length false
  | [], _ => rfl
  | a :: xs, h => by
      have ha : oddb a = false := oddb_eq_false_iff.2 (h a (by simp))
      simp only [List.map_cons, List.length_cons, List.replicate_succ, ha]
      exact congrArg _ (map_oddb_allEven fun b hb => h b (List.mem_cons_of_mem _ hb))

/-- Coq `grey_to_binary_0s_hd`. -/
lemma greyToBinary_replicate_false_hd : ∀ (n : ℕ) (xs : List Bool),
    (greyToBinary (List.replicate n false ++ xs)).headD false
      = (greyToBinary xs).headD false
  | 0, xs => rfl
  | n + 1, xs => by
      simp only [List.replicate_succ, List.cons_append, greyToBinary_cons,
        List.headD_cons, Bool.false_xor]
      exact greyToBinary_replicate_false_hd n xs

/-- Coq `grey_to_binary_0s`. -/
lemma greyToBinary_replicate_false : ∀ (n : ℕ) (xs : List Bool),
    greyToBinary (List.replicate n false ++ xs)
      = List.replicate n ((greyToBinary xs).headD false) ++ greyToBinary xs
  | 0, xs => rfl
  | n + 1, xs => by
      have ih := greyToBinary_replicate_false n xs
      simp only [List.replicate_succ, List.cons_append, greyToBinary_cons,
        Bool.false_xor, ih]
      congr 1
      cases n with
      | zero => simp
      | succ m => simp [List.replicate_succ]

/-- Coq `hd_repeat`. -/
lemma headD_replicate (x : Bool) (n : ℕ) (xs : List Bool) :
    (List.replicate n x ++ x :: xs).headD false = x := by
  cases n <;> simp [List.replicate_succ]

/-- `headD` of a replicated own-head prefix. -/
lemma headD_replicate_append_self (n : ℕ) (w : List Bool) :
    (List.replicate n (w.headD false) ++ w).headD false = w.headD false := by
  cases n <;> simp [List.replicate_succ]

/-- Coq `repeat_app_S`. -/
lemma replicate_append_succ {α} (x : α) (n : ℕ) (xs : List α) :
    List.replicate n x ++ x :: xs = List.replicate (n + 1) x ++ xs := by
  induction n with
  | zero => rfl
  | succ n ih => simp only [List.replicate_succ, List.cons_append, ih]

/-- Coq `binary_to_nat_S`. -/
lemma binaryToNat_succ : ∀ (n : ℕ) (xs : List Bool),
    binaryToNat (List.replicate n true ++ false :: xs) + 1
      = binaryToNat (List.replicate n false ++ true :: xs)
  | 0, xs => by simp; omega
  | n + 1, xs => by
      have ih := binaryToNat_succ n xs
      simp only [List.replicate_succ, List.cons_append, binaryToNat_cons_true,
        binaryToNat_cons_false] at *
      omega

/-- Coq `list_to_binary_S_hd`. -/
lemma listToBinary_succ_hd : ∀ (xs : List ℕ) (z : ℕ) (zs : List ℕ),
    (listToBinary (xs ++ (z + 1) :: zs)).headD false
      = !(listToBinary (xs ++ z :: zs)).headD false
  | [], z, zs => by
      simp only [List.nil_append, listToBinary_cons, List.headD_cons, oddb_succ,
        xor_not_left]
  | a :: xs, z, zs => by
      simp only [List.cons_append, listToBinary_cons, List.headD_cons,
        listToBinary_succ_hd xs z zs, xor_not_right]

/-- Coq `list_to_binary_app_O_hd`. -/
lemma listToBinary_append_zero_hd : ∀ (xs : List ℕ),
    (listToBinary (xs ++ [0])).headD false = (listToBinary xs).headD false
  | [] => rfl
  | a :: xs => by
      simp only [List.cons_append, listToBinary_cons, List.headD_cons,
        listToBinary_append_zero_hd xs]

/-- Coq `binary_to_nat_app_O`. -/
lemma binaryToNat_append_false : ∀ (xs : List Bool),
    binaryToNat (xs ++ [false]) = binaryToNat xs
  | [] => rfl
  | a :: xs => by
      simp only [List.cons_append, binaryToNat, binaryToNat_append_false xs]

lemma pow2_ne_zero (i : ℕ) : 2 ^ i ≠ 0 := (Nat.two_pow_pos i).ne'

/-- Coq `binary_to_nat_1s_app`. -/
lemma binaryToNat_replicate_true_append : ∀ (n : ℕ) (xs : List Bool),
    binaryToNat (List.replicate n true ++ xs) = binaryToNat xs * 2 ^ n + 2 ^ n - 1
  | 0, xs => by simp
  | n + 1, xs => by
      have ih := binaryToNat_replicate_true_append n xs
      have hp : 0 < 2 ^ n := Nat.two_pow_pos n
      simp only [List.replicate_succ, List.cons_append, binaryToNat_cons_true, ih,
        pow_succ, ← mul_assoc]
      omega

/-- Coq `binary_to_nat_0s_app`. -/
lemma binaryToNat_replicate_false_append : ∀ (n : ℕ) (xs : List Bool),
    binaryToNat (List.replicate n false ++ xs) = binaryToNat xs * 2 ^ n
  | 0, xs => by simp
  | n + 1, xs => by
      have ih := binaryToNat_replicate_false_append n xs
      simp only [List.replicate_succ, List.cons_append, binaryToNat_cons_false, ih,
        pow_succ, ← mul_assoc]

/-- Coq `binary_to_nat_1s`. -/
lemma binaryToNat_replicate_true (n : ℕ) :
    binaryToNat (List.replicate n true) = 2 ^ n - 1 := by
  have := binaryToNat_replicate_true_append n []
  simpa using this

/-- Coq `binary_to_nat_0s`. -/
lemma binaryToNat_replicate_false (n : ℕ) :
    binaryToNat (List.replicate n false) = 0 := by
  have := binaryToNat_replicate_false_append n []
  simpa using this

/-! ### Unfolding lemmas for the observables -/

lemma toS_def (x : ℕ) (xs : List ℕ) :
    toS (x, xs) = xor (decide (Even x)) ((listToBinary xs).headD false) := rfl

lemma toN_def (xs : List ℕ) (x : ℕ) : toN (x, xs) = binaryToNat (listToBinary xs) := rfl

lemma toL_def (x : ℕ) (xs : List ℕ) : toL (x, xs) = xs.length := by
  simp [toL, toNBinary]

/-- The `listToBinary` of an all-even-prefix list, split at the first odd entry
(`Odd y`): `1^(n+1) 0…`-shaped when the digit after `y` xors to `false`. -/
lemma listToBinary_allEven_prefix {xs : List ℕ} (hev : AllEven xs) (rest : List ℕ) :
    listToBinary (xs ++ rest)
      = List.replicate xs.length ((listToBinary rest).headD false) ++ listToBinary rest := by
  unfold listToBinary
  rw [List.map_append, map_oddb_allEven hev, greyToBinary_replicate_false]

/-! ## Effect of the operations on `s`, `n`, `l`, `aᵢ` (Coq level 3) -/

lemma Increment_sgn {s1 s2 : S17} (h : Increment s1 s2) : toS s1 = toS s2 := by
  rcases increment_inv h with
    ⟨x, xs, y, z, zs, hx, hnz, hev, hy, rfl, rfl⟩ | ⟨x, y, xs, hx, rfl, rfl⟩
  · rw [toS_def, toS_def, decide_even_succ]
    have hhd : (listToBinary (xs ++ y :: (z + 1) :: zs)).headD false
        = !(listToBinary (xs ++ y :: z :: zs)).headD false := by
      have := listToBinary_succ_hd (xs ++ [y]) z zs
      simpa [List.append_assoc] using this
    rw [hhd, xor_not_left, xor_not_right]
  · rw [toS_def, toS_def, decide_even_succ]
    have hhd : (listToBinary ((y + 1) :: xs)).headD false
        = !(listToBinary (y :: xs)).headD false := by
      have := listToBinary_succ_hd [] y xs
      simpa using this
    rw [hhd, xor_not_left, xor_not_right]

lemma Halve_sgn {s1 s2 : S17} (h : Halve s1 s2) : (!toS s1) = toS s2 := by
  obtain ⟨x, xs, rfl, rfl⟩ := halve_inv h
  rw [toS_def, toS_def, listToBinary_cons]
  simp only [List.headD_cons, decide_even_succ_eq_oddb]
  cases hx : oddb x <;> cases hh : (listToBinary xs).headD false <;> simp

lemma Zero_sgn {s1 s2 : S17} (h : Zero s1 s2) : toS s2 = false := by
  obtain ⟨x, xs, y, hnz, hev, hx, hy, rfl, rfl⟩ := zero_inv h
  rw [toS_def, listToBinary_allEven_prefix hev, headD_replicate_append_self]
  simp [listToBinary_cons, listToBinary_nil, hy, show oddb 0 = false from rfl, hx]

lemma Overflow_sgn {s1 s2 : S17} (h : Overflow s1 s2) : toS s2 = false := by
  obtain ⟨x, xs, y, hnz, hev, hx, hy, rfl, rfl⟩ := overflow_inv h
  rw [toS_def, listToBinary_allEven_prefix hev, headD_replicate_append_self]
  simp [listToBinary_cons, listToBinary_nil, hy, show oddb 0 = false from rfl,
    Nat.even_add_one, hx]

/-- The digit shape of a list starting with an all-even prefix and one odd
entry: `(!c)^(n+1) c ⋯` where `c` is the head digit of the tail (Coq
`Increment_inc`/`Increment_dec` fused). -/
lemma listToBinary_incr_split {xs : List ℕ} (hev : AllEven xs) {y : ℕ} (hy : Odd y)
    (z : ℕ) (zs : List ℕ) :
    listToBinary (xs ++ y :: z :: zs)
      = List.replicate (xs.length + 1) (!(listToBinary (z :: zs)).headD false)
          ++ listToBinary (z :: zs) := by
  rw [listToBinary_allEven_prefix hev]
  have hodd : oddb y = true := oddb_eq_true_iff.2 hy
  have hcons : listToBinary (y :: z :: zs)
      = (!(listToBinary (z :: zs)).headD false) :: listToBinary (z :: zs) := by
    rw [listToBinary_cons (a := y), hodd]
    cases (listToBinary (z :: zs)).headD false <;> rfl
  rw [hcons]
  simp only [List.headD_cons]
  exact replicate_append_succ _ _ _

/-- Head digit of the incremented tail flips. -/
lemma listToBinary_head_succ (z : ℕ) (zs : List ℕ) :
    (listToBinary ((z + 1) :: zs)).headD false
      = !(listToBinary (z :: zs)).headD false := by
  simpa using listToBinary_succ_hd [] z zs

lemma Increment_n {s1 s2 : S17} (h : Increment s1 s2) :
    if toS s1 then toN s1 + 1 = toN s2 else toN s1 = toN s2 + 1 := by
  rcases increment_inv h with
    ⟨x, xs, y, z, zs, hx, hnz, hev, hy, rfl, rfl⟩ | ⟨x, y, xs, hx, rfl, rfl⟩
  · -- even head-counter case: the interesting one
    have hc : (listToBinary (z :: zs)).headD false
        = xor (oddb z) ((listToBinary zs).headD false) := by
      rw [listToBinary_cons, List.headD_cons]
    set c := xor (oddb z) ((listToBinary zs).headD false) with hcdef
    have hsplit1 := listToBinary_incr_split hev hy z zs
    have hsplit2 := listToBinary_incr_split hev hy (z + 1) zs
    rw [listToBinary_head_succ, hc, Bool.not_not] at hsplit2
    rw [hc] at hsplit1
    have hcons1 : listToBinary (z :: zs) = c :: listToBinary zs := by
      rw [listToBinary_cons]
    have hcons2 : listToBinary ((z + 1) :: zs) = (!c) :: listToBinary zs := by
      rw [listToBinary_cons, oddb_succ, xor_not_left]
    have hS : toS (x + 1, xs ++ y :: z :: zs) = !c := by
      rw [toS_def, hsplit1]
      have hde : decide (Even (x + 1)) = false := by
        simp [Nat.even_add_one, hx]
      rw [hde]
      simp [List.replicate_succ]
    rw [hS]
    have hn1 : toN (x + 1, xs ++ y :: z :: zs)
        = binaryToNat (List.replicate (xs.length + 1) (!c) ++ c :: listToBinary zs) := by
      rw [toN_def, hsplit1, hcons1]
    have hn2 : toN (x, xs ++ y :: (z + 1) :: zs)
        = binaryToNat (List.replicate (xs.length + 1) c ++ (!c) :: listToBinary zs) := by
      rw [toN_def, hsplit2, hcons2]
    cases hcv : c with
    | false =>
        rw [hcv] at hn1 hn2
        simp only [Bool.not_false, if_true]
        rw [hn1, hn2]
        exact binaryToNat_succ _ _
    | true =>
        rw [hcv] at hn1 hn2
        simp only [Bool.not_true]
        rw [hn1, hn2]
        exact (binaryToNat_succ _ _).symm
  · -- odd head-counter case
    set d := xor (oddb y) ((listToBinary xs).headD false) with hddef
    have hcons1 : listToBinary (y :: xs) = d :: listToBinary xs := by
      rw [listToBinary_cons]
    have hcons2 : listToBinary ((y + 1) :: xs) = (!d) :: listToBinary xs := by
      rw [listToBinary_cons, oddb_succ, xor_not_left]
    have hS : toS (x + 1, y :: xs) = !d := by
      rw [toS_def, hcons1]
      have hde : decide (Even (x + 1)) = true := by
        simp [hx]
      rw [hde, List.headD_cons]
      cases d <;> rfl
    rw [hS, toN_def, toN_def, hcons1, hcons2]
    cases d with
    | false => simp; omega
    | true => simp; omega

lemma Halve_n {s1 s2 : S17} (h : Halve s1 s2) : toN s1 / 2 = toN s2 := by
  obtain ⟨x, xs, rfl, rfl⟩ := halve_inv h
  rw [toN_def, toN_def, listToBinary_cons]
  simp only [binaryToNat]
  cases xor (oddb x) ((listToBinary xs).headD false) <;> simp
  omega

lemma Zero_n {s1 s2 : S17} (h : Zero s1 s2) : toN s2 = 2 ^ toL s1 - 1 := by
  obtain ⟨x, xs, y, hnz, hev, hx, hy, rfl, rfl⟩ := zero_inv h
  have htail : listToBinary [y + 1, 0, 0] = [true, false, false] := by
    simp [listToBinary_cons, listToBinary_nil, hy, show oddb 0 = false from rfl]
  rw [toN_def, listToBinary_allEven_prefix hev, htail]
  have hhd : ([true, false, false] : List Bool).headD false = true := rfl
  rw [hhd, show (true : Bool) :: [false, false] = [true, false, false] from rfl,
    show (List.replicate xs.length true ++ [true, false, false] : List Bool)
      = List.replicate xs.length true ++ true :: [false, false] from rfl,
    replicate_append_succ, binaryToNat_replicate_true_append]
  rw [toL_def]
  simp [binaryToNat]

lemma Overflow_n {s1 s2 : S17} (h : Overflow s1 s2) : toN s2 = 0 := by
  obtain ⟨x, xs, y, hnz, hev, hx, hy, rfl, rfl⟩ := overflow_inv h
  have htail : listToBinary [y + 1, 0] = [false, false] := by
    simp [listToBinary_cons, listToBinary_nil, hy, show oddb 0 = false from rfl]
  rw [toN_def, listToBinary_allEven_prefix hev, htail]
  have hhd : ([false, false] : List Bool).headD false = false := rfl
  rw [hhd, binaryToNat_replicate_false_append]
  simp [binaryToNat]

lemma Increment_len {s1 s2 : S17} (h : Increment s1 s2) : toL s1 = toL s2 := by
  rcases increment_inv h with
    ⟨x, xs, y, z, zs, hx, hnz, hev, hy, rfl, rfl⟩ | ⟨x, y, xs, hx, rfl, rfl⟩ <;>
    simp [toL_def]

lemma Halve_len {s1 s2 : S17} (h : Halve s1 s2) : toL s1 = toL s2 + 1 := by
  obtain ⟨x, xs, rfl, rfl⟩ := halve_inv h
  simp [toL_def]

lemma Zero_len {s1 s2 : S17} (h : Zero s1 s2) : toL s2 = toL s1 + 2 := by
  obtain ⟨x, xs, y, _, _, _, _, rfl, rfl⟩ := zero_inv h
  simp [toL_def]

lemma Overflow_len {s1 s2 : S17} (h : Overflow s1 s2) : toL s2 = toL s1 + 1 := by
  obtain ⟨x, xs, y, _, _, _, _, rfl, rfl⟩ := overflow_inv h
  simp [toL_def]

/-! ### `divpow2r` arithmetic (Coq lines 1232–1414) -/

lemma two_pow_succ' (i : ℕ) : 2 ^ (i + 1) = 2 ^ i + 2 ^ i := by
  rw [pow_succ]; omega

/-- Coq `divpow2r_inc`: at the flip point, `divpow2r` increments. -/
lemma divpow2r_inc {n i : ℕ} (h : n % 2 ^ (i + 1) = 2 ^ i - 1) :
    divpow2r n i + 1 = divpow2r (n + 1) i := by
  have hpi : 0 < 2 ^ i := Nat.two_pow_pos i
  have h2 : 2 ^ (i + 1) = 2 ^ i + 2 ^ i := two_pow_succ' i
  have hq := Nat.div_add_mod n (2 ^ (i + 1))
  rw [h] at hq
  set q := n / 2 ^ (i + 1) with hqdef
  have hT : 2 ^ (i + 1) * (q + 1) = 2 ^ (i + 1) * q + 2 ^ (i + 1) := by ring
  unfold divpow2r
  have e1 : n + 2 ^ i = 2 ^ (i + 1) * q + (2 ^ (i + 1) - 1) := by omega
  have e2 : n + 1 + 2 ^ i = 2 ^ (i + 1) * (q + 1) := by omega
  rw [e1, e2, Nat.mul_div_cancel_left _ (Nat.two_pow_pos _),
    Nat.mul_add_div (Nat.two_pow_pos _), Nat.div_eq_of_lt (by omega)]

/-- Coq `divpow2r_eq`: away from the flip point, `divpow2r` is unchanged. -/
lemma divpow2r_eq {n i : ℕ} (h : n % 2 ^ (i + 1) ≠ 2 ^ i - 1) :
    divpow2r n i = divpow2r (n + 1) i := by
  have hpi : 0 < 2 ^ i := Nat.two_pow_pos i
  have h2 : 2 ^ (i + 1) = 2 ^ i + 2 ^ i := two_pow_succ' i
  have hq := Nat.div_add_mod n (2 ^ (i + 1))
  have hr : n % 2 ^ (i + 1) < 2 ^ (i + 1) := Nat.mod_lt _ (Nat.two_pow_pos _)
  set q := n / 2 ^ (i + 1) with hqdef
  set r := n % 2 ^ (i + 1) with hrdef
  unfold divpow2r
  have e1 : n + 2 ^ i = 2 ^ (i + 1) * q + (r + 2 ^ i) := by omega
  have e2 : n + 1 + 2 ^ i = 2 ^ (i + 1) * q + (r + 1 + 2 ^ i) := by omega
  rw [e1, e2, Nat.mul_add_div (Nat.two_pow_pos _), Nat.mul_add_div (Nat.two_pow_pos _)]
  rcases Nat.lt_or_ge r (2 ^ i - 1) with hc | hc
  · rw [Nat.div_eq_of_lt (by omega), Nat.div_eq_of_lt (by omega)]
  · have hc2 : 2 ^ i ≤ r := by omega
    have hd1 : (r + 2 ^ i) / 2 ^ (i + 1) = 1 :=
      Nat.div_eq_of_lt_le (by omega) (by omega)
    have hd2 : (r + 1 + 2 ^ i) / 2 ^ (i + 1) = 1 :=
      Nat.div_eq_of_lt_le (by omega) (by omega)
    rw [hd1, hd2]

/-- Coq `divpow2r_d_lt`: digits strictly below the flip run are unchanged. -/
lemma divpow2r_d_lt {i n : ℕ} (h : i < n) (xs : List Bool) :
    divpow2r (binaryToNat (List.replicate n true ++ false :: xs)) i
      = divpow2r (binaryToNat (List.replicate n false ++ true :: xs)) i := by
  rw [← binaryToNat_succ, binaryToNat_replicate_true_append]
  apply divpow2r_eq
  set b := binaryToNat (false :: xs) with hbdef
  have hsplit : (2:ℕ) ^ n = 2 ^ (i + 1) * 2 ^ (n - (i + 1)) := by
    rw [← pow_add]; congr 1; omega
  have hK : 0 < 2 ^ (n - (i + 1)) := Nat.two_pow_pos _
  have hA : 0 < 2 ^ (i + 1) := Nat.two_pow_pos _
  have hI : 0 < 2 ^ i := Nat.two_pow_pos i
  have h2 : 2 ^ (i + 1) = 2 ^ i + 2 ^ i := two_pow_succ' i
  have hle : 2 ^ (i + 1) ≤ 2 ^ n := by
    rw [hsplit]; exact Nat.le_mul_of_pos_right _ hK
  have e1 : b * 2 ^ n = b * 2 ^ (n - (i + 1)) * 2 ^ (i + 1) := by
    rw [hsplit]; ring
  have e3 : (2 ^ (n - (i + 1)) - 1) * 2 ^ (i + 1) = 2 ^ n - 2 ^ (i + 1) := by
    rw [Nat.sub_mul, one_mul, mul_comm, ← hsplit]
  have hadd : 2 ^ (i + 1) * (b * 2 ^ (n - (i + 1)) + (2 ^ (n - (i + 1)) - 1))
      = b * 2 ^ (n - (i + 1)) * 2 ^ (i + 1) + (2 ^ (n - (i + 1)) - 1) * 2 ^ (i + 1) := by
    ring
  have hmod : (b * 2 ^ n + 2 ^ n - 1) % 2 ^ (i + 1) = 2 ^ (i + 1) - 1 := by
    rw [show b * 2 ^ n + 2 ^ n - 1
        = 2 ^ (i + 1) * (b * 2 ^ (n - (i + 1)) + (2 ^ (n - (i + 1)) - 1))
          + (2 ^ (i + 1) - 1) by rw [hadd]; omega,
      Nat.mul_add_mod, Nat.mod_eq_of_lt (by omega)]
  rw [hmod]
  omega

/-- Coq `divpow2r_d_eq`: the digit at the top of the flip run increments. -/
lemma divpow2r_d_eq (n : ℕ) (xs : List Bool) :
    divpow2r (binaryToNat (List.replicate n true ++ false :: xs)) n + 1
      = divpow2r (binaryToNat (List.replicate n false ++ true :: xs)) n := by
  rw [← binaryToNat_succ, binaryToNat_replicate_true_append]
  apply divpow2r_inc
  have hI : 0 < 2 ^ n := Nat.two_pow_pos n
  have h2 : 2 ^ (n + 1) = 2 ^ n + 2 ^ n := two_pow_succ' n
  have e1 : binaryToNat (false :: xs) * 2 ^ n = 2 ^ (n + 1) * binaryToNat xs := by
    rw [binaryToNat_cons_false, pow_succ]; ring
  rw [show binaryToNat (false :: xs) * 2 ^ n + 2 ^ n - 1
      = 2 ^ (n + 1) * binaryToNat xs + (2 ^ n - 1) by rw [← e1]; omega,
    Nat.mul_add_mod, Nat.mod_eq_of_lt (by omega)]

/-- Coq `divpow2r_d_gt`: digits strictly above the flip run are unchanged. -/
lemma divpow2r_d_gt {i n : ℕ} (h : n < i) (xs : List Bool) :
    divpow2r (binaryToNat (List.replicate n true ++ false :: xs)) i
      = divpow2r (binaryToNat (List.replicate n false ++ true :: xs)) i := by
  rw [← binaryToNat_succ, binaryToNat_replicate_true_append]
  apply divpow2r_eq
  intro hcontra
  have hdvd : (2:ℕ) ^ (n + 1) ∣ 2 ^ (i + 1) := pow_dvd_pow 2 (by omega)
  have hIn : 0 < 2 ^ n := Nat.two_pow_pos n
  have h2n : 2 ^ (n + 1) = 2 ^ n + 2 ^ n := two_pow_succ' n
  have e1 : binaryToNat (false :: xs) * 2 ^ n = 2 ^ (n + 1) * binaryToNat xs := by
    rw [binaryToNat_cons_false, pow_succ]; ring
  have hVmod : (binaryToNat (false :: xs) * 2 ^ n + 2 ^ n - 1) % 2 ^ (n + 1)
      = 2 ^ n - 1 := by
    rw [show binaryToNat (false :: xs) * 2 ^ n + 2 ^ n - 1
        = 2 ^ (n + 1) * binaryToNat xs + (2 ^ n - 1) by rw [← e1]; omega,
      Nat.mul_add_mod, Nat.mod_eq_of_lt (by omega)]
  have hL := congrArg (· % 2 ^ (n + 1)) hcontra
  simp only [Nat.mod_mod_of_dvd _ hdvd] at hL
  rw [hVmod] at hL
  -- `(2^i - 1) % 2^(n+1) = 2^(n+1) - 1`, contradiction with `hL`.
  have hsplit : (2:ℕ) ^ i = 2 ^ (n + 1) * 2 ^ (i - (n + 1)) := by
    rw [← pow_add]; congr 1; omega
  have hK : 0 < 2 ^ (i - (n + 1)) := Nat.two_pow_pos _
  have hA : 0 < 2 ^ (n + 1) := Nat.two_pow_pos _
  have e3 : (2 ^ (i - (n + 1)) - 1) * 2 ^ (n + 1) = 2 ^ i - 2 ^ (n + 1) := by
    rw [Nat.sub_mul, one_mul, mul_comm, ← hsplit]
  have hle : 2 ^ (n + 1) ≤ 2 ^ i := by
    rw [hsplit]; exact Nat.le_mul_of_pos_right _ hK
  have e4 : 2 ^ (n + 1) * (2 ^ (i - (n + 1)) - 1)
      = (2 ^ (i - (n + 1)) - 1) * 2 ^ (n + 1) := by ring
  have hR : (2 ^ i - 1) % 2 ^ (n + 1) = 2 ^ (n + 1) - 1 := by
    rw [show 2 ^ i - 1 = 2 ^ (n + 1) * (2 ^ (i - (n + 1)) - 1) + (2 ^ (n + 1) - 1) by
        rw [e4]; omega,
      Nat.mul_add_mod, Nat.mod_eq_of_lt (by omega)]
  rw [hR] at hL
  omega

/-! ### Per-digit flip counting (Coq `Increment_a`, Proposition 2.2 step) -/

/-- The two digit shapes around an `Increment.even` step, parametrized by the
head digit `c` of the tail. -/
lemma increment_even_shapes {xs : List ℕ} (hev : AllEven xs) {y : ℕ} (hy : Odd y)
    (z : ℕ) (zs : List ℕ) :
    listToBinary (xs ++ y :: z :: zs)
        = List.replicate (xs.length + 1)
            (!xor (oddb z) ((listToBinary zs).headD false))
          ++ xor (oddb z) ((listToBinary zs).headD false) :: listToBinary zs ∧
      listToBinary (xs ++ y :: (z + 1) :: zs)
        = List.replicate (xs.length + 1)
            (xor (oddb z) ((listToBinary zs).headD false))
          ++ (!xor (oddb z) ((listToBinary zs).headD false)) :: listToBinary zs := by
  have hc : (listToBinary (z :: zs)).headD false
      = xor (oddb z) ((listToBinary zs).headD false) := by
    rw [listToBinary_cons, List.headD_cons]
  constructor
  · have h1 := listToBinary_incr_split hev hy z zs
    rw [hc] at h1
    rw [h1, listToBinary_cons]
  · have h2 := listToBinary_incr_split hev hy (z + 1) zs
    rw [listToBinary_head_succ, hc, Bool.not_not] at h2
    rw [h2, listToBinary_cons, oddb_succ, xor_not_left]

/-- `toS` of the pre-state in the even case. -/
lemma increment_even_toS {x : ℕ} (hx : Even x) {xs : List ℕ} (hev : AllEven xs)
    {y : ℕ} (hy : Odd y) (z : ℕ) (zs : List ℕ) :
    toS (x + 1, xs ++ y :: z :: zs)
      = !xor (oddb z) ((listToBinary zs).headD false) := by
  rw [toS_def, (increment_even_shapes hev hy z zs).1]
  have hde : decide (Even (x + 1)) = false := by
    simp [Nat.even_add_one, hx]
  rw [hde]
  simp [List.replicate_succ]

/-- The per-digit balance across one carry ripple: entry `z` becomes `z+1`
while the counter moves from `1^p 0 w` to `0^p 1 w`; every position balances.
Both branches of `Increment_a` are instances of this. -/
lemma digit_balance {p : ℕ} (front : List ℕ) (hlen : front.length = p)
    (z : ℕ) (zs : List ℕ) (w : List Bool) (i : ℕ) :
    (front ++ (z + 1) :: zs).getD i 0
        + divpow2r (binaryToNat (List.replicate p true ++ false :: w)) i
      = (front ++ z :: zs).getD i 0
        + divpow2r (binaryToNat (List.replicate p false ++ true :: w)) i := by
  rcases Nat.lt_trichotomy i p with hip | hip | hip
  · rw [List.getD_append _ _ _ _ (by omega), List.getD_append _ _ _ _ (by omega),
      divpow2r_d_lt (h := hip)]
  · subst hip
    rw [List.getD_append_right _ _ _ _ (by omega),
      List.getD_append_right _ _ _ _ (by omega), hlen, Nat.sub_self,
      List.getD_cons_zero, List.getD_cons_zero, ← divpow2r_d_eq]
    omega
  · obtain ⟨j, hj⟩ : ∃ j, i - p = j + 1 := ⟨i - p - 1, by omega⟩
    rw [List.getD_append_right _ _ _ _ (by omega),
      List.getD_append_right _ _ _ _ (by omega), hlen, hj, List.getD_cons_succ,
      List.getD_cons_succ, divpow2r_d_gt (h := hip)]

/-- Coq `Increment_a` (one induction step of Proposition 2.2). -/
lemma Increment_a {s1 s2 : S17} (h : Increment s1 s2) :
    if toS s1 then
      ∀ i, ai i s2 + divpow2r (toN s1) i = ai i s1 + divpow2r (toN s2) i
    else
      ∀ i, ai i s1 + divpow2r (toN s1) i = ai i s2 + divpow2r (toN s2) i := by
  rcases increment_inv h with
    ⟨x, xs, y, z, zs, hx, hnz, hev, hy, rfl, rfl⟩ | ⟨x, y, xs, hx, rfl, rfl⟩
  · -- even case
    obtain ⟨hsh1, hsh2⟩ := increment_even_shapes hev hy z zs
    have hS := increment_even_toS hx hev hy z zs
    have hlist1 : xs ++ y :: z :: zs = (xs ++ [y]) ++ z :: zs := by simp
    have hlist2 : xs ++ y :: (z + 1) :: zs = (xs ++ [y]) ++ (z + 1) :: zs := by simp
    have hlen : (xs ++ [y]).length = xs.length + 1 := by simp
    cases hcv : xor (oddb z) ((listToBinary zs).headD false) with
    | false =>
        rw [hcv] at hsh1 hsh2 hS
        simp only [Bool.not_false] at hsh1 hsh2 hS
        rw [hS, if_pos rfl]
        intro i
        show ai i (x, xs ++ y :: (z + 1) :: zs)
            + divpow2r (toN (x + 1, xs ++ y :: z :: zs)) i
          = ai i (x + 1, xs ++ y :: z :: zs)
            + divpow2r (toN (x, xs ++ y :: (z + 1) :: zs)) i
        rw [show toN (x + 1, xs ++ y :: z :: zs)
            = binaryToNat (List.replicate (xs.length + 1) true ++ false :: listToBinary zs)
            from by rw [toN_def, hsh1],
          show toN (x, xs ++ y :: (z + 1) :: zs)
            = binaryToNat (List.replicate (xs.length + 1) false ++ true :: listToBinary zs)
            from by rw [toN_def, hsh2]]
        simp only [ai, hlist1, hlist2]
        exact digit_balance (xs ++ [y]) hlen z zs (listToBinary zs) i
    | true =>
        rw [hcv] at hsh1 hsh2 hS
        simp only [Bool.not_true] at hsh1 hsh2 hS
        rw [hS, if_neg (by simp)]
        intro i
        show ai i (x + 1, xs ++ y :: z :: zs)
            + divpow2r (toN (x + 1, xs ++ y :: z :: zs)) i
          = ai i (x, xs ++ y :: (z + 1) :: zs)
            + divpow2r (toN (x, xs ++ y :: (z + 1) :: zs)) i
        rw [show toN (x + 1, xs ++ y :: z :: zs)
            = binaryToNat (List.replicate (xs.length + 1) false ++ true :: listToBinary zs)
            from by rw [toN_def, hsh1],
          show toN (x, xs ++ y :: (z + 1) :: zs)
            = binaryToNat (List.replicate (xs.length + 1) true ++ false :: listToBinary zs)
            from by rw [toN_def, hsh2]]
        simp only [ai, hlist1, hlist2]
        exact (digit_balance (xs ++ [y]) hlen z zs (listToBinary zs) i).symm
  · -- odd case: an instance of `digit_balance` with an empty front
    have hcons1 : listToBinary (y :: xs)
        = xor (oddb y) ((listToBinary xs).headD false) :: listToBinary xs := by
      rw [listToBinary_cons]
    have hcons2 : listToBinary ((y + 1) :: xs)
        = (!xor (oddb y) ((listToBinary xs).headD false)) :: listToBinary xs := by
      rw [listToBinary_cons, oddb_succ, xor_not_left]
    have hS : toS (x + 1, y :: xs) = !xor (oddb y) ((listToBinary xs).headD false) := by
      rw [toS_def, hcons1]
      have hde : decide (Even (x + 1)) = true := by
        simp [hx]
      rw [hde, List.headD_cons]
      cases xor (oddb y) ((listToBinary xs).headD false) <;> rfl
    cases hcv : xor (oddb y) ((listToBinary xs).headD false) with
    | false =>
        rw [hcv] at hcons1 hcons2 hS
        simp only [Bool.not_false] at hcons2 hS
        rw [hS, if_pos rfl]
        intro i
        show ai i (x, (y + 1) :: xs) + divpow2r (toN (x + 1, y :: xs)) i
          = ai i (x + 1, y :: xs) + divpow2r (toN (x, (y + 1) :: xs)) i
        rw [show toN (x + 1, y :: xs)
            = binaryToNat (List.replicate 0 true ++ false :: listToBinary xs)
            from by rw [toN_def, hcons1]; rfl,
          show toN (x, (y + 1) :: xs)
            = binaryToNat (List.replicate 0 false ++ true :: listToBinary xs)
            from by rw [toN_def, hcons2]; rfl]
        simpa only [ai, List.nil_append] using
          digit_balance (p := 0) ([] : List ℕ) rfl y xs (listToBinary xs) i
    | true =>
        rw [hcv] at hcons1 hcons2 hS
        simp only [Bool.not_true] at hcons2 hS
        rw [hS, if_neg (by simp)]
        intro i
        show ai i (x + 1, y :: xs) + divpow2r (toN (x + 1, y :: xs)) i
          = ai i (x, (y + 1) :: xs) + divpow2r (toN (x, (y + 1) :: xs)) i
        rw [show toN (x + 1, y :: xs)
            = binaryToNat (List.replicate 0 false ++ true :: listToBinary xs)
            from by rw [toN_def, hcons1]; rfl,
          show toN (x, (y + 1) :: xs)
            = binaryToNat (List.replicate 0 true ++ false :: listToBinary xs)
            from by rw [toN_def, hcons2]; rfl]
        simpa only [ai, List.nil_append] using
          (digit_balance (p := 0) ([] : List ℕ) rfl y xs (listToBinary xs) i).symm

/-! ### `Increments` closure (Proposition 2.2) -/

lemma Increment_fst {s1 s2 : S17} (h : Increment s1 s2) : s1.1 = s2.1 + 1 := by
  rcases increment_inv h with
    ⟨x, xs, y, z, zs, _, _, _, _, rfl, rfl⟩ | ⟨x, y, xs, _, rfl, rfl⟩ <;> rfl

lemma Increments_sgn {n : ℕ} {s1 s2 : S17} (h : Increments n s1 s2) :
    toS s1 = toS s2 := by
  induction h with
  | zero s => rfl
  | succ h1 _ ih => rw [Increment_sgn h1, ih]

lemma Increments_len {n : ℕ} {s1 s2 : S17} (h : Increments n s1 s2) :
    toL s1 = toL s2 := by
  induction h with
  | zero s => rfl
  | succ h1 _ ih => rw [Increment_len h1, ih]

lemma Increments_n {n : ℕ} {s1 s2 : S17} (h : Increments n s1 s2) :
    if toS s1 then toN s1 + n = toN s2 else toN s1 = toN s2 + n := by
  induction h with
  | zero s => cases hs : toS s <;> simp
  | @succ n s1 s2 s3 h1 h2 ih =>
      have hsgn := Increment_sgn h1
      have hn := Increment_n h1
      rw [← hsgn] at ih
      cases hs : toS s1 <;> rw [hs] at ih hn <;> simp at ih hn ⊢ <;> omega

lemma Increments_a {n : ℕ} {s1 s2 : S17} (h : Increments n s1 s2) :
    if toS s1 then
      ∀ i, ai i s2 + divpow2r (toN s1) i = ai i s1 + divpow2r (toN s2) i
    else
      ∀ i, ai i s1 + divpow2r (toN s1) i = ai i s2 + divpow2r (toN s2) i := by
  induction h with
  | zero s => cases hs : toS s <;> simp
  | @succ n s1 s2 s3 h1 h2 ih =>
      have hsgn := Increment_sgn h1
      have hd := Increment_a h1
      rw [← hsgn] at ih
      cases hs : toS s1 <;> rw [hs] at ih hd <;> simp at ih hd ⊢ <;> intro i <;>
        have h1i := ih i <;> have h2i := hd i <;> omega

lemma Increments_a0 {n : ℕ} {s1 s2 : S17} (h : Increments n s1 s2) :
    if toS s1 then s1.1 + toN s1 = s2.1 + toN s2
    else s2.1 + toN s1 = s1.1 + toN s2 := by
  induction h with
  | zero s => cases hs : toS s <;> simp
  | @succ n s1 s2 s3 h1 h2 ih =>
      have hsgn := Increment_sgn h1
      have hn := Increment_n h1
      have hfst := Increment_fst h1
      rw [← hsgn] at ih
      cases hs : toS s1 <;> rw [hs] at ih hn <;> simp at ih hn ⊢ <;> omega

lemma Increment_a0 {s1 s2 : S17} (h : Increment s1 s2) :
    if toS s1 then s1.1 + toN s1 = s2.1 + toN s2
    else s2.1 + toN s1 = s1.1 + toN s2 :=
  Increments_a0 (Increments.succ h (Increments.zero s2))

/-! ### Decomposition and zero-counter lemmas (Coq lines 1630–1846) -/

/-- Coq `Forall_Even_dec`: split a list at its first odd entry. -/
lemma allEven_dec (xs : List ℕ) :
    AllEven xs ∨ ∃ xs0 y zs, AllEven xs0 ∧ Odd y ∧ xs = xs0 ++ y :: zs := by
  induction xs with
  | nil => exact .inl fun a ha => absurd ha (by simp)
  | cons a xs ih =>
      rcases Nat.even_or_odd a with ha | ha
      · rcases ih with h | ⟨xs0, y, zs, h0, h1, rfl⟩
        · refine .inl fun b hb => ?_
          rcases List.mem_cons.1 hb with rfl | hb
          exacts [ha, h b hb]
        · refine .inr ⟨a :: xs0, y, zs, fun b hb => ?_, h1, rfl⟩
          rcases List.mem_cons.1 hb with rfl | hb
          exacts [ha, h0 b hb]
      · exact .inr ⟨[], a, xs, fun b hb => absurd hb (by simp), ha, rfl⟩

/-- Coq `to_n_Even`. -/
lemma toN_allEven {x : ℕ} {xs : List ℕ} (h : AllEven xs) : toN (x, xs) = 0 := by
  rw [toN_def]
  have h1 := listToBinary_allEven_prefix h []
  simp only [listToBinary_nil, List.headD_nil, List.append_nil] at h1
  rw [h1, binaryToNat_replicate_false]

/-- Coq `to_n_0_binary_0_Even`. -/
lemma toN_zero_shape : ∀ {xs : List ℕ}, binaryToNat (listToBinary xs) = 0 →
    listToBinary xs = List.replicate xs.length false ∧ AllEven xs
  | [], _ => ⟨rfl, fun a ha => absurd ha (by simp)⟩
  | a :: xs, h => by
      rw [listToBinary_cons] at h
      have hb : xor (oddb a) ((listToBinary xs).headD false) = false ∧
          binaryToNat (listToBinary xs) = 0 := by
        cases hx : xor (oddb a) ((listToBinary xs).headD false)
        · rw [hx, binaryToNat_cons_false] at h
          exact ⟨rfl, by omega⟩
        · rw [hx, binaryToNat_cons_true] at h
          exact absurd h (by omega)
      obtain ⟨I1, I2⟩ := toN_zero_shape hb.2
      have hhd : (listToBinary xs).headD false = false := by
        rw [I1]
        cases hxl : xs.length <;> simp [List.replicate_succ]
      have hodda : oddb a = false := by
        have hb1 := hb.1
        rw [hhd] at hb1
        simpa using hb1
      constructor
      · rw [listToBinary_cons, hb.1, I1, List.length_cons, List.replicate_succ]
      · intro b hb'
        rcases List.mem_cons.1 hb' with rfl | hb''
        exacts [oddb_eq_false_iff.1 hodda, I2 b hb'']

/-- Coq `to_n_0_Even`. -/
lemma toN_zero_allEven {x : ℕ} {xs : List ℕ} (h : toN (x, xs) = 0) : AllEven xs :=
  (toN_zero_shape (by rwa [toN_def] at h)).2

/-! ### WF machinery -/

/-- Coq `WF`. -/
inductive WF : S17 → Prop
  | one {s : S17} : WF1 s → WF s
  | two {s : S17} : WF2 s → WF s

lemma wf1_inv {s : S17} (h : WF1 s) :
    ∃ x xs y, Nonzero xs ∧ s = (x, xs ++ [y]) := by
  cases h with | intro x xs y hnz => exact ⟨x, xs, y, hnz, rfl⟩

lemma wf2_inv {s : S17} (h : WF2 s) :
    ∃ x xs y zs, Nonzero xs ∧ AllEven xs ∧ Odd y ∧ Nonzero zs ∧
      s = (x, xs ++ y :: (zs ++ [0, 0])) := by
  cases h with | intro x xs y zs hnz hev hy hnzz => exact ⟨x, xs, y, zs, hnz, hev, hy, hnzz, rfl⟩

/-- Coq `WF1_00`. -/
lemma WF1_00 (x : ℕ) (xs : List ℕ) : ¬ WF1 (x, xs ++ [0, 0]) := by
  intro h
  obtain ⟨x', xs', y', hnz, heq⟩ := wf1_inv h
  have hl : xs ++ [0, 0] = xs' ++ [y'] := congrArg Prod.snd heq
  have h00 : (xs ++ [0]) ++ [0] = xs' ++ [y'] := by rw [← hl]; simp
  obtain ⟨hxs', hy⟩ := List.append_inj' h00 rfl
  exact hnz 0 (by rw [← hxs']; simp) rfl

/-- Coq `WF_nonempty`. -/
lemma WF_nonempty {x : ℕ} {xs : List ℕ} (h : WF (x, xs)) : xs ≠ [] := by
  cases h with
  | one h1 =>
      obtain ⟨_, xs', y', _, heq⟩ := wf1_inv h1
      have hx : xs = xs' ++ [y'] := congrArg Prod.snd heq
      rw [hx]
      simp
  | two h2 =>
      obtain ⟨_, xs', y', zs', _, _, _, _, heq⟩ := wf2_inv h2
      have hx : xs = xs' ++ y' :: (zs' ++ [0, 0]) := congrArg Prod.snd heq
      rw [hx]
      simp

/-- Coq `to_n_pow2sub1`: a full counter forces the shape. -/
lemma toN_pow2sub1 : ∀ (xs : List ℕ) (y : ℕ),
    binaryToNat (listToBinary (xs ++ [y, 0, 0])) = 2 ^ (xs.length + 1) - 1 →
    (listToBinary (xs ++ [y, 0, 0])).headD false = true ∧ AllEven xs ∧ Odd y
  | [], y => by
      intro h
      simp only [List.nil_append, List.length_nil] at h ⊢
      have hl : listToBinary [y, 0, 0] = [oddb y, false, false] := by
        simp [listToBinary_cons, listToBinary_nil, show oddb 0 = false from rfl]
      rw [hl] at h ⊢
      cases hy : oddb y
      · simp [binaryToNat] at h
        exact absurd h (Nat.not_odd_iff_even.2 (oddb_eq_false_iff.1 hy))
      · exact ⟨rfl, fun a ha => absurd ha (by simp), oddb_eq_true_iff.1 hy⟩
  | a :: xs, y => by
      intro h
      rw [List.cons_append, listToBinary_cons] at h
      have hpow : 0 < 2 ^ (xs.length + 1) := Nat.two_pow_pos _
      have h2 : (2:ℕ) ^ (xs.length + 1 + 1) = 2 ^ (xs.length + 1) + 2 ^ (xs.length + 1) :=
        two_pow_succ' _
      simp only [List.length_cons] at h
      have hb : xor (oddb a) ((listToBinary (xs ++ [y, 0, 0])).headD false) = true ∧
          binaryToNat (listToBinary (xs ++ [y, 0, 0])) = 2 ^ (xs.length + 1) - 1 := by
        cases hx : xor (oddb a) ((listToBinary (xs ++ [y, 0, 0])).headD false) <;>
          rw [hx] at h <;> simp at h ⊢ <;> omega
      obtain ⟨I1, I2, I3⟩ := toN_pow2sub1 xs y hb.2
      have hodda : oddb a = false := by
        have hb1 := hb.1
        rw [I1] at hb1
        cases ha : oddb a <;> rw [ha] at hb1
        simp at hb1 ⊢
      refine ⟨?_, ?_, I3⟩
      · rw [List.cons_append, listToBinary_cons, List.headD_cons, hodda, I1]
        rfl
      · intro b hb'
        rcases List.mem_cons.1 hb' with rfl | hb''
        exacts [oddb_eq_false_iff.1 hodda, I2 b hb'']

/-- Any counter over a list ending in `[0, 0]` is small (core of Coq `WF2_n_lt`). -/
lemma toN_append_00_lt : ∀ (l : List ℕ),
    binaryToNat (listToBinary (l ++ [0, 0])) < 2 ^ l.length
  | [] => by
      simp [listToBinary_cons, listToBinary_nil, show oddb 0 = false from rfl]
  | a :: l => by
      have ih := toN_append_00_lt l
      rw [List.cons_append, listToBinary_cons]
      have h2 : (2:ℕ) ^ (l.length + 1) = 2 ^ l.length + 2 ^ l.length := two_pow_succ' _
      cases hx : xor (oddb a) ((listToBinary (l ++ [0, 0])).headD false) <;>
        simp [List.length_cons, h2] <;> omega

/-- Coq `WF2_n_lt`. -/
lemma WF2_n_lt {s1 : S17} (h : WF2 s1) : toN s1 < 2 ^ (toL s1 - 2) := by
  obtain ⟨x, xs, y, zs, _, _, _, _, rfl⟩ := wf2_inv h
  rw [toN_def, toL_def]
  have hb := toN_append_00_lt (xs ++ y :: zs)
  have e : (xs ++ y :: zs) ++ [0, 0] = xs ++ y :: (zs ++ [0, 0]) := by simp
  rw [e] at hb
  have hlen : (xs ++ y :: (zs ++ [0, 0])).length - 2 = (xs ++ y :: zs).length := by
    simp
    omega
  rw [hlen]
  exact hb

/-! ### Nonzero/AllEven bookkeeping -/

lemma odd_ne_zero {y : ℕ} (h : Odd y) : y ≠ 0 := by
  rcases h with ⟨k, rfl⟩; omega

lemma nonzero_nil : Nonzero [] := fun a ha => absurd ha (by simp)

lemma nonzero_cons {a : ℕ} {xs : List ℕ} (ha : a ≠ 0) (h : Nonzero xs) :
    Nonzero (a :: xs) := by
  intro b hb; rcases List.mem_cons.1 hb with rfl | hb; exacts [ha, h b hb]

lemma nonzero_append {xs ys : List ℕ} (h1 : Nonzero xs) (h2 : Nonzero ys) :
    Nonzero (xs ++ ys) := by
  intro a ha; rcases List.mem_append.1 ha with h | h; exacts [h1 a h, h2 a h]

lemma nonzero_singleton {a : ℕ} (ha : a ≠ 0) : Nonzero [a] :=
  nonzero_cons ha nonzero_nil

/-! ### Closed forms over an all-even prefix -/

/-- With `Even x₁` and an all-even prefix, the direction bit is `oddb y`. -/
lemma toS_allEven_prefix {x1 : ℕ} (hx : Even x1) {xs : List ℕ} (hev : AllEven xs)
    (y : ℕ) : toS (x1 + 1, xs ++ [y]) = oddb y := by
  rw [toS_def, listToBinary_allEven_prefix hev, headD_replicate_append_self]
  have hde : decide (Even (x1 + 1)) = false := by
    simp [Nat.even_add_one, hx]
  rw [hde]
  simp [listToBinary_cons, listToBinary_nil]

/-- All-even prefix and odd last entry: the counter is full. -/
lemma toN_allEven_prefix_odd {x : ℕ} {xs : List ℕ} (hev : AllEven xs) {y : ℕ}
    (hy : Odd y) : toN (x, xs ++ [y]) = 2 ^ (xs.length + 1) - 1 := by
  rw [toN_def, listToBinary_allEven_prefix hev]
  have hLy : listToBinary [y] = [true] := by
    simp [listToBinary_cons, listToBinary_nil, hy]
  rw [hLy]
  have : (List.replicate xs.length (([true] : List Bool).headD false) ++ [true] : List Bool)
      = List.replicate (xs.length + 1) true ++ [] := by
    rw [show (([true] : List Bool).headD false) = true from rfl,
      show ([true] : List Bool) = true :: [] from rfl, replicate_append_succ]
  rw [this]
  simp [binaryToNat_replicate_true]

/-! ### Single-step preconditions, WF1 track (Coq lines 1855–2434) -/

/-- The constructive core: an even head counter and a non-all-even list admit an
`Increment.even` step preserving `WF1`. -/
lemma increment_even_step {x1 : ℕ} {xs0 : List ℕ} {y0 : ℕ} {zs : List ℕ} {y1 : ℕ}
    (hx : Even x1) (hnz0 : Nonzero xs0) (hev0 : AllEven xs0) (hy0 : Odd y0)
    (hnzz : Nonzero zs) :
    ∃ s2, Increment (x1 + 1, (xs0 ++ y0 :: zs) ++ [y1]) s2 ∧ WF1 s2 := by
  cases zs with
  | nil =>
      refine ⟨(x1, xs0 ++ y0 :: (y1 + 1) :: []), ?_, ?_⟩
      · have h := Increment.even (x := x1) (xs := xs0) (y := y0) (z := y1) (zs := [])
          hx hnz0 hev0 hy0
        have e : (xs0 ++ y0 :: List.nil) ++ [y1] = xs0 ++ y0 :: y1 :: [] := by simp
        rw [e]
        exact h
      · have e : xs0 ++ y0 :: (y1 + 1) :: [] = (xs0 ++ [y0]) ++ [y1 + 1] := by simp
        rw [e]
        exact WF1.intro _ _ _ (nonzero_append hnz0 (nonzero_singleton (odd_ne_zero hy0)))
  | cons z zs' =>
      refine ⟨(x1, xs0 ++ y0 :: (z + 1) :: (zs' ++ [y1])), ?_, ?_⟩
      · have h := Increment.even (x := x1) (xs := xs0) (y := y0) (z := z)
          (zs := zs' ++ [y1]) hx hnz0 hev0 hy0
        have e : (xs0 ++ y0 :: z :: zs') ++ [y1] = xs0 ++ y0 :: z :: (zs' ++ [y1]) := by
          simp
        rw [e]
        exact h
      · have e : xs0 ++ y0 :: (z + 1) :: (zs' ++ [y1])
            = (xs0 ++ y0 :: (z + 1) :: zs') ++ [y1] := by simp
        rw [e]
        refine WF1.intro _ _ _ ?_
        refine nonzero_append hnz0 (nonzero_cons (odd_ne_zero hy0)
          (nonzero_cons (by omega) fun a ha => hnzz a (by simp [ha])))

/-- The constructive core for an odd head counter. -/
lemma increment_odd_step {x1 : ℕ} {XS : List ℕ} {y1 : ℕ} (hx : Odd x1)
    (hnz : Nonzero XS) :
    ∃ s2, Increment (x1 + 1, XS ++ [y1]) s2 ∧ WF1 s2 := by
  cases XS with
  | nil =>
      exact ⟨(x1, [y1 + 1]), Increment.odd hx,
        WF1.intro x1 [] (y1 + 1) nonzero_nil⟩
  | cons x2 XS' =>
      refine ⟨(x1, (x2 + 1) :: (XS' ++ [y1])), Increment.odd hx, ?_⟩
      have e : (x2 + 1) :: (XS' ++ [y1]) = ((x2 + 1) :: XS') ++ [y1] := rfl
      rw [e]
      exact WF1.intro _ _ _ (nonzero_cons (by omega)
        fun a ha => hnz a (by simp [ha]))

/-- Coq `Increment_inc_precond1`. -/
lemma Increment_inc_precond1 {s1 : S17} (h : WF1 s1) (hs : toS s1 = true)
    (hn : toN s1 < 2 ^ toL s1 - 1) (hf : 0 < s1.1) :
    ∃ s2, Increment s1 s2 ∧ WF1 s2 := by
  obtain ⟨x, XS, y1, hnz, rfl⟩ := wf1_inv h
  obtain ⟨x1, rfl⟩ : ∃ x1, x = x1 + 1 := ⟨x - 1, by
    have : 0 < x := hf
    omega⟩
  rcases Nat.even_or_odd x1 with hx | hx
  · rcases allEven_dec XS with hev | ⟨xs0, y0, zs, hev0, hy0, rfl⟩
    · exfalso
      have hts := toS_allEven_prefix hx hev y1
      rw [hs] at hts
      have hy1 : Odd y1 := oddb_eq_true_iff.1 hts.symm
      have htn := toN_allEven_prefix_odd (x := x1 + 1) hev hy1
      rw [toL_def, show (XS ++ [y1]).length = XS.length + 1 by simp] at hn
      omega
    · exact increment_even_step hx (fun a ha => hnz a (by simp [ha])) hev0 hy0
        (fun a ha => hnz a (by simp [ha]))
  · exact increment_odd_step hx hnz

/-- Coq `Increment_dec_precond1`. -/
lemma Increment_dec_precond1 {s1 : S17} (h : WF1 s1) (hs : toS s1 = false)
    (hn : 0 < toN s1) (hf : 0 < s1.1) :
    ∃ s2, Increment s1 s2 ∧ WF1 s2 := by
  obtain ⟨x, XS, y1, hnz, rfl⟩ := wf1_inv h
  obtain ⟨x1, rfl⟩ : ∃ x1, x = x1 + 1 := ⟨x - 1, by
    have : 0 < x := hf
    omega⟩
  rcases Nat.even_or_odd x1 with hx | hx
  · rcases allEven_dec XS with hev | ⟨xs0, y0, zs, hev0, hy0, rfl⟩
    · exfalso
      have hts := toS_allEven_prefix hx hev y1
      rw [hs] at hts
      have hy1 : Even y1 := oddb_eq_false_iff.1 hts.symm
      have htn : toN (x1 + 1, XS ++ [y1]) = 0 :=
        toN_allEven (fun a ha => by
          rcases List.mem_append.1 ha with h' | h'
          · exact hev a h'
          · rcases List.mem_singleton.1 h'; exact hy1)
      omega
    · exact increment_even_step hx (fun a ha => hnz a (by simp [ha])) hev0 hy0
        (fun a ha => hnz a (by simp [ha]))
  · exact increment_odd_step hx hnz

/-- Coq `Halve_precond1`. -/
lemma Halve_precond1 {s1 : S17} (h : WF1 s1) (hf : s1.1 = 0) (hl : 2 ≤ toL s1) :
    ∃ s2, Halve s1 s2 ∧ WF1 s2 := by
  obtain ⟨x, XS, y1, hnz, rfl⟩ := wf1_inv h
  obtain rfl : x = 0 := hf
  cases XS with
  | nil =>
      rw [toL_def] at hl
      simp at hl
  | cons a XS' =>
      refine ⟨(a + 1, XS' ++ [y1]), Halve.intro a (XS' ++ [y1]), ?_⟩
      exact WF1.intro _ _ _ fun b hb => hnz b (by simp [hb])

/-- Coq `dec_to_0__a0_Odd`. -/
lemma dec_to_0_a0_odd {s1 : S17} (hs : toS s1 = false) (hn : toN s1 = 0) :
    Odd s1.1 := by
  obtain ⟨x, xs⟩ := s1
  obtain ⟨I1, _⟩ := toN_zero_shape (by rwa [toN_def] at hn)
  have hhd : (listToBinary xs).headD false = false := by
    rw [I1]
    cases hxl : xs.length <;> simp [List.replicate_succ]
  rw [toS_def, hhd] at hs
  simp only [Bool.xor_false] at hs
  simpa [Nat.not_even_iff_odd] using of_decide_eq_false hs

/-- Coq `Zero_precond`. -/
lemma Zero_precond {s1 : S17} (h : WF1 s1) (hs : toS s1 = false) (hn : toN s1 = 0) :
    ∃ s2, Zero s1 s2 ∧ WF2 s2 := by
  have hodd := dec_to_0_a0_odd hs hn
  obtain ⟨x, xs, y, hnz, rfl⟩ := wf1_inv h
  obtain ⟨x1, rfl⟩ : ∃ x1, x = x1 + 1 := ⟨x - 1, by
    have := odd_ne_zero hodd
    omega⟩
  have hx1 : Even x1 := by
    have : Odd (x1 + 1) := hodd
    rcases this with ⟨k, hk⟩
    exact ⟨k, by omega⟩
  have hev : AllEven (xs ++ [y]) := toN_zero_allEven hn
  have hevxs : AllEven xs := fun a ha => hev a (by simp [ha])
  have hy : Even y := hev y (by simp)
  refine ⟨(x1, xs ++ [y + 1, 0, 0]), Zero.intro hnz hevxs hx1 hy, ?_⟩
  exact WF2.intro _ _ _ _ hnz hevxs (Even.add_one hy) nonzero_nil

/-- Coq `Overflow_precond_0`: a full counter over `xs ++ [y]` forces the shape. -/
lemma overflow_precond_0 : ∀ (xs : List ℕ) (y : ℕ),
    binaryToNat (listToBinary (xs ++ [y])) = 2 ^ (xs.length + 1) - 1 →
    AllEven xs ∧ Odd y
  | [], y => by
      intro h
      simp only [List.nil_append, List.length_nil] at h
      have hl : listToBinary [y] = [oddb y] := by
        simp [listToBinary_cons, listToBinary_nil]
      rw [hl] at h
      cases hy : oddb y
      · simp [binaryToNat] at h
        exact absurd h (Nat.not_odd_iff_even.2 (oddb_eq_false_iff.1 hy))
      · exact ⟨fun a ha => absurd ha (by simp), oddb_eq_true_iff.1 hy⟩
  | a :: xs, y => by
      intro h
      rw [List.cons_append, listToBinary_cons] at h
      have hpow : 0 < 2 ^ (xs.length + 1) := Nat.two_pow_pos _
      have h2 : (2:ℕ) ^ (xs.length + 1 + 1) = 2 ^ (xs.length + 1) + 2 ^ (xs.length + 1) :=
        two_pow_succ' _
      simp only [List.length_cons] at h
      have hb : xor (oddb a) ((listToBinary (xs ++ [y])).headD false) = true ∧
          binaryToNat (listToBinary (xs ++ [y])) = 2 ^ (xs.length + 1) - 1 := by
        cases hx : xor (oddb a) ((listToBinary (xs ++ [y])).headD false) <;>
          rw [hx] at h <;> simp at h ⊢ <;> omega
      obtain ⟨I2, I3⟩ := overflow_precond_0 xs y hb.2
      -- head digit of the tail is true, so `a` is even
      have hhd : (listToBinary (xs ++ [y])).headD false = true := by
        rw [listToBinary_allEven_prefix I2, headD_replicate_append_self]
        simp [listToBinary_cons, listToBinary_nil, I3]
      have hodda : oddb a = false := by
        have hb1 := hb.1
        rw [hhd] at hb1
        cases ha : oddb a <;> rw [ha] at hb1
        simp at hb1 ⊢
      refine ⟨?_, I3⟩
      intro b hb'
      rcases List.mem_cons.1 hb' with rfl | hb''
      exacts [oddb_eq_false_iff.1 hodda, I2 b hb'']

/-- Coq `Overflow_precond`. -/
lemma Overflow_precond {s1 : S17} (h : WF1 s1) (hs : toS s1 = true)
    (hn : toN s1 = 2 ^ toL s1 - 1) (hf : s1.1 = 1) :
    ∃ s2, Overflow s1 s2 ∧ WF1 s2 := by
  obtain ⟨x, xs, y, hnz, rfl⟩ := wf1_inv h
  obtain rfl : x = 1 := hf
  rw [toN_def, toL_def, show (xs ++ [y]).length = xs.length + 1 by simp] at hn
  obtain ⟨hev, hy⟩ := overflow_precond_0 xs y hn
  refine ⟨(1, xs ++ [y + 1, 0]), ?_, ?_⟩
  · exact Overflow.intro (x := 0) hnz hev (by simp) hy
  · have e : xs ++ [y + 1, 0] = (xs ++ [y + 1]) ++ [0] := by simp
    rw [e]
    exact WF1.intro _ _ _ (nonzero_append hnz (nonzero_singleton (by omega)))

/-! ### Iterated preconditions (Coq lines 2435–2606, WF1 track) -/

/-- Coq `Increments_inc_precond1`. -/
lemma Increments_inc_precond1 {s1 : S17} (n : ℕ) (h : WF1 s1) (hs : toS s1 = true)
    (hn : toN s1 + n < 2 ^ toL s1) (hf : n ≤ s1.1) :
    ∃ s2, Increments n s1 s2 ∧ WF1 s2 := by
  induction n generalizing s1 with
  | zero => exact ⟨s1, Increments.zero s1, h⟩
  | succ n ih =>
      obtain ⟨s4, I1, I2⟩ := Increment_inc_precond1 h hs (by omega) (by omega)
      have hsgn := Increment_sgn I1
      have hnn := Increment_n I1
      have hlen := Increment_len I1
      have hfst := Increment_fst I1
      rw [hs] at hnn
      simp at hnn
      obtain ⟨s3, X1, X2⟩ := ih I2 (by rw [← hsgn]; exact hs)
        (by rw [← hlen]; omega) (by omega)
      exact ⟨s3, Increments.succ I1 X1, X2⟩

/-- Coq `Increments_dec_precond1`. -/
lemma Increments_dec_precond1 {s1 : S17} (n : ℕ) (h : WF1 s1) (hs : toS s1 = false)
    (hn : n ≤ toN s1) (hf : n ≤ s1.1) :
    ∃ s2, Increments n s1 s2 ∧ WF1 s2 := by
  induction n generalizing s1 with
  | zero => exact ⟨s1, Increments.zero s1, h⟩
  | succ n ih =>
      obtain ⟨s4, I1, I2⟩ := Increment_dec_precond1 h hs (by omega) (by omega)
      have hsgn := Increment_sgn I1
      have hnn := Increment_n I1
      have hfst := Increment_fst I1
      rw [hs] at hnn
      simp at hnn
      obtain ⟨s3, X1, X2⟩ := ih I2 (by rw [← hsgn]; exact hs) (by omega) (by omega)
      exact ⟨s3, Increments.succ I1 X1, X2⟩

/-! ### Entry bookkeeping for `Zero`/`Overflow`/`Halve` (Coq lines 2687–2782) -/

lemma allEven_cons {a : ℕ} {xs : List ℕ} (ha : Even a) (h : AllEven xs) :
    AllEven (a :: xs) := by
  intro b hb; rcases List.mem_cons.1 hb with rfl | hb; exacts [ha, h b hb]

lemma allEven_append {xs ys : List ℕ} (h1 : AllEven xs) (h2 : AllEven ys) :
    AllEven (xs ++ ys) := by
  intro a ha; rcases List.mem_append.1 ha with h | h; exacts [h1 a h, h2 a h]

private lemma getD_pair_zero (k : ℕ) : ([0, 0] : List ℕ).getD k 0 = 0 := by
  match k with
  | 0 => rfl
  | 1 => rfl
  | (n + 2) => simp [List.getD]

private lemma getD_singleton_succ (y j : ℕ) : ([y] : List ℕ).getD (j + 1) 0 = 0 := by
  match j with
  | 0 => rfl
  | (n + 1) => simp [List.getD]

/-- Coq `Zero_a0`. -/
lemma Zero_a0 {s1 s2 : S17} (h : Zero s1 s2) : s1.1 = s2.1 + 1 := by
  obtain ⟨x, xs, y, _, _, _, _, rfl, rfl⟩ := zero_inv h; rfl

/-- Coq `Zero_a1`. -/
lemma Zero_a1 {s1 s2 : S17} (h : Zero s1 s2) (hl : 3 ≤ toL s1) :
    ai 0 s1 = ai 0 s2 := by
  obtain ⟨x, xs, y, _, _, _, _, rfl, rfl⟩ := zero_inv h
  rw [toL_def] at hl
  simp only [List.length_append, List.length_cons, List.length_nil] at hl
  obtain ⟨a, xs', rfl⟩ : ∃ a xs', xs = a :: xs' := by
    cases xs with
    | nil => simp at hl
    | cons a xs' => exact ⟨a, xs', rfl⟩
  simp [ai]

/-- Coq `Zero_a`. -/
lemma Zero_a {s1 s2 : S17} (h : Zero s1 s2) (i : ℕ) :
    ai i s1 + (if i = toL s1 - 1 then 1 else 0) = ai i s2 := by
  obtain ⟨x, xs, y, _, _, _, _, rfl, rfl⟩ := zero_inv h
  rw [toL_def, show (xs ++ [y]).length - 1 = xs.length by simp]
  simp only [ai]
  rcases Nat.lt_trichotomy i xs.length with hip | hip | hip
  · rw [if_neg (by omega), List.getD_append _ _ _ _ (by omega),
      List.getD_append _ _ _ _ (by omega)]
    omega
  · subst hip
    rw [if_pos rfl, List.getD_append_right _ _ _ _ (by omega),
      List.getD_append_right _ _ _ _ (by omega), Nat.sub_self]
    rfl
  · obtain ⟨j, hj⟩ : ∃ j, i - xs.length = j + 1 := ⟨i - xs.length - 1, by omega⟩
    rw [if_neg (by omega), List.getD_append_right _ _ _ _ (by omega),
      List.getD_append_right _ _ _ _ (by omega), hj, getD_singleton_succ,
      show ([y + 1, 0, 0] : List ℕ).getD (j + 1) 0 = ([0, 0] : List ℕ).getD j 0
        from rfl, getD_pair_zero]

/-- Coq `Overflow_a0`. -/
lemma Overflow_a0 {s1 s2 : S17} (h : Overflow s1 s2) : s1.1 = s2.1 := by
  obtain ⟨x, xs, y, _, _, _, _, rfl, rfl⟩ := overflow_inv h; rfl

/-- Coq `Overflow_a`. -/
lemma Overflow_a {s1 s2 : S17} (h : Overflow s1 s2) (i : ℕ) :
    ai i s1 + (if i = toL s1 - 1 then 1 else 0) = ai i s2 := by
  obtain ⟨x, xs, y, _, _, _, _, rfl, rfl⟩ := overflow_inv h
  rw [toL_def, show (xs ++ [y]).length - 1 = xs.length by simp]
  simp only [ai]
  rcases Nat.lt_trichotomy i xs.length with hip | hip | hip
  · rw [if_neg (by omega), List.getD_append _ _ _ _ (by omega),
      List.getD_append _ _ _ _ (by omega)]
    omega
  · subst hip
    rw [if_pos rfl, List.getD_append_right _ _ _ _ (by omega),
      List.getD_append_right _ _ _ _ (by omega), Nat.sub_self]
    rfl
  · obtain ⟨j, hj⟩ : ∃ j, i - xs.length = j + 1 := ⟨i - xs.length - 1, by omega⟩
    rw [if_neg (by omega), List.getD_append_right _ _ _ _ (by omega),
      List.getD_append_right _ _ _ _ (by omega), hj, getD_singleton_succ,
      show ([y + 1, 0] : List ℕ).getD (j + 1) 0 = ([0] : List ℕ).getD j 0 from rfl]
    match j with
    | 0 => rfl
    | j + 1 => rw [getD_singleton_succ]

/-- Coq `Halve_a0`. -/
lemma Halve_a0 {s1 s2 : S17} (h : Halve s1 s2) : s2.1 = ai 0 s1 + 1 := by
  obtain ⟨x, xs, rfl, rfl⟩ := halve_inv h
  simp [ai]

/-- Coq `Halve_a`. -/
lemma Halve_a {s1 s2 : S17} (h : Halve s1 s2) (i : ℕ) : ai i s2 = ai (i + 1) s1 := by
  obtain ⟨x, xs, rfl, rfl⟩ := halve_inv h
  simp [ai]

/-! ### WF2-track preconditions (Coq lines 1947–2330, 2472–2606) -/

/-- Head digit of `L (xs ++ [y, 0, 0])` for even prefix and odd `y`. -/
lemma headD_L_odd3 {xs : List ℕ} (hev : AllEven xs) {y : ℕ} (hy : Odd y) :
    (listToBinary (xs ++ [y, 0, 0])).headD false = true := by
  rw [listToBinary_allEven_prefix hev, headD_replicate_append_self]
  simp [listToBinary_cons, listToBinary_nil, hy]

/-- Full-counter value of `(x, xs ++ [y, 0, 0])` for even prefix and odd `y`. -/
lemma toN_L_odd3 {x : ℕ} {xs : List ℕ} (hev : AllEven xs) {y : ℕ} (hy : Odd y) :
    toN (x, xs ++ [y, 0, 0]) = 2 ^ (xs.length + 1) - 1 := by
  rw [toN_def, listToBinary_allEven_prefix hev]
  have hLy : listToBinary [y, 0, 0] = [true, false, false] := by
    simp [listToBinary_cons, listToBinary_nil, hy, show oddb 0 = false from rfl]
  rw [hLy, show (([true, false, false] : List Bool).headD false) = true from rfl,
    show ([true, false, false] : List Bool) = true :: [false, false] from rfl,
    replicate_append_succ, binaryToNat_replicate_true_append]
  simp [binaryToNat]

/-- The counter of an odd entry followed by an all-even tail is exactly `1`. -/
lemma toN_odd_cons_allEven {x y : ℕ} (hy : Odd y) {w : List ℕ} (hev : AllEven w) :
    toN (x, y :: w) = 1 := by
  rw [toN_def, listToBinary_cons]
  have h1 := listToBinary_allEven_prefix hev []
  simp only [listToBinary_nil, List.headD_nil, List.append_nil] at h1
  have hhd : (listToBinary w).headD false = false := by
    rw [h1]
    cases hxl : w.length <;> simp [List.replicate_succ]
  rw [hhd, h1]
  simp [oddb_eq_true_iff.2 hy, binaryToNat_replicate_false]

/-- Coq `Increment_inc_precond22` (`WF2 → WF2`). -/
lemma Increment_inc_precond22 {s1 : S17} (h : WF2 s1) (hs : toS s1 = true)
    (hn : toN s1 < 2 ^ (toL s1 - 2) - 1) (hf : 0 < s1.1) :
    ∃ s2, Increment s1 s2 ∧ WF2 s2 := by
  obtain ⟨x, xs, y, zs, hnz, hev, hy, hnzz, rfl⟩ := wf2_inv h
  obtain ⟨x1, rfl⟩ : ∃ x1, x = x1 + 1 := ⟨x - 1, by
    have : 0 < x := hf
    omega⟩
  rcases Nat.even_or_odd x1 with hx | hx
  · cases zs with
    | nil =>
        exfalso
        have htn : toN (x1 + 1, xs ++ y :: (([] : List ℕ) ++ [0, 0]))
            = 2 ^ (xs.length + 1) - 1 := toN_L_odd3 hev hy
        rw [toL_def] at hn
        have hlen : (xs ++ y :: (([] : List ℕ) ++ [0, 0])).length - 2
            = xs.length + 1 := by simp
        rw [hlen] at hn
        omega
    | cons z zs' =>
        refine ⟨(x1, xs ++ y :: (z + 1) :: (zs' ++ [0, 0])), ?_, ?_⟩
        · show Increment (x1 + 1, xs ++ y :: z :: (zs' ++ [0, 0]))
            (x1, xs ++ y :: (z + 1) :: (zs' ++ [0, 0]))
          exact Increment.even hx hnz hev hy
        · exact WF2.intro _ _ _ _ hnz hev hy
            (nonzero_cons (by omega) fun a ha => hnzz a (by simp [ha]))
  · cases xs with
    | nil =>
        refine ⟨(x1, (y + 1) :: (zs ++ [0, 0])), Increment.odd hx, ?_⟩
        rcases allEven_dec zs with hevz | ⟨xs0, y0, zs0, hev0, hy0, rfl⟩
        · exfalso
          have I1 : Increment (x1 + 1, ([] : List ℕ) ++ y :: (zs ++ [0, 0]))
              (x1, (y + 1) :: (zs ++ [0, 0])) := Increment.odd hx
          have hnn := Increment_n I1
          rw [hs] at hnn
          simp only [if_pos] at hnn
          have h0 : toN (x1, (y + 1) :: (zs ++ [0, 0])) = 0 :=
            toN_allEven (allEven_cons (Odd.add_one hy)
              (allEven_append hevz (by
                intro a ha
                simp at ha
                subst ha
                exact ⟨0, rfl⟩)))
          simp at hnn
          omega
        · have e : (y + 1) :: ((xs0 ++ y0 :: zs0) ++ [0, 0])
              = ((y + 1) :: xs0) ++ y0 :: (zs0 ++ [0, 0]) := by simp
          rw [e]
          exact WF2.intro _ _ _ _
            (nonzero_cons (by omega) fun a ha => hnzz a (by simp [ha]))
            (allEven_cons (Odd.add_one hy) hev0) hy0
            (fun a ha => hnzz a (by simp [ha]))
    | cons x2 xs' =>
        refine ⟨(x1, (x2 + 1) :: (xs' ++ y :: (zs ++ [0, 0]))), Increment.odd hx, ?_⟩
        have hx2 : Even x2 := hev x2 (by simp)
        have e : (x2 + 1) :: (xs' ++ y :: (zs ++ [0, 0]))
            = ([] : List ℕ) ++ (x2 + 1) :: ((xs' ++ y :: zs) ++ [0, 0]) := by simp
        rw [e]
        exact WF2.intro _ _ _ _ nonzero_nil (fun a ha => absurd ha (by simp))
          (Even.add_one hx2)
          (nonzero_append (fun a ha => hnz a (by simp [ha]))
            (nonzero_cons (odd_ne_zero hy) hnzz))

/-- Coq `Increment_inc_precond21` (`WF2 → WF1` at the sub-counter top). -/
lemma Increment_inc_precond21 {s1 : S17} (h : WF2 s1) (hs : toS s1 = true)
    (hn : toN s1 = 2 ^ (toL s1 - 2) - 1) (hf : 0 < s1.1) :
    ∃ s2, Increment s1 s2 ∧ WF1 s2 := by
  obtain ⟨x, xs, y, zs, hnz, hev, hy, hnzz, rfl⟩ := wf2_inv h
  obtain ⟨x1, rfl⟩ : ∃ x1, x = x1 + 1 := ⟨x - 1, by
    have : 0 < x := hf
    omega⟩
  cases zs with
  | cons z0 zs' =>
      exfalso
      rcases List.eq_nil_or_concat (z0 :: zs') with h' | ⟨zs0, y0, h'⟩
      · simp at h'
      · rw [toN_def, toL_def] at hn
        have e : xs ++ y :: ((z0 :: zs') ++ [0, 0])
            = (xs ++ y :: zs0) ++ [y0, 0, 0] := by
          rw [h']
          simp
        rw [e] at hn
        have hlen : ((xs ++ y :: zs0) ++ [y0, 0, 0]).length - 2
            = (xs ++ y :: zs0).length + 1 := by
          simp
          omega
        rw [hlen] at hn
        obtain ⟨_, I2, _⟩ := toN_pow2sub1 (xs ++ y :: zs0) y0 hn
        exact absurd (I2 y (by simp)) (Nat.not_even_iff_odd.2 hy)
  | nil =>
      have hhd : (listToBinary (xs ++ y :: (([] : List ℕ) ++ [0, 0]))).headD false
          = true := headD_L_odd3 hev hy
      rw [toS_def, hhd] at hs
      have hx : Even x1 := by
        rcases Nat.even_or_odd x1 with hx | hx
        · exact hx
        · exfalso
          have hde : decide (Even (x1 + 1)) = true := by
            simp [hx]
          rw [hde] at hs
          simp at hs
      refine ⟨(x1, xs ++ y :: 1 :: [0]), ?_, ?_⟩
      case _ =>
        show Increment (x1 + 1, xs ++ y :: 0 :: [0]) (x1, xs ++ y :: (0 + 1) :: [0])
        exact Increment.even hx hnz hev hy
      case _ => ?_
      have e : xs ++ y :: 1 :: [0] = (xs ++ [y, 1]) ++ [0] := by simp
      rw [e]
      exact WF1.intro _ _ _ (nonzero_append hnz (nonzero_cons (odd_ne_zero hy)
        (nonzero_singleton (by omega))))

/-- Coq `Increment_dec_precond2` (`WF2 → WF2`, decrementing). -/
lemma Increment_dec_precond2 {s1 : S17} (h : WF2 s1) (hs : toS s1 = false)
    (hn : 1 < toN s1) (hf : 0 < s1.1) :
    ∃ s2, Increment s1 s2 ∧ WF2 s2 := by
  obtain ⟨x, xs, y, zs, hnz, hev, hy, hnzz, rfl⟩ := wf2_inv h
  obtain ⟨x1, rfl⟩ : ∃ x1, x = x1 + 1 := ⟨x - 1, by
    have : 0 < x := hf
    omega⟩
  rcases Nat.even_or_odd x1 with hx | hx
  · cases zs with
    | nil =>
        exfalso
        have hhd : (listToBinary (xs ++ y :: (([] : List ℕ) ++ [0, 0]))).headD false
            = true := headD_L_odd3 hev hy
        rw [toS_def, hhd] at hs
        have hde : decide (Even (x1 + 1)) = false := by
          simp [Nat.even_add_one, hx]
        rw [hde] at hs
        simp at hs
    | cons z zs' =>
        refine ⟨(x1, xs ++ y :: (z + 1) :: (zs' ++ [0, 0])), ?_, ?_⟩
        · show Increment (x1 + 1, xs ++ y :: z :: (zs' ++ [0, 0]))
            (x1, xs ++ y :: (z + 1) :: (zs' ++ [0, 0]))
          exact Increment.even hx hnz hev hy
        · exact WF2.intro _ _ _ _ hnz hev hy
            (nonzero_cons (by omega) fun a ha => hnzz a (by simp [ha]))
  · cases xs with
    | nil =>
        refine ⟨(x1, (y + 1) :: (zs ++ [0, 0])), Increment.odd hx, ?_⟩
        rcases allEven_dec zs with hevz | ⟨xs0, y0, zs0, hev0, hy0, rfl⟩
        · exfalso
          have htn : toN (x1 + 1, ([] : List ℕ) ++ y :: (zs ++ [0, 0])) = 1 :=
            toN_odd_cons_allEven hy
              (allEven_append hevz (by
                intro a ha
                simp at ha
                subst ha
                exact ⟨0, rfl⟩))
          omega
        · have e : (y + 1) :: ((xs0 ++ y0 :: zs0) ++ [0, 0])
              = ((y + 1) :: xs0) ++ y0 :: (zs0 ++ [0, 0]) := by simp
          rw [e]
          exact WF2.intro _ _ _ _
            (nonzero_cons (by omega) fun a ha => hnzz a (by simp [ha]))
            (allEven_cons (Odd.add_one hy) hev0) hy0
            (fun a ha => hnzz a (by simp [ha]))
    | cons x2 xs' =>
        refine ⟨(x1, (x2 + 1) :: (xs' ++ y :: (zs ++ [0, 0]))), Increment.odd hx, ?_⟩
        have hx2 : Even x2 := hev x2 (by simp)
        have e : (x2 + 1) :: (xs' ++ y :: (zs ++ [0, 0]))
            = ([] : List ℕ) ++ (x2 + 1) :: ((xs' ++ y :: zs) ++ [0, 0]) := by simp
        rw [e]
        exact WF2.intro _ _ _ _ nonzero_nil (fun a ha => absurd ha (by simp))
          (Even.add_one hx2)
          (nonzero_append (fun a ha => hnz a (by simp [ha]))
            (nonzero_cons (odd_ne_zero hy) hnzz))

/-- Coq `Halve_precond2`. -/
lemma Halve_precond2 {s1 : S17} (h : WF2 s1) (hf : s1.1 = 0) (hn : toN s1 ≠ 1) :
    ∃ s2, Halve s1 s2 ∧ WF2 s2 := by
  obtain ⟨x, xs, y, zs, hnz, hev, hy, hnzz, rfl⟩ := wf2_inv h
  obtain rfl : x = 0 := hf
  cases xs with
  | nil =>
      refine ⟨(y + 1, zs ++ [0, 0]), Halve.intro y (zs ++ [0, 0]), ?_⟩
      rcases allEven_dec zs with hevz | ⟨xs0, y0, zs0, hev0, hy0, rfl⟩
      · exfalso
        have htn : toN (0, ([] : List ℕ) ++ y :: (zs ++ [0, 0])) = 1 :=
          toN_odd_cons_allEven hy
            (allEven_append hevz (by
              intro a ha
              simp at ha
              subst ha
              exact ⟨0, rfl⟩))
        exact hn htn
      · have e : (xs0 ++ y0 :: zs0) ++ [0, 0] = xs0 ++ y0 :: (zs0 ++ [0, 0]) := by
          simp
        rw [e]
        exact WF2.intro _ _ _ _ (fun a ha => hnzz a (by simp [ha])) hev0 hy0
          (fun a ha => hnzz a (by simp [ha]))
  | cons a xs' =>
      refine ⟨(a + 1, xs' ++ y :: (zs ++ [0, 0])),
        Halve.intro a (xs' ++ y :: (zs ++ [0, 0])), ?_⟩
      exact WF2.intro _ _ _ _ (fun b hb => hnz b (by simp [hb]))
        (fun b hb => hev b (by simp [hb])) hy hnzz

/-- Coq `Increments_inc_precond2`. -/
lemma Increments_inc_precond2 {s1 : S17} (n : ℕ) (h : WF2 s1) (hs : toS s1 = true)
    (hge : 2 ^ (toL s1 - 2) ≤ toN s1 + n) (hlt : toN s1 + n < 2 ^ toL s1)
    (hf : n ≤ s1.1) :
    ∃ s2, Increments n s1 s2 ∧ WF1 s2 := by
  induction n generalizing s1 with
  | zero =>
      have := WF2_n_lt h
      omega
  | succ n ih =>
      have hlt2 := WF2_n_lt h
      rcases Nat.lt_or_ge (toN s1) (2 ^ (toL s1 - 2) - 1) with hc | hc
      · obtain ⟨s4, I1, I2⟩ := Increment_inc_precond22 h hs (by omega) (by omega)
        have hsgn := Increment_sgn I1
        have hnn := Increment_n I1
        have hlen := Increment_len I1
        have hfst := Increment_fst I1
        rw [hs] at hnn
        simp at hnn
        obtain ⟨s3, X1, X2⟩ := ih I2 (by rw [← hsgn]; exact hs)
          (by rw [← hlen]; omega) (by rw [← hlen]; omega) (by omega)
        exact ⟨s3, Increments.succ I1 X1, X2⟩
      · have hceq : toN s1 = 2 ^ (toL s1 - 2) - 1 := by omega
        obtain ⟨s4, I1, I2⟩ := Increment_inc_precond21 h hs hceq (by omega)
        have hsgn := Increment_sgn I1
        have hnn := Increment_n I1
        have hlen := Increment_len I1
        have hfst := Increment_fst I1
        rw [hs] at hnn
        simp at hnn
        obtain ⟨s3, X1, X2⟩ := Increments_inc_precond1 n I2
          (by rw [← hsgn]; exact hs) (by rw [← hlen]; omega) (by omega)
        exact ⟨s3, Increments.succ I1 X1, X2⟩

/-- Coq `Increments_dec_precond2`. -/
lemma Increments_dec_precond2 {s1 : S17} (n : ℕ) (h : WF2 s1) (hs : toS s1 = false)
    (hn : n + 1 ≤ toN s1) (hf : n ≤ s1.1) :
    ∃ s2, Increments n s1 s2 ∧ WF2 s2 := by
  induction n generalizing s1 with
  | zero => exact ⟨s1, Increments.zero s1, h⟩
  | succ n ih =>
      obtain ⟨s4, I1, I2⟩ := Increment_dec_precond2 h hs (by omega) (by omega)
      have hsgn := Increment_sgn I1
      have hnn := Increment_n I1
      have hfst := Increment_fst I1
      rw [hs] at hnn
      simp at hnn
      obtain ⟨s3, X1, X2⟩ := ih I2 (by rw [← hsgn]; exact hs) (by omega) (by omega)
      exact ⟨s3, Increments.succ I1 X1, X2⟩

/-! ## Level 4: `weakly_embanked` / `embanked` (Coq lines 2606–2684) -/

/-- Coq `weakly_embanked` (Proposition 3.4 packaging): the composite
`Zero, Increments(dec), Halve, Increments(inc), Halve` with all counter
bookkeeping.  The four ℕ indices are `s_1 = toN s3`, `h_1 = toN s4`,
`s_2 = toN s5`, `h_2 = toN s6`. -/
inductive WeaklyEmbanked : S17 → S17 → ℕ → ℕ → ℕ → ℕ → Prop
  | intro (n1 n2 : ℕ) (s1 s2 s3 s4 s5 s6 : S17)
      (Z12 : Zero s1 s2)
      (I23 : Increments n1 s2 s3)
      (H34 : Halve s3 s4)
      (I45 : Increments (n2 + 1) s4 s5)
      (H56 : Halve s5 s6)
      (hwf1 : WF1 s1)
      (hs1s : toS s1 = false)
      (hs1n : toN s1 = 0)
      (hs1l : 3 ≤ toL s1)
      (hs1a0_odd : Odd s1.1)
      (hs1a0_lt : s1.1 < 2 ^ toL s1 - 1)
      (hs1a1_lt : ai 0 s1 < 3 * 2 ^ (toL s1 - 1))
      (hwf6 : WF1 s6)
      (hs6s : toS s6 = false)
      (hs6l : toL s6 = toL s1)
      (n34 : toN s4 = toN s3 / 2)
      (n56 : toN s6 = toN s5 / 2)
      (n3e : toN s3 + s1.1 = 2 ^ toL s1)
      (n4e : toN s4 + s1.1 / 2 + 1 = 2 ^ (toL s1 - 1))
      (n5e : toN s5 = ai 0 s1 + 2 ^ (toL s1 - 1))
      (n6e : toN s6 = ai 0 s1 / 2 + 2 ^ (toL s1 - 2))
      (a60 : ai 1 s1 + 2 ^ (toL s1 - 2) + divpow2r (toN s5) 0 + 1
        = s6.1 + divpow2r (toN s4) 0 + divpow2r (toN s3) 1)
      (a6 : ∀ i, ai (i + 2) s1 + (if i + 2 = toL s1 - 1 then 1 else 0)
          + divpow2r (2 ^ toL s1 - 1) (i + 2) + divpow2r (toN s5) (i + 1)
        = ai i s6 + divpow2r (toN s4) (i + 1) + divpow2r (toN s3) (i + 2)) :
      WeaklyEmbanked s1 s6 (toN s3) (toN s4) (toN s5) (toN s6)

/-- Coq `embanked`: a `weakly_embanked` followed by `Increments(dec), Zero`
(with the `Zero` undone in the bookkeeping). -/
inductive Embanked : S17 → S17 → ℕ → ℕ → ℕ → ℕ → Prop
  | intro (n1 : ℕ) (s1 s6 s7 s8 : S17) (s_1 h_1 s_2 h_2 : ℕ)
      (hwemb : WeaklyEmbanked s1 s6 s_1 h_1 s_2 h_2)
      (I67 : Increments n1 s6 s7)
      (Z78 : Zero s7 s8)
      (h_a60_ge_n6 : h_2 ≤ s6.1)
      (a70 : ai 1 s1 + 2 ^ (toL s1 - 2) + divpow2r s_2 0 - toN s7 + 1
        = s7.1 + h_2 + divpow2r h_1 0 + divpow2r s_1 1)
      (a7 : ∀ i, ai (i + 2) s1 + (if i + 2 = toL s1 - 1 then 1 else 0)
          + divpow2r (2 ^ toL s1 - 1) (i + 2) + divpow2r s_2 (i + 1) + divpow2r h_2 i
        = ai i s7 + divpow2r h_1 (i + 1) + divpow2r s_1 (i + 2))
      (hwf7 : WF1 s7)
      (hs7s : toS s7 = false)
      (hs7n : toN s7 = 0)
      (hleq : toL s1 = toL s7) :
      Embanked s1 s7 s_1 h_1 s_2 h_2

/-- Coq `Add2`: state `s2` is `s1` with `ai' i0` bumped by two. -/
inductive Add2 : ℕ → S17 → S17 → Prop
  | intro (i0 : ℕ) (s1 s2 : S17)
      (h : ∀ i, ai' i s1 + (if i = i0 then 2 else 0) = ai' i s2) :
      Add2 i0 s1 s2

/-! ### div2 helpers (Coq lines 2820–2938) -/

lemma pow2_split {n : ℕ} (h : n ≠ 0) : 2 ^ n = 2 ^ (n - 1) + 2 ^ (n - 1) := by
  conv_lhs => rw [show n = (n - 1) + 1 by omega]
  exact two_pow_succ' _

lemma div2ceil_pow2sub1 {n : ℕ} (h : n ≠ 0) : (2 ^ n - 1 + 1) / 2 = 2 ^ (n - 1) := by
  have e := pow2_split h
  have := Nat.two_pow_pos (n - 1)
  omega

lemma divpow2r_zero (n : ℕ) : divpow2r n 0 = (n + 1) / 2 := by
  unfold divpow2r
  norm_num

lemma div2ceil_div2floor_odd {n : ℕ} (h : Odd n) : (n + 1) / 2 = n / 2 + 1 := by
  obtain ⟨k, rfl⟩ := h
  omega

lemma div2ceil_div2floor_even {n : ℕ} (h : Even n) : (n + 1) / 2 = n / 2 := by
  obtain ⟨k, rfl⟩ := h
  omega

lemma div2_add_odd {n1 n2 : ℕ} (h1 : Odd n1) (h2 : Odd n2) :
    n1 / 2 + n2 / 2 + 1 = (n1 + n2) / 2 := by
  obtain ⟨k, rfl⟩ := h1
  obtain ⟨j, rfl⟩ := h2
  omega

lemma pow2_div2 {i : ℕ} (h : i ≠ 0) : 2 ^ i / 2 = 2 ^ (i - 1) := by
  have e := pow2_split h
  omega

lemma pow2_add (i : ℕ) : 2 ^ i + 2 ^ i = 2 ^ (i + 1) := (two_pow_succ' i).symm

lemma pow2_even {i : ℕ} (h : i ≠ 0) : Even (2 ^ i) := ⟨2 ^ (i - 1), pow2_split h⟩

lemma div2_add2 (a : ℕ) : (a + 2) / 2 = a / 2 + 1 := by omega

/-! ### Proposition 3.4: `weakly_embanked_precond` (Coq lines 2945–3168) -/

lemma weakly_embanked_precond {s1 : S17} (hwf1 : WF1 s1) (hs1s : toS s1 = false)
    (hs1n : toN s1 = 0) (hs1l : 3 ≤ toL s1) (hs1a0_odd : Odd s1.1)
    (hs1a0_lt : s1.1 < 2 ^ toL s1 - 1) (hs1a1_lt : ai 0 s1 < 3 * 2 ^ (toL s1 - 1)) :
    ∃ s6 s_1 h_1 s_2 h_2, WeaklyEmbanked s1 s6 s_1 h_1 s_2 h_2 := by
  have hpow1 : 0 < 2 ^ toL s1 := Nat.two_pow_pos _
  have hpowl1 : 0 < 2 ^ (toL s1 - 1) := Nat.two_pow_pos _
  have hpowl2 : 0 < 2 ^ (toL s1 - 2) := Nat.two_pow_pos _
  have hsplit1 : 2 ^ toL s1 = 2 ^ (toL s1 - 1) + 2 ^ (toL s1 - 1) := by
    conv_lhs => rw [show toL s1 = (toL s1 - 1) + 1 by omega]
    exact two_pow_succ' _
  have hsplit2 : 2 ^ (toL s1 - 1) = 2 ^ (toL s1 - 2) + 2 ^ (toL s1 - 2) := by
    conv_lhs => rw [show toL s1 - 1 = (toL s1 - 2) + 1 by omega]
    exact two_pow_succ' _
  -- Zero step
  obtain ⟨s2, Z12, hwf2⟩ := Zero_precond hwf1 hs1s hs1n
  have hs2s := Zero_sgn Z12
  have hs2n := Zero_n Z12
  have hs2l := Zero_len Z12
  have hs2a0 := Zero_a0 Z12
  have hs2a1 := Zero_a1 Z12 hs1l
  have hs2a := Zero_a Z12
  have hs2a0_even : Even s2.1 := by
    rcases hs1a0_odd with ⟨k, hk⟩
    exact ⟨k, by omega⟩
  have hs2n_odd : Odd (toN s2) := ⟨2 ^ (toL s1 - 1) - 1, by omega⟩
  -- Increments (decrement) by `s2.1`
  obtain ⟨s3, I23, hwf3⟩ := Increments_dec_precond2 s2.1 hwf2 hs2s
    (by omega) (le_refl _)
  have hs3s := Increments_sgn I23
  have hs3n := Increments_n I23
  have hs3l := Increments_len I23
  have hs3a0 := Increments_a0 I23
  have hs3a := Increments_a I23
  rw [hs2s] at hs3n hs3a0 hs3a
  simp only [Bool.false_eq_true, if_false] at hs3n hs3a0 hs3a
  have hs3a0_0 : s3.1 = 0 := by omega
  have hs3n_odd : Odd (toN s3) := by
    rcases hs2n_odd with ⟨k, hk⟩
    rcases hs2a0_even with ⟨j, hj⟩
    exact ⟨k - j, by omega⟩
  have hs3n_gt1 : 1 < toN s3 := by omega
  -- Halve
  obtain ⟨s4, H34, hwf4⟩ := Halve_precond2 hwf3 hs3a0_0 (by omega)
  have hs4s := Halve_sgn H34
  have hs4n := Halve_n H34
  have hs4l := Halve_len H34
  have hs4a0 := Halve_a0 H34
  have hs4a := Halve_a H34
  have hs3s' : toS s3 = false := by rw [← hs3s]; exact hs2s
  have hs4s' : toS s4 = true := by rw [← hs4s, hs3s']; rfl
  -- counter waypoints after the first halve
  have hd2 : divpow2r (toN s2) 0 = 2 ^ (toL s1 - 1) := by
    rw [divpow2r_zero, hs2n]
    omega
  have hd3 : divpow2r (toN s3) 0 = toN s3 / 2 + 1 := by
    rw [divpow2r_zero]
    exact div2ceil_div2floor_odd hs3n_odd
  have hs3a1 := hs3a 0
  rw [hd2, hd3] at hs3a1
  have h_a11_a40 : ai 0 s1 + 2 ^ (toL s1 - 1) = s4.1 + toN s3 / 2 := by omega
  have hn3_expr : toN s3 + s1.1 = 2 ^ toL s1 := by omega
  have ha10_odd2 : s1.1 % 2 = 1 := Nat.odd_iff.1 hs1a0_odd
  have hn3_odd2 : toN s3 % 2 = 1 := Nat.odd_iff.1 hs3n_odd
  have hn4_expr : toN s4 + s1.1 / 2 + 1 = 2 ^ (toL s1 - 1) := by omega
  have hl4 : toL s4 = toL s1 + 1 := by omega
  -- Increments (increment) by `s4.1`
  obtain ⟨s5, I45, hwf5⟩ := Increments_inc_precond2 s4.1 hwf4 hs4s'
    (by rw [hl4, show toL s1 + 1 - 2 = toL s1 - 1 by omega]; omega)
    (by rw [hl4, show (2:ℕ) ^ (toL s1 + 1) = 2 ^ toL s1 + 2 ^ toL s1 from
        two_pow_succ' _]; omega)
    (le_refl _)
  have hs5s := Increments_sgn I45
  have hs5n := Increments_n I45
  have hs5l := Increments_len I45
  have hs5a0 := Increments_a0 I45
  have hs5a := Increments_a I45
  rw [hs4s'] at hs5n hs5a0 hs5a
  simp only [if_true] at hs5n hs5a0 hs5a
  have hs5a0_0 : s5.1 = 0 := by omega
  have hn5_expr : toN s5 = ai 0 s1 + 2 ^ (toL s1 - 1) := by omega
  -- final Halve
  obtain ⟨s6, H56, hwf6⟩ := Halve_precond1 hwf5 hs5a0_0 (by omega)
  have hs6s := Halve_sgn H56
  have hs6n := Halve_n H56
  have hs6l := Halve_len H56
  have hs6a0 := Halve_a0 H56
  have hs6a := Halve_a H56
  have hs5s' : toS s5 = true := by rw [← hs5s]; exact hs4s'
  have hs6s' : toS s6 = false := by rw [← hs6s, hs5s']; rfl
  have hn6_expr : toN s6 = ai 0 s1 / 2 + 2 ^ (toL s1 - 2) := by omega
  -- the `a₆⁰` balance
  have hd21 : divpow2r (toN s2) 1 = 2 ^ (toL s1 - 2) := by
    unfold divpow2r
    rw [hs2n]
    norm_num
    omega
  have ha60_expr : ai 1 s1 + 2 ^ (toL s1 - 2) + divpow2r (toN s5) 0 + 1
      = s6.1 + divpow2r (toN s4) 0 + divpow2r (toN s3) 1 := by
    have h1 := hs2a 1
    rw [if_neg (by omega : (1:ℕ) ≠ toL s1 - 1)] at h1
    have h2 := hs3a 1
    rw [hd21] at h2
    have h3 : ai 0 s4 = ai 1 s3 := hs4a 0
    have h4 := hs5a 0
    have h5 := hs6a0
    omega
  -- the `a₆` balance
  have ha6_expr : ∀ i, ai (i + 2) s1 + (if i + 2 = toL s1 - 1 then 1 else 0)
      + divpow2r (2 ^ toL s1 - 1) (i + 2) + divpow2r (toN s5) (i + 1)
      = ai i s6 + divpow2r (toN s4) (i + 1) + divpow2r (toN s3) (i + 2) := by
    intro i
    have h1 := hs2a (i + 2)
    have h2 := hs3a (i + 2)
    rw [hs2n] at h2
    have h3 : ai (i + 1) s4 = ai (i + 2) s3 := hs4a (i + 1)
    have h4 := hs5a (i + 1)
    have h5 := hs6a i
    omega
  -- assemble
  rw [hs4a0] at I45
  exact ⟨s6, toN s3, toN s4, toN s5, toN s6,
    WeaklyEmbanked.intro s2.1 (ai 0 s3) s1 s2 s3 s4 s5 s6 Z12 I23 H34 I45 H56
      hwf1 hs1s hs1n hs1l hs1a0_odd hs1a0_lt hs1a1_lt hwf6 hs6s' (by omega)
      hs4n.symm hs6n.symm hn3_expr hn4_expr hn5_expr hn6_expr ha60_expr ha6_expr⟩

/-- Coq `embanked_precond`. -/
lemma embanked_precond {s1 s6 : S17} {s_1 h_1 s_2 h_2 : ℕ}
    (hweb : WeaklyEmbanked s1 s6 s_1 h_1 s_2 h_2) (hle : h_2 ≤ s6.1) :
    ∃ s7, Embanked s1 s7 s_1 h_1 s_2 h_2 := by
  obtain ⟨n1, n2, s1, s2, s3, s4, s5, s6, Z12, I23, H34, I45, H56, hwf1, hs1s,
    hs1n, hs1l, hs1a0_odd, hs1a0_lt, hs1a1_lt, hwf6, hs6s, hs6l, n34, n56, n3e,
    n4e, n5e, n6e, a60, a6⟩ := hweb
  obtain ⟨s7, I67, hwf7⟩ := Increments_dec_precond1 (toN s6) hwf6 hs6s
    (le_refl _) hle
  have hs7s := Increments_sgn I67
  have hs7n := Increments_n I67
  have hs7l := Increments_len I67
  have hs7a0 := Increments_a0 I67
  have hs7a := Increments_a I67
  rw [hs6s] at hs7n hs7a0 hs7a
  simp only [Bool.false_eq_true, if_false] at hs7n hs7a0 hs7a
  have hn7_0 : toN s7 = 0 := by omega
  have ha70 : ai 1 s1 + 2 ^ (toL s1 - 2) + divpow2r (toN s5) 0 - toN s7 + 1
      = s7.1 + toN s6 + divpow2r (toN s4) 0 + divpow2r (toN s3) 1 := by omega
  have ha7 : ∀ i, ai (i + 2) s1 + (if i + 2 = toL s1 - 1 then 1 else 0)
      + divpow2r (2 ^ toL s1 - 1) (i + 2) + divpow2r (toN s5) (i + 1)
      + divpow2r (toN s6) i
      = ai i s7 + divpow2r (toN s4) (i + 1) + divpow2r (toN s3) (i + 2) := by
    intro i
    have hd7 : divpow2r (toN s7) i = 0 := by
      rw [hn7_0]
      unfold divpow2r
      rw [Nat.zero_add, Nat.div_eq_of_lt]
      have := Nat.two_pow_pos i
      rw [two_pow_succ' i]
      omega
    have h1 := a6 i
    have h2 := hs7a i
    omega
  obtain ⟨s8, Z78, _⟩ := Zero_precond hwf7 (by rw [← hs7s]; exact hs6s) hn7_0
  refine ⟨s7, Embanked.intro (toN s6) s1 s6 s7 s8 (toN s3) (toN s4) (toN s5)
    (toN s6) ?_ I67 Z78 hle ha70 ha7 hwf7 (by rw [← hs7s]; exact hs6s) hn7_0
    (by omega)⟩
  exact WeaklyEmbanked.intro n1 n2 s1 s2 s3 s4 s5 s6 Z12 I23 H34 I45 H56
    hwf1 hs1s hs1n hs1l hs1a0_odd hs1a0_lt hs1a1_lt hwf6 hs6s hs6l n34 n56
    n3e n4e n5e n6e a60 a6

/-! ### `divpow2r` bridges and `ctzS` (Coq lines 3294–3433) -/

lemma divpow2r_mono {n1 n2 : ℕ} (h : n1 ≤ n2) (i : ℕ) :
    divpow2r n1 i ≤ divpow2r n2 i :=
  Nat.div_le_div_right (by omega)

lemma divpow2r_div2 (n i : ℕ) : divpow2r (n / 2) i = divpow2r n (i + 1) := by
  unfold divpow2r
  have h1 : (2:ℕ) ^ (i + 1 + 1) = 2 ^ (i + 1) * 2 := pow_succ 2 (i + 1)
  have h2 : (n + 2 ^ (i + 1)) / 2 = n / 2 + 2 ^ i := by
    have := two_pow_succ' i
    omega
  rw [h1, mul_comm, ← Nat.div_div_eq_div_mul, h2]

lemma divpow2r_div2_add2 (n i : ℕ) :
    divpow2r (n / 2 + 1) i = divpow2r (n + 2) (i + 1) := by
  rw [← divpow2r_div2, show (n + 2) / 2 = n / 2 + 1 by omega]

lemma divpow2r_S (n i : ℕ) :
    divpow2r (n + 1) i
      = divpow2r n i + (if n % 2 ^ (i + 1) = 2 ^ i - 1 then 1 else 0) := by
  by_cases h : n % 2 ^ (i + 1) = 2 ^ i - 1
  · rw [if_pos h, ← divpow2r_inc h]
  · rw [if_neg h, ← divpow2r_eq h]
    omega

/-- Coq `ctzS n`: the number of trailing binary zeros of `n + 1`. -/
def ctzS (n : ℕ) : ℕ :=
  if n % 2 = 1 then ctzS (n / 2) + 1 else 0
decreasing_by omega

/-- Coq `ctzS_spec`. -/
lemma ctzS_spec : ∀ (n i : ℕ), ctzS n = i ↔ n % 2 ^ (i + 1) = 2 ^ i - 1 := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro i
    rcases Nat.mod_two_eq_zero_or_one n with hpar | hpar
    · have hct : ctzS n = 0 := by rw [ctzS]; simp [hpar]
      cases i with
      | zero =>
          rw [hct]
          norm_num
          omega
      | succ i' =>
          constructor
          · intro h
            rw [hct] at h
            omega
          · intro h
            exfalso
            have hdvd : (2:ℕ) ∣ 2 ^ (i' + 1 + 1) := ⟨2 ^ (i' + 1), by rw [pow_succ]; ring⟩
            have hmm := Nat.mod_mod_of_dvd n hdvd
            rw [h] at hmm
            have hsp := two_pow_succ' i'
            have hp' : 0 < 2 ^ i' := Nat.two_pow_pos i'
            omega
    · have hct : ctzS n = ctzS (n / 2) + 1 := by rw [ctzS]; simp [hpar]
      cases i with
      | zero =>
          rw [hct]
          norm_num
          omega
      | succ i' =>
          have ih' := ih (n / 2) (by omega) i'
          have key : n % 2 ^ (i' + 1 + 1) = 2 ^ (i' + 1) - 1
              ↔ (n / 2) % 2 ^ (i' + 1) = 2 ^ i' - 1 := by
            have h2M : (2:ℕ) ^ (i' + 1 + 1) = 2 * 2 ^ (i' + 1) := by
              rw [pow_succ]; ring
            have htq := Nat.div_add_mod (n / 2) (2 ^ (i' + 1))
            have hrlt : (n / 2) % 2 ^ (i' + 1) < 2 ^ (i' + 1) :=
              Nat.mod_lt _ (Nat.two_pow_pos _)
            have hmul : 2 ^ (i' + 1 + 1) * (n / 2 / 2 ^ (i' + 1))
                = 2 * (2 ^ (i' + 1) * (n / 2 / 2 ^ (i' + 1))) := by
              rw [h2M]; ring
            have hnm : n % 2 ^ (i' + 1 + 1) = 2 * ((n / 2) % 2 ^ (i' + 1)) + 1 := by
              have e1 : n = 2 ^ (i' + 1 + 1) * (n / 2 / 2 ^ (i' + 1))
                  + (2 * ((n / 2) % 2 ^ (i' + 1)) + 1) := by omega
              calc n % 2 ^ (i' + 1 + 1)
                  = (2 ^ (i' + 1 + 1) * (n / 2 / 2 ^ (i' + 1))
                    + (2 * ((n / 2) % 2 ^ (i' + 1)) + 1)) % 2 ^ (i' + 1 + 1) := by
                    rw [← e1]
                _ = (2 * ((n / 2) % 2 ^ (i' + 1)) + 1) % 2 ^ (i' + 1 + 1) :=
                    Nat.mul_add_mod _ _ _
                _ = 2 * ((n / 2) % 2 ^ (i' + 1)) + 1 := Nat.mod_eq_of_lt (by omega)
            have hsp := two_pow_succ' i'
            have hp' : 0 < 2 ^ i' := Nat.two_pow_pos i'
            omega
          rw [hct, key]
          constructor
          · intro h
            exact ih'.1 (by omega)
          · intro h
            have := ih'.2 h
            omega

/-! ### Lemma 3.5: how the four counters move under `Add2 i` -/

lemma emb_wemb_s_h {e ne nne : S17} {i s_1 h_1 s_2 h_2 s_1' h_1' s_2' h_2' : ℕ}
    (He : Embanked e ne s_1 h_1 s_2 h_2)
    (Hwe : WeaklyEmbanked ne nne s_1' h_1' s_2' h_2')
    (Hadd : Add2 i e ne) :
    match i with
    | 0 => (s_1, h_1, s_2, h_2) = (s_1' + 2, h_1' + 1, s_2', h_2')
    | 1 => (s_1, h_1, s_2 + 2, h_2 + 1) = (s_1', h_1', s_2', h_2')
    | _ + 2 => (s_1, h_1, s_2, h_2) = (s_1', h_1', s_2', h_2') := by
  obtain ⟨n1, e, s6, ne, s8, s_1, h_1, s_2, h_2, hwemb, I67, Z78, hge, a70, a7,
    hwf7, hs7s, hs7n, hleq⟩ := He
  obtain ⟨m1, m2, e, e2, e3, e4, e5, s6, Z12, I23, H34, I45, H56, hwf1, hs1s,
    hs1n, hs1l, hs1a0_odd, hs1a0_lt, hs1a1_lt, hwf6, hs6s, hs6l, n34, n56, n3e,
    n4e, n5e, n6e, a60, a6⟩ := hwemb
  obtain ⟨k1, k2, ne, f2, f3, f4, f5, nne, Z12', I23', H34', I45', H56', hwf1',
    hs1s', hs1n', hs1l', hs1a0_odd', hs1a0_lt', hs1a1_lt', hwf6', hs6s', hs6l',
    n34', n56', n3e', n4e', n5e', n6e', a60', a6'⟩ := Hwe
  obtain ⟨hadd2⟩ := Hadd
  have h0 := hadd2 0
  have h1 := hadd2 1
  simp only [ai'] at h0 h1
  rw [← hleq] at n3e' n4e' n5e' n6e'
  match i with
  | 0 =>
      norm_num at h0 h1
      simp only [Prod.mk.injEq]
      refine ⟨by omega, by omega, by omega, by omega⟩
  | 1 =>
      norm_num at h0 h1
      simp only [Prod.mk.injEq]
      refine ⟨by omega, by omega, by omega, by omega⟩
  | (j + 2) =>
      rw [if_neg (by omega : ¬(0:ℕ) = j + 2)] at h0
      rw [if_neg (by omega : ¬(1:ℕ) = j + 2)] at h1
      simp only [Prod.mk.injEq]
      refine ⟨by omega, by omega, by omega, by omega⟩

/-! ### Proposition 3.6: each embanked step spawns the next (Coq lines 3451–3663) -/

lemma emb_wemb_Add2_emb {e ne ne' : S17} {i s_1 h_1 s_2 h_2 s_1' h_1' s_2' h_2' : ℕ}
    (He : Embanked e ne s_1 h_1 s_2 h_2)
    (Hwe : WeaklyEmbanked ne ne' s_1' h_1' s_2' h_2')
    (Hadd : Add2 i e ne) :
    ∃ nne, Embanked ne nne s_1' h_1' s_2' h_2' ∧
      match i with
      | 0 => Add2 (ctzS (h_1 - 1)) ne nne
      | 1 => Add2 (ctzS h_2 + 1) ne nne
      | i0 + 2 => Add2 i0 ne nne := by
  have Hsh := emb_wemb_s_h He Hwe Hadd
  obtain ⟨n1, e, s6, ne, s8, s_1, h_1, s_2, h_2, hwemb, I67, Z78, hge, a70, a7,
    hwf7, hs7s, hs7n, hleq⟩ := He
  obtain ⟨m1, m2, e, e2, e3, e4, e5, s6, Z12, I23, H34, I45, H56, hwf1, hs1s,
    hs1n, hs1l, hs1a0_odd, hs1a0_lt, hs1a1_lt, hwf6, hs6s, hs6l, n34, n56, n3e,
    n4e, n5e, n6e, a60, a6⟩ := hwemb
  obtain ⟨k1, k2, ne, f2, f3, f4, f5, ne', Z12', I23', H34', I45', H56', hwf1',
    hs1s', hs1n', hs1l', hs1a0_odd', hs1a0_lt', hs1a1_lt', hwf6', hs6s', hs6l',
    n34', n56', n3e', n4e', n5e', n6e', a60', a6'⟩ := Hwe
  obtain ⟨hadd2⟩ := Hadd
  rw [hleq] at a70 a7
  -- monotonicity facts for nat-subtraction safety
  have E1 : divpow2r (toN f4) 0 ≤ divpow2r (toN f4 + 1) 0 := divpow2r_mono (by omega) 0
  have E2 : divpow2r (toN f3) 1 ≤ divpow2r (toN f3 + 2) 1 := divpow2r_mono (by omega) 1
  have E3 : divpow2r (toN e5) 0 ≤ divpow2r (toN e5 + 2) 0 := divpow2r_mono (by omega) 0
  cases i with
  | zero =>
    have Hsh' := Hsh
    simp only [Prod.mk.injEq] at Hsh'
    obtain ⟨Q1, Q2, Q3, Q4⟩ := Hsh'
    rw [Q1, Q2, Q3, Q4] at a70 a7
    have hadd2_2 := hadd2 2
    rw [if_neg (by omega : ¬(2:ℕ) = 0)] at hadd2_2
    simp only [ai'] at hadd2_2
    obtain ⟨nne, He'⟩ := embanked_precond
      (WeaklyEmbanked.intro k1 k2 ne f2 f3 f4 f5 ne' Z12' I23' H34' I45' H56'
        hwf1' hs1s' hs1n' hs1l' hs1a0_odd' hs1a0_lt' hs1a1_lt' hwf6' hs6s' hs6l'
        n34' n56' n3e' n4e' n5e' n6e' a60' a6') (by omega)
    obtain ⟨w1, ne, ne'2, nne, w8, ww1, ww2, ww3, ww4, hwemb', I67', Z78', hge',
      a70', a7', hwf7', hs7s', hs7n', hleq'⟩ := He'
    refine ⟨nne, ?_, ?_⟩
    · exact Embanked.intro w1 ne ne'2 nne w8 _ _ _ _ hwemb' I67' Z78' hge'
        a70' a7' hwf7' hs7s' hs7n' hleq'
    · have H1 : ∀ j, divpow2r (toN f4 + 1) j = divpow2r (toN f3 + 2) (j + 1) := by
        intro j
        rw [n34', divpow2r_div2_add2]
      have H2 : ∀ j, divpow2r (toN f4) j = divpow2r (toN f3) (j + 1) := by
        intro j
        rw [n34', divpow2r_div2]
      have Ha : ∀ k, ai' k ne + 2 * divpow2r (toN f4 + 1) k
          = ai' k nne + 2 * divpow2r (toN f4) k := by
        intro k
        match k with
        | 0 =>
            simp only [ai']
            have h1 : divpow2r (toN f4 + 1) 0 = divpow2r (toN f3 + 2) 1 := H1 0
            have h2 : divpow2r (toN f4) 0 = divpow2r (toN f3) 1 := H2 0
            omega
        | (j + 1) =>
            simp only [ai']
            have ha7 := a7 j
            have ha7' := a7' j
            have hadj := hadd2 (j + 3)
            rw [if_neg (by omega : ¬(j + 3 : ℕ) = 0)] at hadj
            simp only [ai'] at hadj
            have h1 : divpow2r (toN f4 + 1) (j + 1) = divpow2r (toN f3 + 2) (j + 2) :=
              H1 (j + 1)
            have h2 : divpow2r (toN f4) (j + 1) = divpow2r (toN f3) (j + 2) :=
              H2 (j + 1)
            omega
      refine Add2.intro _ _ _ fun k => ?_
      rw [show toN e4 - 1 = toN f4 by omega]
      by_cases hE : k = ctzS (toN f4)
      · rw [if_pos hE]
        have hcond := (ctzS_spec (toN f4) k).1 hE.symm
        have hinc := divpow2r_inc hcond
        have hHa := Ha k
        omega
      · rw [if_neg hE]
        have hcond : ¬ toN f4 % 2 ^ (k + 1) = 2 ^ k - 1 :=
          fun hc => hE ((ctzS_spec (toN f4) k).2 hc).symm
        have heq := divpow2r_eq hcond
        have hHa := Ha k
        omega
  | succ i =>
    cases i with
    | zero =>
      have Hsh' := Hsh
      simp only [Prod.mk.injEq] at Hsh'
      obtain ⟨Q1, Q2, Q3, Q4⟩ := Hsh'
      rw [Q1, Q2] at a70 a7
      have a60c := a60'
      rw [← Q3] at a60c
      have hadd2_2 := hadd2 2
      rw [if_neg (by omega : ¬(2:ℕ) = 1)] at hadd2_2
      simp only [ai'] at hadd2_2
      have hd20 : divpow2r (toN e5 + 2) 0 = divpow2r (toN e5) 0 + 1 := by
        rw [divpow2r_zero, divpow2r_zero]
        omega
      obtain ⟨nne, He'⟩ := embanked_precond
        (WeaklyEmbanked.intro k1 k2 ne f2 f3 f4 f5 ne' Z12' I23' H34' I45' H56'
          hwf1' hs1s' hs1n' hs1l' hs1a0_odd' hs1a0_lt' hs1a1_lt' hwf6' hs6s' hs6l'
          n34' n56' n3e' n4e' n5e' n6e' a60' a6') (by omega)
      obtain ⟨w1, ne, ne'2, nne, w8, ww1, ww2, ww3, ww4, hwemb', I67', Z78', hge',
        a70', a7', hwf7', hs7s', hs7n', hleq'⟩ := He'
      refine ⟨nne, ?_, ?_⟩
      · exact Embanked.intro w1 ne ne'2 nne w8 _ _ _ _ hwemb' I67' Z78' hge'
          a70' a7' hwf7' hs7s' hs7n' hleq'
      · rw [← Q3, ← Q4] at a70' a7'
        have H1 : ∀ j, divpow2r (toN s6 + 1) j = divpow2r (toN e5 + 2) (j + 1) := by
          intro j
          rw [n56, divpow2r_div2_add2]
        have H2 : ∀ j, divpow2r (toN s6) j = divpow2r (toN e5) (j + 1) := by
          intro j
          rw [n56, divpow2r_div2]
        have Ha : ∀ j, ai j ne + 2 * divpow2r (toN s6 + 1) j
            = ai j nne + 2 * divpow2r (toN s6) j := by
          intro j
          have ha7 := a7 j
          have ha7' := a7' j
          have hadj := hadd2 (j + 3)
          rw [if_neg (by omega : ¬(j + 3 : ℕ) = 1)] at hadj
          simp only [ai'] at hadj
          have h1 : divpow2r (toN s6 + 1) j = divpow2r (toN e5 + 2) (j + 1) := H1 j
          have h2 : divpow2r (toN s6) j = divpow2r (toN e5) (j + 1) := H2 j
          omega
        refine Add2.intro _ _ _ fun k => ?_
        match k with
        | 0 =>
            rw [if_neg (by omega : ¬(0:ℕ) = ctzS (toN s6) + 1)]
            simp only [ai']
            have h1 : divpow2r (toN s6 + 1) 0 = divpow2r (toN e5 + 2) 1 := H1 0
            have h2 : divpow2r (toN s6) 0 = divpow2r (toN e5) 1 := H2 0
            omega
        | (j + 1) =>
            simp only [ai']
            have hHa := Ha j
            by_cases hE : j = ctzS (toN s6)
            · rw [if_pos (by omega : j + 1 = ctzS (toN s6) + 1)]
              have hcond := (ctzS_spec (toN s6) j).1 hE.symm
              have hinc := divpow2r_inc hcond
              omega
            · rw [if_neg (by omega : ¬(j + 1 : ℕ) = ctzS (toN s6) + 1)]
              have hcond : ¬ toN s6 % 2 ^ (j + 1) = 2 ^ j - 1 :=
                fun hc => hE ((ctzS_spec (toN s6) j).2 hc).symm
              have heq := divpow2r_eq hcond
              omega
    | succ i0 =>
      have Hsh' := Hsh
      simp only [Prod.mk.injEq] at Hsh'
      obtain ⟨Q1, Q2, Q3, Q4⟩ := Hsh'
      rw [Q1, Q2, Q3, Q4] at a70 a7
      have hadd2_2 := hadd2 2
      simp only [ai'] at hadd2_2
      obtain ⟨nne, He'⟩ := embanked_precond
        (WeaklyEmbanked.intro k1 k2 ne f2 f3 f4 f5 ne' Z12' I23' H34' I45' H56'
          hwf1' hs1s' hs1n' hs1l' hs1a0_odd' hs1a0_lt' hs1a1_lt' hwf6' hs6s' hs6l'
          n34' n56' n3e' n4e' n5e' n6e' a60' a6') (by omega)
      obtain ⟨w1, ne, ne'2, nne, w8, ww1, ww2, ww3, ww4, hwemb', I67', Z78', hge',
        a70', a7', hwf7', hs7s', hs7n', hleq'⟩ := He'
      refine ⟨nne, ?_, ?_⟩
      · exact Embanked.intro w1 ne ne'2 nne w8 _ _ _ _ hwemb' I67' Z78' hge'
          a70' a7' hwf7' hs7s' hs7n' hleq'
      · refine Add2.intro _ _ _ fun k => ?_
        match k with
        | 0 =>
            simp only [ai']
            by_cases hE : (0 : ℕ) = i0
            · rw [if_pos hE]
              rw [if_pos (by omega : (2 : ℕ) = i0 + 1 + 1)] at hadd2_2
              omega
            · rw [if_neg hE]
              rw [if_neg (by omega : ¬(2 : ℕ) = i0 + 1 + 1)] at hadd2_2
              omega
        | (j + 1) =>
            simp only [ai']
            have ha7 := a7 j
            have ha7' := a7' j
            have hadj := hadd2 (j + 3)
            simp only [ai'] at hadj
            by_cases hE : (j + 1 : ℕ) = i0
            · rw [if_pos hE]
              rw [if_pos (by omega : (j + 3 : ℕ) = i0 + 1 + 1)] at hadj
              omega
            · rw [if_neg hE]
              rw [if_neg (by omega : ¬(j + 3 : ℕ) = i0 + 1 + 1)] at hadj
              omega

/-! ## Level 5: `embanked_batch` (Coq lines 3666–4025) -/

/-- Coq `Add2s`: cumulative effect of a batch — indices of matching parity up
to `i0` are each bumped by two. -/
inductive Add2s : ℕ → S17 → S17 → Prop
  | intro (i0 : ℕ) (s1 s2 : S17)
      (h : ∀ i, ai' i s1 + (if i ≤ i0 ∧ i % 2 = i0 % 2 then 2 else 0) = ai' i s2) :
      Add2s i0 s1 s2

lemma add2s_inv {i0 : ℕ} {s1 s2 : S17} (h : Add2s i0 s1 s2) :
    ∀ i, ai' i s1 + (if i ≤ i0 ∧ i % 2 = i0 % 2 then 2 else 0) = ai' i s2 := by
  cases h with | intro h => exact h

lemma add2_inv {i0 : ℕ} {s1 s2 : S17} (h : Add2 i0 s1 s2) :
    ∀ i, ai' i s1 + (if i = i0 then 2 else 0) = ai' i s2 := by
  cases h with | intro h => exact h

/-- Coq `Add2s_O`. -/
lemma Add2s_O {s1 s2 : S17} (h : Add2 0 s1 s2) : Add2s 0 s1 s2 := by
  refine Add2s.intro _ _ _ fun i => ?_
  have h1 := add2_inv h i
  split_ifs at h1 ⊢ <;> omega

/-- Coq `Add2s_SO`. -/
lemma Add2s_SO {s1 s2 : S17} (h : Add2 1 s1 s2) : Add2s 1 s1 s2 := by
  refine Add2s.intro _ _ _ fun i => ?_
  have h1 := add2_inv h i
  split_ifs at h1 ⊢ <;> omega

/-- Coq `Add2s_SS`. -/
lemma Add2s_SS {i : ℕ} {s1 s2 s3 : S17} (h : Add2 (i + 2) s1 s2)
    (h0 : Add2s i s2 s3) : Add2s (i + 2) s1 s3 := by
  refine Add2s.intro _ _ _ fun k => ?_
  have h1 := add2_inv h k
  have h2 := add2s_inv h0 k
  split_ifs at h1 h2 ⊢ <;> omega

/-- Coq `embanked_batch`: a run of `embanked` steps whose `Add2` indices
descend by two to `0` or `1`. -/
inductive EmbankedBatch : ℕ → S17 → S17 → ℕ → ℕ → Prop
  | zero {e ne : S17} {s_1 h_1 s_2 h_2 : ℕ}
      (He : Embanked e ne s_1 h_1 s_2 h_2) (Ha : Add2 0 e ne) :
      EmbankedBatch 0 e ne h_1 h_2
  | one {e ne : S17} {s_1 h_1 s_2 h_2 : ℕ}
      (He : Embanked e ne s_1 h_1 s_2 h_2) (Ha : Add2 1 e ne) :
      EmbankedBatch 1 e ne h_1 h_2
  | ss {i : ℕ} {e ne n'e : S17} {s_1 h_1 s_2 h_2 : ℕ}
      (He : Embanked e ne s_1 h_1 s_2 h_2) (Ha : Add2 (i + 2) e ne)
      (Heb : EmbankedBatch i ne n'e h_1 h_2) :
      EmbankedBatch (i + 2) e n'e h_1 h_2

/-- Coq `embanked_Add2SS_embanked`: an `Add2 (i+2)`-marked embanked step spawns
an identical-countered embanked step marked `Add2 i`. -/
lemma embanked_Add2SS_embanked {i : ℕ} {e ne : S17} {s_1' h_1' s_2' h_2' : ℕ}
    (He : Embanked e ne s_1' h_1' s_2' h_2') (Ha : Add2 (i + 2) e ne) :
    ∃ nne, Embanked ne nne s_1' h_1' s_2' h_2' ∧ Add2 i ne nne := by
  have Hkeep := He
  obtain ⟨n1, e, s6, ne, s8, s_1', h_1', s_2', h_2', hwemb, I67, Z78, hge, a70,
    a7, hwf7, hs7s, hs7n, hleq⟩ := He
  obtain ⟨m1, m2, e, e2, e3, e4, e5, s6, Z12, I23, H34, I45, H56, hwf1, hs1s,
    hs1n, hs1l, hs1a0_odd, hs1a0_lt, hs1a1_lt, hwf6, hs6s, hs6l, n34, n56, n3e,
    n4e, n5e, n6e, a60, a6⟩ := hwemb
  have h0 := add2_inv Ha 0
  have h1 := add2_inv Ha 1
  simp only [ai'] at h0 h1
  rw [if_neg (by omega : ¬(0:ℕ) = i + 2)] at h0
  rw [if_neg (by omega : ¬(1:ℕ) = i + 2)] at h1
  rw [hleq] at hs1l hs1a0_lt hs1a1_lt
  obtain ⟨ne0, t1, t2, t3, t4, Hwe⟩ := weakly_embanked_precond hwf7 hs7s hs7n
    hs1l (dec_to_0_a0_odd hs7s hs7n) (by omega) (by omega)
  have Hsh := emb_wemb_s_h Hkeep Hwe Ha
  simp only [Prod.mk.injEq] at Hsh
  obtain ⟨Q1, Q2, Q3, Q4⟩ := Hsh
  obtain ⟨nne, He', Ha'⟩ := emb_wemb_Add2_emb Hkeep Hwe Ha
  rw [← Q1, ← Q2, ← Q3, ← Q4] at He'
  exact ⟨nne, He', Ha'⟩

/-- Coq `embanked__embanked_batch`. -/
lemma embanked_embanked_batch : ∀ {i : ℕ} {e ne : S17} {s_1' h_1' s_2' h_2' : ℕ},
    Embanked e ne s_1' h_1' s_2' h_2' → Add2 i e ne →
    ∃ n'e, EmbankedBatch i e n'e h_1' h_2' := by
  intro i
  induction i using Nat.strong_induction_on with
  | _ i ih =>
    intro e ne s_1' h_1' s_2' h_2' He Ha
    match i with
    | 0 => exact ⟨ne, EmbankedBatch.zero He Ha⟩
    | 1 => exact ⟨ne, EmbankedBatch.one He Ha⟩
    | (j + 2) =>
        obtain ⟨nne, He', Ha'⟩ := embanked_Add2SS_embanked He Ha
        obtain ⟨n'e, Heb⟩ := ih j (by omega) He' Ha'
        exact ⟨n'e, EmbankedBatch.ss He Ha Heb⟩

/-- Coq `embanked_batch_last`: the tail of a batch is a batch at `i % 2`. -/
lemma embanked_batch_last {i : ℕ} {e ne : S17} {h_1 h_2 : ℕ}
    (h : EmbankedBatch i e ne h_1 h_2) :
    ∃ e', EmbankedBatch (i % 2) e' ne h_1 h_2 := by
  induction h with
  | zero He Ha => exact ⟨_, EmbankedBatch.zero He Ha⟩
  | one He Ha => exact ⟨_, EmbankedBatch.one He Ha⟩
  | @ss j _ _ _ _ _ _ _ He Ha Heb ih =>
      obtain ⟨e', Heb'⟩ := ih
      exact ⟨e', by rwa [show (j + 2) % 2 = j % 2 by omega]⟩

/-- Coq `embanked_batch_Add2s`. -/
lemma embanked_batch_Add2s {i : ℕ} {e ne : S17} {h_1 h_2 : ℕ}
    (h : EmbankedBatch i e ne h_1 h_2) : Add2s i e ne := by
  induction h with
  | zero He Ha => exact Add2s_O Ha
  | one He Ha => exact Add2s_SO Ha
  | ss He Ha Heb ih => exact Add2s_SS Ha ih

/-- Coq `embanked_batch_precond_01` + `embanked_batch_precond` fused. -/
lemma embanked_batch_precond {i : ℕ} {e ne ne' : S17} {h_1 h_2 s_1' h_1' s_2' h_2' : ℕ}
    (Heb : EmbankedBatch i e ne h_1 h_2)
    (Hwe : WeaklyEmbanked ne ne' s_1' h_1' s_2' h_2') :
    ∃ n'ne, EmbankedBatch
      (match i % 2 with
        | 0 => ctzS (h_1 - 1)
        | _ => ctzS h_2 + 1) ne n'ne h_1' h_2' := by
  obtain ⟨e', Heb'⟩ := embanked_batch_last Heb
  rcases him : i % 2 with _ | m
  · rw [him] at Heb'
    cases Heb' with
    | zero He Ha =>
        obtain ⟨nne, He', Ha'⟩ := emb_wemb_Add2_emb He Hwe Ha
        exact embanked_embanked_batch He' Ha'
  · have hm : i % 2 = 1 := by omega
    rw [hm] at Heb'
    cases Heb' with
    | one He Ha =>
        obtain ⟨nne, He', Ha'⟩ := emb_wemb_Add2_emb He Hwe Ha
        exact embanked_embanked_batch He' Ha'

/-- Coq `embanked_batch_postcond`. -/
lemma embanked_batch_postcond {i : ℕ} {e ne : S17} {h_1 h_2 : ℕ}
    (h : EmbankedBatch i e ne h_1 h_2) :
    WF1 ne ∧ toS ne = false ∧ toN ne = 0 ∧ 3 ≤ toL ne ∧ Odd ne.1 := by
  induction h with
  | zero He Ha =>
      obtain ⟨n1, e, s6, ne, s8, s_1', h_1', s_2', h_2', hwemb, I67, Z78, hge,
        a70, a7, hwf7, hs7s, hs7n, hleq⟩ := He
      refine ⟨hwf7, hs7s, hs7n, ?_, dec_to_0_a0_odd hs7s hs7n⟩
      obtain ⟨m1, m2, _, e2, e3, e4, e5, _, _, _, _, _, _, _, _, _, hs1l,
        _, _, _, _, _, _, _, _, _, _, _, _, _, _⟩ := hwemb
      omega
  | one He Ha =>
      obtain ⟨n1, e, s6, ne, s8, s_1', h_1', s_2', h_2', hwemb, I67, Z78, hge,
        a70, a7, hwf7, hs7s, hs7n, hleq⟩ := He
      refine ⟨hwf7, hs7s, hs7n, ?_, dec_to_0_a0_odd hs7s hs7n⟩
      obtain ⟨m1, m2, _, e2, e3, e4, e5, _, _, _, _, _, _, _, _, _, hs1l,
        _, _, _, _, _, _, _, _, _, _, _, _, _, _⟩ := hwemb
      omega
  | ss He Ha Heb ih => exact ih

/-- Coq `embanked_batch__wemb`. -/
lemma embanked_batch_wemb {i : ℕ} {e ne : S17} {h_1 h_2 : ℕ}
    (Heb : EmbankedBatch i e ne h_1 h_2)
    (Ha0 : ai' 0 ne < 2 ^ toL ne - 1)
    (Ha1 : ai' 1 ne < 2 ^ (toL ne - 1) * 3) :
    ∃ ne0 s_1' h_1' s_2' h_2', WeaklyEmbanked ne ne0 s_1' h_1' s_2' h_2' := by
  obtain ⟨hwf, hs, hn, hl, hodd⟩ := embanked_batch_postcond Heb
  simp only [ai'] at Ha0 Ha1
  exact weakly_embanked_precond hwf hs hn hl hodd Ha0 (by omega)

/-- Coq `embanked_batch_len`. -/
lemma embanked_batch_len {i : ℕ} {e ne : S17} {h_1 h_2 : ℕ}
    (h : EmbankedBatch i e ne h_1 h_2) : toL e = toL ne := by
  induction h with
  | zero He Ha =>
      obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, hleq⟩ := He
      exact hleq
  | one He Ha =>
      obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, hleq⟩ := He
      exact hleq
  | ss He Ha Heb ih =>
      obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, hleq⟩ := He
      rw [hleq]
      exact ih

/-- Coq `embanked_batch_a0_a1`. -/
lemma embanked_batch_a0_a1 {i : ℕ} {e ne : S17} {h_1 h_2 : ℕ}
    (h : EmbankedBatch i e ne h_1 h_2) :
    ai' 0 ne = ai' 0 e + (1 - i % 2) * 2 ∧ ai' 1 ne = ai' 1 e + (i % 2) * 2 := by
  have Ha := embanked_batch_Add2s h
  have h0 := add2s_inv Ha 0
  have h1 := add2s_inv Ha 1
  split_ifs at h0 h1 <;> omega

/-- Coq `embanked_batch_precond'`: a batch with room to spare spawns the next
batch, with the `(h₁, h₂)` bookkeeping resolved by parity. -/
lemma embanked_batch_precond' {i : ℕ} {e ne : S17} {h_1 h_2 : ℕ}
    (Heb : EmbankedBatch i e ne h_1 h_2)
    (Ha0 : ai' 0 ne < 2 ^ toL ne - 1)
    (Ha1 : ai' 1 ne < 2 ^ (toL ne - 1) * 3) :
    ∃ n'ne, match i % 2 with
      | 0 => EmbankedBatch (ctzS (h_1 - 1)) ne n'ne (h_1 - 1) h_2
      | _ => EmbankedBatch (ctzS h_2 + 1) ne n'ne h_1 (h_2 + 1) := by
  obtain ⟨ne0, s_1', h_1', s_2', h_2', Hwe⟩ := embanked_batch_wemb Heb Ha0 Ha1
  obtain ⟨e', Heb'⟩ := embanked_batch_last Heb
  have hpre := embanked_batch_precond Heb Hwe
  rcases him : i % 2 with _ | m
  · rw [him] at Heb' hpre
    cases Heb' with
    | zero He Ha =>
        have Hsh := emb_wemb_s_h He Hwe Ha
        simp only [Prod.mk.injEq] at Hsh
        obtain ⟨Q1, Q2, Q3, Q4⟩ := Hsh
        obtain ⟨n'ne, hb⟩ := hpre
        refine ⟨n'ne, ?_⟩
        have hb' : EmbankedBatch (ctzS (h_1 - 1)) ne n'ne h_1' h_2' := hb
        show EmbankedBatch (ctzS (h_1 - 1)) ne n'ne (h_1 - 1) h_2
        rw [show h_1' = h_1 - 1 by omega, show h_2' = h_2 by omega] at hb'
        exact hb'
  · have hm : i % 2 = 1 := by omega
    rw [hm] at Heb' hpre
    cases Heb' with
    | one He Ha =>
        have Hsh := emb_wemb_s_h He Hwe Ha
        simp only [Prod.mk.injEq] at Hsh
        obtain ⟨Q1, Q2, Q3, Q4⟩ := Hsh
        obtain ⟨n'ne, hb⟩ := hpre
        refine ⟨n'ne, ?_⟩
        have hb' : EmbankedBatch (ctzS h_2 + 1) ne n'ne h_1' h_2' := hb
        show EmbankedBatch (ctzS h_2 + 1) ne n'ne h_1 (h_2 + 1)
        rw [show h_1' = h_1 by omega, show h_2' = h_2 + 1 by omega] at hb'
        exact hb'

/-! ### Power-of-two `divpow2r` values and `ctzS` shifts (Coq lines 4041–4274) -/

lemma divpow2r_pow2 : ∀ (j i : ℕ), j + 1 ≤ i →
    divpow2r (2 ^ i) j = 2 ^ (i - (j + 1))
  | 0, i, h => by
      obtain ⟨i', rfl⟩ : ∃ i', i = i' + 1 := ⟨i - 1, by omega⟩
      rw [divpow2r_zero, show i' + 1 - (0 + 1) = i' by omega]
      have := two_pow_succ' i'
      omega
  | (j + 1), i, h => by
      obtain ⟨i', rfl⟩ : ∃ i', i = i' + 1 := ⟨i - 1, by omega⟩
      have ih := divpow2r_pow2 j i' (by omega)
      have hd : (2:ℕ) ^ (i' + 1) / 2 = 2 ^ i' := by
        have := two_pow_succ' i'
        omega
      rw [← divpow2r_div2, hd, ih, show i' - (j + 1) = i' + 1 - (j + 1 + 1) by omega]

lemma divpow2r_pow2sub1 : ∀ (j i : ℕ), j + 1 ≤ i →
    divpow2r (2 ^ i - 1) j = 2 ^ (i - (j + 1))
  | 0, i, h => by
      obtain ⟨i', rfl⟩ : ∃ i', i = i' + 1 := ⟨i - 1, by omega⟩
      rw [divpow2r_zero, show i' + 1 - (0 + 1) = i' by omega]
      have := two_pow_succ' i'
      have := Nat.two_pow_pos i'
      omega
  | (j + 1), i, h => by
      obtain ⟨i', rfl⟩ : ∃ i', i = i' + 1 := ⟨i - 1, by omega⟩
      have ih := divpow2r_pow2sub1 j i' (by omega)
      have hd : ((2:ℕ) ^ (i' + 1) - 1) / 2 = 2 ^ i' - 1 := by
        have := two_pow_succ' i'
        have := Nat.two_pow_pos i'
        omega
      rw [← divpow2r_div2, hd, ih, show i' - (j + 1) = i' + 1 - (j + 1 + 1) by omega]

lemma divpow2r_small {n i : ℕ} (h : n < 2 ^ i) : divpow2r n i = 0 := by
  unfold divpow2r
  have := two_pow_succ' i
  rw [Nat.div_eq_of_lt (by omega)]

lemma divpow2r_pow2_small {j i : ℕ} (h : j < i) : divpow2r (2 ^ j) i = 0 :=
  divpow2r_small (Nat.pow_lt_pow_right (by omega) h)

lemma divpow2r_pow2_1 (i : ℕ) : divpow2r (2 ^ i) i = 1 := by
  unfold divpow2r
  rw [pow2_add, Nat.div_self (Nat.two_pow_pos _)]

lemma divpow2r_pow2sub1_small {j i : ℕ} (h : j ≤ i) : divpow2r (2 ^ j - 1) i = 0 := by
  apply divpow2r_small
  have := Nat.pow_le_pow_right (by omega : 1 ≤ 2) h
  have := Nat.two_pow_pos j
  omega

/-- Coq `ctz_upper_bound`. -/
lemma ctz_upper_bound {i m : ℕ} (h : m < 2 ^ i - 1) : ctzS m < i := by
  have hspec := (ctzS_spec m (ctzS m)).1 rfl
  have hle : m % 2 ^ (ctzS m + 1) ≤ m := Nat.mod_le _ _
  by_contra hcon
  have hpow := Nat.pow_le_pow_right (by omega : 1 ≤ 2) (by omega : i ≤ ctzS m)
  have := Nat.two_pow_pos i
  omega

/-- Coq `ctzS_add`: adding `2^i` above the active bits preserves `ctzS`. -/
lemma ctzS_add {i m : ℕ} (h : m < 2 ^ i - 1) : ctzS (2 ^ i + m) = ctzS m := by
  have hub := ctz_upper_bound h
  have hspec := (ctzS_spec m (ctzS m)).1 rfl
  apply (ctzS_spec _ _).2
  have hsplit : (2:ℕ) ^ i = 2 ^ (ctzS m + 1) * 2 ^ (i - (ctzS m + 1)) := by
    rw [← pow_add]
    congr 1
    omega
  calc (2 ^ i + m) % 2 ^ (ctzS m + 1)
      = (2 ^ (ctzS m + 1) * 2 ^ (i - (ctzS m + 1)) + m) % 2 ^ (ctzS m + 1) := by
        rw [← hsplit]
    _ = m % 2 ^ (ctzS m + 1) := Nat.mul_add_mod _ _ _
    _ = 2 ^ (ctzS m) - 1 := hspec

/-- Coq `ctzS_sub`: the mirror position keeps `ctzS`. -/
lemma ctzS_sub {i m : ℕ} (_hi : 0 < i) (h : m < 2 ^ i - 1) :
    ctzS (2 ^ i - m - 2) = ctzS m := by
  have hub := ctz_upper_bound h
  have hspec := (ctzS_spec m (ctzS m)).1 rfl
  set v1 := ctzS m with hv1
  set M := (2:ℕ) ^ (v1 + 1) with hM
  have hMpos : 0 < M := Nat.two_pow_pos _
  have hMsplit : M = 2 ^ v1 + 2 ^ v1 := two_pow_succ' v1
  have hv1pos : 0 < 2 ^ v1 := Nat.two_pow_pos v1
  have hipos : 0 < 2 ^ i := Nat.two_pow_pos i
  apply (ctzS_spec _ _).2
  set v2 := (2 ^ i - m - 2) % M with hv2
  have hv2lt : v2 < M := Nat.mod_lt _ hMpos
  have hMdvd : M ∣ 2 ^ i := pow_dvd_pow 2 (by omega)
  have h2i : (2:ℕ) ^ i % M = 0 := by
    obtain ⟨c, hc⟩ := hMdvd
    rw [hc, Nat.mul_mod_right]
  have e0 : 2 ^ i - m - 2 + (m + 2) = 2 ^ i := by omega
  have hsum : (v2 + (m + 2)) % M = 0 := by
    rw [hv2, Nat.mod_add_mod, e0, h2i]
  have hm2 : (m + 2) % M = (2 ^ v1 + 1) % M := by
    rw [← Nat.mod_add_mod, hspec, show 2 ^ v1 - 1 + 2 = 2 ^ v1 + 1 by omega]
  have key : (v2 + (2 ^ v1 + 1)) % M = 0 := by
    rw [Nat.add_mod v2 (2 ^ v1 + 1), ← hm2, ← Nat.add_mod]
    exact hsum
  rcases Nat.lt_trichotomy v2 (2 ^ v1 - 1) with hc | hc | hc
  · exfalso
    rw [Nat.mod_eq_of_lt (by omega)] at key
    omega
  · exact hc
  · exfalso
    have e : v2 + (2 ^ v1 + 1) = (v2 - 2 ^ v1 + 1) + M := by omega
    rw [e, Nat.add_mod_right, Nat.mod_eq_of_lt (by omega)] at key
    omega

/-! ### Field accessors (avoid fragile positional destructuring) -/

lemma weaklyEmbanked_fields {s1 s6 : S17} {s_1 h_1 s_2 h_2 : ℕ}
    (h : WeaklyEmbanked s1 s6 s_1 h_1 s_2 h_2) :
    WF1 s1 ∧ toS s1 = false ∧ toN s1 = 0 ∧ 3 ≤ toL s1 ∧ Odd s1.1 ∧
    s1.1 < 2 ^ toL s1 - 1 ∧ ai 0 s1 < 3 * 2 ^ (toL s1 - 1) ∧
    WF1 s6 ∧ toS s6 = false ∧ toL s6 = toL s1 ∧
    h_1 = s_1 / 2 ∧ h_2 = s_2 / 2 ∧
    s_1 + s1.1 = 2 ^ toL s1 ∧ h_1 + s1.1 / 2 + 1 = 2 ^ (toL s1 - 1) ∧
    s_2 = ai 0 s1 + 2 ^ (toL s1 - 1) ∧ h_2 = ai 0 s1 / 2 + 2 ^ (toL s1 - 2) ∧
    (ai 1 s1 + 2 ^ (toL s1 - 2) + divpow2r s_2 0 + 1
      = s6.1 + divpow2r h_1 0 + divpow2r s_1 1) ∧
    (∀ i, ai (i + 2) s1 + (if i + 2 = toL s1 - 1 then 1 else 0)
        + divpow2r (2 ^ toL s1 - 1) (i + 2) + divpow2r s_2 (i + 1)
      = ai i s6 + divpow2r h_1 (i + 1) + divpow2r s_1 (i + 2)) := by
  obtain ⟨n1, n2, s1, s2, s3, s4, s5, s6, Z12, I23, H34, I45, H56, hwf1, hs1s,
    hs1n, hs1l, hs1a0_odd, hs1a0_lt, hs1a1_lt, hwf6, hs6s, hs6l, n34, n56, n3e,
    n4e, n5e, n6e, a60, a6⟩ := h
  exact ⟨hwf1, hs1s, hs1n, hs1l, hs1a0_odd, hs1a0_lt, hs1a1_lt, hwf6, hs6s,
    hs6l, n34, n56, n3e, n4e, n5e, n6e, a60, a6⟩

lemma embanked_fields {s1 s7 : S17} {s_1 h_1 s_2 h_2 : ℕ}
    (h : Embanked s1 s7 s_1 h_1 s_2 h_2) :
    (ai 1 s1 + 2 ^ (toL s1 - 2) + divpow2r s_2 0 - toN s7 + 1
      = s7.1 + h_2 + divpow2r h_1 0 + divpow2r s_1 1) ∧
    (∀ i, ai (i + 2) s1 + (if i + 2 = toL s1 - 1 then 1 else 0)
        + divpow2r (2 ^ toL s1 - 1) (i + 2) + divpow2r s_2 (i + 1) + divpow2r h_2 i
      = ai i s7 + divpow2r h_1 (i + 1) + divpow2r s_1 (i + 2)) ∧
    WF1 s7 ∧ toS s7 = false ∧ toN s7 = 0 ∧ toL s1 = toL s7 := by
  obtain ⟨n1, s1, s6, s7, s8, s_1, h_1, s_2, h_2, hwemb, I67, Z78, hge, a70, a7,
    hwf7, hs7s, hs7n, hleq⟩ := h
  exact ⟨a70, a7, hwf7, hs7s, hs7n, hleq⟩

/-- Coq `le_ctzS_sum`: how one increment moves the scaled quotient. -/
lemma le_ctzS_sum (i m : ℕ) :
    2 * (m / 2 ^ i) + (if i ≤ ctzS m then 2 else 0) = 2 * ((m + 1) / 2 ^ i) := by
  have hspec := (ctzS_spec m (ctzS m)).1 rfl
  have hpi : 0 < 2 ^ i := Nat.two_pow_pos i
  by_cases hE : i ≤ ctzS m
  · rw [if_pos hE]
    have hdvd : (2:ℕ) ^ i ∣ 2 ^ (ctzS m + 1) := pow_dvd_pow 2 (by omega)
    have h1 : m % 2 ^ i = (m % 2 ^ (ctzS m + 1)) % 2 ^ i :=
      (Nat.mod_mod_of_dvd m hdvd).symm
    rw [hspec] at h1
    have hsplit : (2:ℕ) ^ ctzS m = 2 ^ i * 2 ^ (ctzS m - i) := by
      rw [← pow_add]
      congr 1
      omega
    have hpv : 0 < 2 ^ (ctzS m - i) := Nat.two_pow_pos _
    have hmulsub : (2:ℕ) ^ i * (2 ^ (ctzS m - i) - 1)
        = 2 ^ i * 2 ^ (ctzS m - i) - 2 ^ i := by
      rw [Nat.mul_sub, Nat.mul_one]
    have hAK : (2:ℕ) ^ i ≤ 2 ^ i * 2 ^ (ctzS m - i) :=
      Nat.le_mul_of_pos_right _ hpv
    have h2 : ((2:ℕ) ^ ctzS m - 1) % 2 ^ i = 2 ^ i - 1 := by
      rw [show (2:ℕ) ^ ctzS m - 1 = 2 ^ i * (2 ^ (ctzS m - i) - 1) + (2 ^ i - 1) by
          omega,
        Nat.mul_add_mod, Nat.mod_eq_of_lt (by omega)]
    have hmod : m % 2 ^ i = 2 ^ i - 1 := h1.trans h2
    have hq := Nat.div_add_mod m (2 ^ i)
    have hT : (2:ℕ) ^ i * (m / 2 ^ i + 1) = 2 ^ i * (m / 2 ^ i) + 2 ^ i := by ring
    have hstep : (m + 1) / 2 ^ i = m / 2 ^ i + 1 := by
      rw [show m + 1 = 2 ^ i * (m / 2 ^ i + 1) by omega,
        Nat.mul_div_cancel_left _ hpi]
    omega
  · rw [if_neg hE]
    have hdvd : (2:ℕ) ^ (ctzS m + 1) ∣ 2 ^ i := pow_dvd_pow 2 (by omega)
    have hq := Nat.div_add_mod m (2 ^ i)
    have hrlt : m % 2 ^ i < 2 ^ i := Nat.mod_lt _ hpi
    have hrm : (m % 2 ^ i) % 2 ^ (ctzS m + 1) = 2 ^ ctzS m - 1 := by
      rw [Nat.mod_mod_of_dvd m hdvd, hspec]
    have hMs : (2:ℕ) ^ (ctzS m + 1) = 2 ^ ctzS m + 2 ^ ctzS m := two_pow_succ' _
    have hvp : 0 < 2 ^ ctzS m := Nat.two_pow_pos _
    have hrne : m % 2 ^ i ≠ 2 ^ i - 1 := by
      intro hcon
      rw [hcon] at hrm
      have hsplit : (2:ℕ) ^ i = 2 ^ (ctzS m + 1) * 2 ^ (i - (ctzS m + 1)) := by
        rw [← pow_add]
        congr 1
        omega
      have hkp : 0 < 2 ^ (i - (ctzS m + 1)) := Nat.two_pow_pos _
      have hmulsub : (2:ℕ) ^ (ctzS m + 1) * (2 ^ (i - (ctzS m + 1)) - 1)
          = 2 ^ (ctzS m + 1) * 2 ^ (i - (ctzS m + 1)) - 2 ^ (ctzS m + 1) := by
        rw [Nat.mul_sub, Nat.mul_one]
      have hAK2 : (2:ℕ) ^ (ctzS m + 1) ≤ 2 ^ (ctzS m + 1) * 2 ^ (i - (ctzS m + 1)) :=
        Nat.le_mul_of_pos_right _ hkp
      have hR : ((2:ℕ) ^ i - 1) % 2 ^ (ctzS m + 1) = 2 ^ (ctzS m + 1) - 1 := by
        rw [show (2:ℕ) ^ i - 1
            = 2 ^ (ctzS m + 1) * (2 ^ (i - (ctzS m + 1)) - 1) + (2 ^ (ctzS m + 1) - 1) by
            omega,
          Nat.mul_add_mod, Nat.mod_eq_of_lt (by omega)]
      rw [hR] at hrm
      omega
    have hstep : (m + 1) / 2 ^ i = m / 2 ^ i := by
      rw [show m + 1 = 2 ^ i * (m / 2 ^ i) + (m % 2 ^ i + 1) by omega,
        Nat.mul_add_div hpi,
        Nat.div_eq_of_lt (show m % 2 ^ i + 1 < 2 ^ i by omega)]
      omega
    omega

end Deciders.Skelet.Skelet17
