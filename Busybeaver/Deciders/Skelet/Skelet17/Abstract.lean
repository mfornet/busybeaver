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
  · simp [Nat.not_even_iff_odd.2 h, Nat.even_add_one, Nat.not_odd_iff_even]

lemma decide_even_succ_eq_oddb (n : ℕ) : decide (Even (n + 1)) = oddb n := by
  rcases Nat.even_or_odd n with h | h
  · simp [Nat.even_add_one, Nat.not_even_iff_odd, h, Nat.not_odd_iff_even,
      oddb_eq_false_iff.2 h]
  · simp [Nat.even_add_one, Nat.not_even_iff_odd.2 h, oddb_eq_true_iff.2 h,
      Nat.even_add_one, h]

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

lemma Halve_sgn {s1 s2 : S17} (h : Halve s1 s2) : !toS s1 = toS s2 := by
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
    Nat.even_add_one, hx, Nat.not_even_iff_odd]

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
        simp [Nat.even_add_one, Nat.not_even_iff_odd, hx]
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
        simp only [Bool.not_true, if_false]
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
        simp [Nat.even_add_one, Nat.not_even_iff_odd, hx]
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
  cases xor (oddb x) ((listToBinary xs).headD false) <;> simp <;> omega

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

end Deciders.Skelet.Skelet17
