import Mathlib.Data.Num.Lemmas

/-!
# Shift-overflow arithmetic

A Lean port of `Coq-BB5/BusyCoq/ShiftOverflow.v` (sligocki's Skelet analyses):
the `b` function ("distance to the next power of two", shifted by one) together
with the `has0`/`all1` bit predicates and their arithmetic.  This is the second
shared layer (after `FixedBin`) of the BB(5) binary-counter holdouts
SM9–12 (Skelet #26/#33/#34/#35).

Coq's `positive` counter value is mirrored by Mathlib's `PosNum`
(`one`/`bit0`/`bit1` ↔ `xH`/`xO`/`xI`); Coq's `N`-valued results and the
`het_add` operation `_ :+ _` become plain `ℕ`.  Arithmetic lemmas are proved by
pushing through the `PosNum → ℕ` coercion (`PosNum.cast_*`) and `omega`.
-/

namespace Deciders.Skelet.ShiftOverflow

open PosNum

/-- Distance (minus one) to the next power of two (Coq `b`). -/
def b : PosNum → ℕ
  | .one => 0
  | .bit0 n => 2 * b n + 1
  | .bit1 n => 2 * b n

/-- `n` has a `0` bit (Coq `has0`). -/
inductive Has0 : PosNum → Prop where
  | bit0 (n : PosNum) : Has0 (.bit0 n)
  | bit1 {n : PosNum} : Has0 n → Has0 (.bit1 n)

/-- `n` is all ones (Coq `all1`). -/
inductive All1 : PosNum → Prop where
  | one : All1 .one
  | bit1 {n : PosNum} : All1 n → All1 (.bit1 n)

/-- `b n = 0` exactly for all-ones words (Coq `b0_all1`). -/
theorem b0_all1 : ∀ {n : PosNum}, b n = 0 → All1 n
  | .one, _ => All1.one
  | .bit0 _, h => by simp only [b] at h; omega
  | .bit1 n, h => All1.bit1 (b0_all1 (by simp only [b] at h; omega))

/-- `b n > 0` implies `n` has a `0` bit (Coq `bgt0_has0`). -/
theorem bgt0_has0 : ∀ {n : PosNum}, 0 < b n → Has0 n
  | .one, h => by simp only [b] at h; omega
  | .bit0 n, _ => Has0.bit0 n
  | .bit1 n, h => Has0.bit1 (bgt0_has0 (by simp only [b] at h; omega))

/-- Incrementing decreases the distance by one (Coq `b_succ`). -/
theorem b_succ : ∀ {n : PosNum}, 0 < b n → b n.succ = b n - 1
  | .one, h => by simp only [b] at h; omega
  | .bit0 n, _ => by show b (PosNum.bit1 n) = _; simp only [b]; omega
  | .bit1 n, h => by
      have hn : 0 < b n := by simp only [b] at h; omega
      show b (PosNum.bit0 n.succ) = _
      simp only [b, b_succ hn]; omega

/-- Add a `ℕ` to a `PosNum` (Coq `het_add`, `_ :+ _`): iterate `succ`. -/
def addN (u : ℕ) (n : PosNum) : PosNum := PosNum.succ^[u] n

@[simp] theorem addN_zero (n : PosNum) : addN 0 n = n := rfl

theorem addN_succ (u : ℕ) (n : PosNum) : addN (u + 1) n = (addN u n).succ :=
  Function.iterate_succ_apply' _ _ _

theorem addN_cast (u : ℕ) (n : PosNum) : ((addN u n : PosNum) : ℕ) = u + (n : ℕ) := by
  induction u with
  | zero => simp
  | succ u ih => rw [addN_succ, PosNum.cast_succ, ih]; omega

/-- Adding `u ≤ b n` shifts the distance down by `u` (Coq `b_add`). -/
theorem b_add : ∀ (u : ℕ) {n : PosNum}, u ≤ b n → b (addN u n) = b n - u
  | 0, n, _ => by simp
  | u + 1, n, h => by
      have hu : u ≤ b n := by omega
      have ih := b_add u hu
      have hpos : 0 < b (addN u n) := by omega
      rw [addN_succ, b_succ hpos, ih]; omega

/-- Saturating at the next power of two (Coq `b_add_self`). -/
theorem b_add_self (n : PosNum) : b (addN (b n) n) = 0 := by
  have := b_add (b n) (le_refl (b n)); simpa using this

/-- From a saturated word, incrementing recovers the value (Coq `all1` half of
`b0_succ`). -/
theorem all1_b_succ : ∀ {n : PosNum}, All1 n → b n.succ = (n : ℕ)
  | _, .one => by decide
  | _, .bit1 (n := m) hm => by
      show b (PosNum.bit0 m.succ) = ((PosNum.bit1 m : PosNum) : ℕ)
      simp only [b, PosNum.cast_bit1, all1_b_succ hm]; omega

/-- `b n = 0 → b (succ n) = n` (Coq `b0_succ`). -/
theorem b0_succ {n : PosNum} (h : b n = 0) : b n.succ = (n : ℕ) :=
  all1_b_succ (b0_all1 h)

/-- Powers of two as `PosNum` (Coq `pow2'`). -/
def pow2' : ℕ → PosNum
  | 0 => .one
  | k + 1 => (pow2' k).bit0

@[simp] theorem pow2'_cast : ∀ k, ((pow2' k : PosNum) : ℕ) = 2 ^ k
  | 0 => by decide
  | k + 1 => by show ((PosNum.bit0 (pow2' k) : PosNum) : ℕ) = _
                simp only [PosNum.cast_bit0, pow2'_cast k]; rw [pow_succ]; omega

/-- The successor of an all-ones word is a power of two (Coq `all1_succ_pow2`). -/
theorem all1_succ_pow2 : ∀ {n : PosNum}, All1 n → ∃ k, n.succ = pow2' k
  | _, .one => ⟨1, rfl⟩
  | _, .bit1 (n := m) hm => by
      obtain ⟨k, hk⟩ := all1_succ_pow2 hm
      exact ⟨k + 1, by show PosNum.bit0 m.succ = pow2' (k + 1); rw [hk]; rfl⟩

/-- Saturating then incrementing lands on a power of two (Coq `b_add_pow2`). -/
theorem b_add_pow2 (n : PosNum) : ∃ k, (addN (b n) n).succ = pow2' k :=
  all1_succ_pow2 (b0_all1 (b_add_self n))

/-- `b` of a power of two (Coq `b_pow2`). -/
theorem b_pow2 : ∀ k, b (pow2' k) = 2 ^ k - 1
  | 0 => rfl
  | k + 1 => by
      show b (PosNum.bit0 (pow2' k)) = _
      have hpos : 0 < 2 ^ k := Nat.two_pow_pos k
      have hp : 2 ^ (k + 1) = 2 ^ k * 2 := pow_succ 2 k
      simp only [b, b_pow2 k]; omega

/-- Append two `0` bits, `k` times (Coq `pow4`). -/
def pow4 : ℕ → PosNum → PosNum
  | 0, n => n
  | k + 1, n => pow4 k n.bit0.bit0

theorem pow4_shift : ∀ k (n : PosNum), pow4 k n.bit0.bit0 = (pow4 k n).bit0.bit0
  | 0, _ => rfl
  | k + 1, n => by simp only [pow4]; rw [pow4_shift k]

/-- `b` of a `pow4`-padded word (Coq `b_pow4`). -/
theorem b_pow4 : ∀ k (n : PosNum), b (pow4 k n) = 2 ^ (2 * k) * (b n + 1) - 1
  | 0, n => by simp [pow4]
  | k + 1, n => by
      show b (pow4 k n.bit0.bit0) = 2 ^ (2 * (k + 1)) * (b n + 1) - 1
      rw [pow4_shift]
      simp only [b]
      rw [b_pow4 k]
      have hpos : 0 < 2 ^ (2 * k) := Nat.two_pow_pos (2 * k)
      have hb : 0 < b n + 1 := by omega
      have hYpos : 0 < 2 ^ (2 * k) * (b n + 1) := Nat.mul_pos hpos hb
      have hp : 2 ^ (2 * (k + 1)) = 2 ^ (2 * k) * 4 := by
        rw [show 2 * (k + 1) = 2 * k + 2 by omega, pow_add]; rfl
      have hY : 2 ^ (2 * (k + 1)) * (b n + 1) = 4 * (2 ^ (2 * k) * (b n + 1)) := by
        rw [hp, Nat.mul_comm (2 ^ (2 * k)) 4, Nat.mul_assoc]
      rw [hY]
      omega

end Deciders.Skelet.ShiftOverflow
