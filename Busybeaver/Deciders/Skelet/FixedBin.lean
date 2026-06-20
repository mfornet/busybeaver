import Busybeaver.Basic

/-!
# Fixed-width binary words

A Lean port of `Coq-BB5/BusyCoq/FixedBin.v` (sligocki's Skelet analyses).  These
fixed-width binary words and their carry-propagating increment relation are the
shared arithmetic foundation of the four BB(5) "binary counter" sporadic
holdouts — Skelet #26/#33/#34/#35 (`sporadicMachine9`/`10`/`11`/`12`).  The
module is pure combinatorics: no Turing machine, no tape.

Coq uses `bin : nat → Type` with a `positive`/`N` width arithmetic; here the
counts are plain `ℕ` and `pow2 k` is just `2 ^ k`.
-/

namespace Deciders.Skelet.FixedBin

/-- Fixed-width binary words of width `k` (Coq `bin`), most-significant digit
outermost.  `b0`/`b1` prepend a low/high bit. -/
inductive Bin : ℕ → Type where
  | bb : Bin 0
  | b0 {k : ℕ} : Bin k → Bin (k + 1)
  | b1 {k : ℕ} : Bin k → Bin (k + 1)

/-- One increment with carry (Coq `-S->`): `b0 n ↦ b1 n`, and `b1 n ↦ b0 n'`
when the carry propagates `n ↦ n'`. -/
inductive Succ : ∀ {k : ℕ}, Bin k → Bin k → Prop where
  | b0 {k : ℕ} (n : Bin k) : Succ (.b0 n) (.b1 n)
  | b1 {k : ℕ} {n n' : Bin k} : Succ n n' → Succ (.b1 n) (.b0 n')

/-- Iterated increment: `Plus u n n'` means `n` reaches `n'` after `u`
increments (Coq `bin_plus`). -/
inductive Plus : ∀ {k : ℕ}, ℕ → Bin k → Bin k → Prop where
  | zero {k : ℕ} (n : Bin k) : Plus 0 n n
  | succ {k : ℕ} {u : ℕ} {n n' n'' : Bin k} :
      Succ n n' → Plus u n' n'' → Plus (u + 1) n n''

/-- `Plus` extended by a final increment (Coq `plus_S'`). -/
theorem plus_S' {k u} {n n' n'' : Bin k} (h : Plus u n n') (hs : Succ n' n'') :
    Plus (u + 1) n n'' := by
  induction h with
  | zero n => exact Plus.succ hs (Plus.zero _)
  | succ hsx _ ih => exact Plus.succ hsx (ih hs)

/-- A `b0`-prefixed word increments at twice the rate (Coq `bin_plus_b0`). -/
theorem plus_b0 {k u} {n n' : Bin k} (h : Plus u n n') :
    Plus (2 * u) (.b0 n) (.b0 n') := by
  induction h with
  | zero n => simpa using Plus.zero (Bin.b0 n)
  | succ hs _ ih =>
      -- `2 * (u + 1)` is defeq to `2 * u + 1 + 1`, so this typechecks directly.
      exact Plus.succ (Succ.b0 _) (Plus.succ (Succ.b1 hs) ih)

/-- The all-zeros word of width `k` (Coq `bin_min`). -/
def binMin : (k : ℕ) → Bin k
  | 0 => .bb
  | k + 1 => .b0 (binMin k)

/-- The all-ones word of width `k` (Coq `bin_max`). -/
def binMax : (k : ℕ) → Bin k
  | 0 => .bb
  | k + 1 => .b1 (binMax k)

/-- `2^k - 1` increments carry `bin_min` to `bin_max` (Coq `inc_to_max`): the
counter saturates after exactly `2^k - 1` steps. -/
theorem inc_to_max : ∀ k, Plus (2 ^ k - 1) (binMin k) (binMax k)
  | 0 => by simpa [binMin, binMax] using Plus.zero Bin.bb
  | k + 1 => by
      have ih := inc_to_max k
      have hb0 := plus_b0 ih
      have hstep : Plus (2 * (2 ^ k - 1) + 1) (binMin (k + 1)) (binMax (k + 1)) := by
        simpa [binMin, binMax] using plus_S' hb0 (Succ.b0 (binMax k))
      have hpos : 0 < 2 ^ k := Nat.two_pow_pos k
      have hpow : 2 ^ (k + 1) = 2 ^ k * 2 := pow_succ 2 k
      have heq : 2 ^ (k + 1) - 1 = 2 * (2 ^ k - 1) + 1 := by omega
      rw [heq]
      exact hstep

end Deciders.Skelet.FixedBin
