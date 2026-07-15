import Busybeaver.Deciders.Skelet.Skelet17.Tape
import Busybeaver.Deciders.Skelet.Skelet17.Abstract

/-!
# Skelet #17 — assembly

Bridges the abstract counter layer (`Abstract.lean`) to the tape layer
(`Tape.lean`) via `toConfig` (Coq `toConfig`), and will ultimately assemble the
non-halting proof for `sporadicMachine8`.
-/

namespace Deciders.Skelet.Skelet17

open Turing
open TM.Table

/-- Coq `toConfig`: the abstract state `(x+1, xs)` denotes the tape
`lower (x :: xs)` (the head exponent is one less than `a₀`). -/
inductive toConfig : S17 → Config 4 1 → Prop
  | intro (x : ℕ) (xs : List ℕ) : toConfig (x + 1, xs) (lower (x :: xs))

/-! ### Inversion helpers (Coq `inverts`) -/

lemma toConfig_inv {s : S17} {c : Config 4 1} (h : toConfig s c) :
    ∃ x xs, s = (x + 1, xs) ∧ c = lower (x :: xs) := by
  cases h with | intro x xs => exact ⟨x, xs, rfl, rfl⟩




/-- Coq `Increment_toConfig`. -/
lemma Increment_toConfig {s1 s2 s3 : S17} {c1 c3 : Config 4 1}
    (h12 : Increment s1 s2) (h23 : TryHalve s2 s3)
    (t1 : toConfig s1 c1) (t3 : toConfig s3 c3) : c1 -[M]->* c3 := by
  obtain ⟨p, ps, hp, hc1⟩ := toConfig_inv t1
  obtain ⟨q, qs, hq, hc3⟩ := toConfig_inv t3
  subst hc1 hc3
  rcases increment_inv h12 with
    ⟨x, xs, y, z, zs, hx, hnz, hev, hy, rfl, rfl⟩ | ⟨x, y, xs, hx, rfl, rfl⟩
  case _ =>
      obtain ⟨hpx, hpl⟩ := Prod.mk.injEq _ _ _ _ ▸ hp
      obtain rfl : x = p := by omega
      subst hpl
      rcases tryHalve_inv h23 with ⟨h0, a, as, hlist, hs3⟩ | ⟨h0, hs3⟩
      · -- `x = 0`: the head counter empties and the list halves.
        obtain rfl : x = 0 := h0
        rw [hq] at hs3
        obtain ⟨rfl, rfl⟩ : a = q ∧ as = qs := by
          have := (Prod.mk.injEq _ _ _ _ ▸ hs3.symm)
          exact ⟨by omega, this.2⟩
        have h := increment_O (xs := xs) (y := y) (z := z) (zs := zs) hnz hev hy
        rw [show xs ++ y :: (z + 1) :: zs = a :: as from hlist] at h
        exact h
      · rw [hq] at hs3
        obtain ⟨hx1, hl1⟩ := Prod.mk.injEq _ _ _ _ ▸ hs3
        obtain rfl : x = q + 1 := by omega
        subst hl1
        exact increment_S_even (x := q) (xs := xs) (y := y) (z := z) (zs := zs)
          hnz hev (by simpa using hx) hy
  case _ =>
      obtain ⟨hpx, hpl⟩ := Prod.mk.injEq _ _ _ _ ▸ hp
      obtain rfl : x = p := by omega
      subst hpl
      rcases tryHalve_inv h23 with ⟨h0, a, as, hlist, hs3⟩ | ⟨h0, hs3⟩
      · obtain rfl : x = 0 := h0
        exact absurd hx (by simp [Nat.odd_iff])
      · rw [hq] at hs3
        obtain ⟨hx1, hl1⟩ := Prod.mk.injEq _ _ _ _ ▸ hs3
        obtain rfl : x = q + 1 := by omega
        subst hl1
        exact increment_S_odd (by simpa using hx)


/-- Coq `Zero_toConfig`. -/
lemma Zero_toConfig {s1 s2 s3 : S17} {c1 c3 : Config 4 1}
    (h12 : Zero s1 s2) (h23 : TryHalve s2 s3)
    (t1 : toConfig s1 c1) (t3 : toConfig s3 c3) : c1 -[M]->* c3 := by
  obtain ⟨p, ps, hp, hc1⟩ := toConfig_inv t1
  obtain ⟨q, qs, hq, hc3⟩ := toConfig_inv t3
  subst hc1 hc3
  obtain ⟨x, xs, y, hnz, hev, hx, hy, rfl, rfl⟩ := zero_inv h12
  obtain ⟨hpx, hpl⟩ := Prod.mk.injEq _ _ _ _ ▸ hp
  obtain rfl : x = p := by omega
  subst hpl
  rcases tryHalve_inv h23 with ⟨h0, a, as, hlist, hs3⟩ | ⟨h0, hs3⟩
  · obtain rfl : x = 0 := h0
    rw [hq] at hs3
    obtain ⟨rfl, rfl⟩ : a = q ∧ as = qs := by
      have := (Prod.mk.injEq _ _ _ _ ▸ hs3.symm)
      exact ⟨by omega, this.2⟩
    have h := zero_O (xs := xs) (y := y) hnz hev hy
    rw [show xs ++ [y + 1, 0, 0] = a :: as from hlist] at h
    exact h
  · rw [hq] at hs3
    obtain ⟨hx1, hl1⟩ := Prod.mk.injEq _ _ _ _ ▸ hs3
    obtain rfl : x = q + 1 := by omega
    subst hl1
    exact zero_S (x := q) (xs := xs) (y := y) hnz hev (by simpa using hx) hy

/-- Coq `Overflow_toConfig`. -/
lemma Overflow_toConfig {s1 s2 s3 s4 : S17} {c1 c4 : Config 4 1}
    (h12 : Overflow s1 s2) (h23 : Zero s2 s3) (h34 : TryHalve s3 s4)
    (t1 : toConfig s1 c1) (t4 : toConfig s4 c4) : c1 -[M]->* c4 := by
  obtain ⟨p, ps, hp, hc1⟩ := toConfig_inv t1
  obtain ⟨q, qs, hq, hc4⟩ := toConfig_inv t4
  subst hc1 hc4
  obtain ⟨x, xs, y, hnz, hev, hx, hy, rfl, rfl⟩ := overflow_inv h12
  obtain ⟨hpx, hpl⟩ := Prod.mk.injEq _ _ _ _ ▸ hp
  obtain rfl : x = p := by omega
  subst hpl
  obtain ⟨x', xs', y', _, _, _, hy', h2, h3⟩ := zero_inv h23
  -- `s2 = (x+1, xs ++ [y+1, 0]) = (x'+1, xs' ++ [y'])` forces
  -- `x' = x`, `y' = 0`, `xs' = xs ++ [y+1]`.
  obtain ⟨hx2, hl2⟩ := Prod.mk.injEq _ _ _ _ ▸ h2
  obtain rfl : x = x' := by omega
  obtain ⟨hxs', rfl⟩ : xs' = xs ++ [y + 1] ∧ y' = 0 := by
    have : xs ++ [y + 1, 0] = (xs ++ [y + 1]) ++ [0] := by
      simp
    rw [this] at hl2
    have := List.append_inj' hl2.symm rfl
    exact ⟨this.1, by simpa using this.2⟩
  subst hxs'
  rw [h3] at h34
  rcases tryHalve_inv h34 with ⟨h0, a, as, hlist, hs4⟩ | ⟨h0, hs4⟩
  · obtain rfl : x = 0 := h0
    rw [hq] at hs4
    obtain ⟨rfl, rfl⟩ : a = q ∧ as = qs := by
      have := (Prod.mk.injEq _ _ _ _ ▸ hs4.symm)
      exact ⟨by omega, this.2⟩
    have h := overflow_O (xs := xs) (y := y) hnz hev hy
    have hgoal : (xs ++ [y + 1]) ++ [0 + 1, 0, 0] = xs ++ [y + 1, 1, 0, 0] := by
      simp
    rw [← hgoal, show (xs ++ [y + 1]) ++ [0 + 1, 0, 0] = a :: as from hlist] at h
    exact h
  · rw [hq] at hs4
    obtain ⟨hx1, hl1⟩ := Prod.mk.injEq _ _ _ _ ▸ hs4
    obtain rfl : x = q + 1 := by omega
    have h := overflow_S (x := q) (xs := xs) (y := y) hnz hev (by simpa using hx) hy
    have hgoal : (xs ++ [y + 1]) ++ [0 + 1, 0, 0] = xs ++ [y + 1, 1, 0, 0] := by
      simp
    rw [hl1, hgoal]
    exact h

end Deciders.Skelet.Skelet17
