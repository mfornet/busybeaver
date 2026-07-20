import Busybeaver.Deciders.Skelet.Skelet17.Tape
import Busybeaver.Deciders.Skelet.Skelet17.Abstract
import Busybeaver.Deciders.Skelet.Skelet17.Induction

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


/-! ### The `toConfig` lifting layer (Coq lines 6390–6688) -/

/-- `toConfig` is functional. -/
lemma toConfig_functional {s : S17} {c c' : Config 4 1}
    (h : toConfig s c) (h' : toConfig s c') : c = c' := by
  obtain ⟨x, xs, hs, rfl⟩ := toConfig_inv h
  obtain ⟨x', xs', hs', rfl⟩ := toConfig_inv h'
  rw [hs] at hs'
  obtain ⟨hx, hl⟩ := Prod.mk.injEq _ _ _ _ ▸ hs'
  obtain rfl : x = x' := by omega
  rw [hl]

/-- Coq `Increment_precond_toConfig`. -/
lemma Increment_precond_toConfig {s1 s2 : S17} (h : Increment s1 s2) :
    ∃ c1, toConfig s1 c1 := by
  cases h <;> exact ⟨_, toConfig.intro _ _⟩

/-- Coq `Increments_precond_toConfig`. -/
lemma Increments_precond_toConfig {n : ℕ} {s1 s2 : S17}
    (h : Increments (n + 1) s1 s2) : ∃ c1, toConfig s1 c1 := by
  cases h with
  | succ h1 _ => exact Increment_precond_toConfig h1

/-- Coq `Zero_precond_toConfig`. -/
lemma Zero_precond_toConfig {s1 s2 : S17} (h : Zero s1 s2) :
    ∃ c1, toConfig s1 c1 := by
  cases h
  exact ⟨_, toConfig.intro _ _⟩

/-- Coq `Overflow_precond_toConfig`. -/
lemma Overflow_precond_toConfig {s1 s2 : S17} (h : Overflow s1 s2) :
    ∃ c1, toConfig s1 c1 := by
  cases h
  exact ⟨_, toConfig.intro _ _⟩

/-- Coq `toConfig_TryHalve_id`. -/
lemma toConfig_TryHalve_id {s1 : S17} {c1 : Config 4 1} (h : toConfig s1 c1) :
    TryHalve s1 s1 := by
  cases h
  exact TryHalve.zero _ _

/-- Coq `Halve_TryHalve`. -/
lemma Halve_TryHalve {s1 s2 : S17} (h : Halve s1 s2) : TryHalve s1 s2 := by
  cases h
  exact TryHalve.one _ _

/-- Coq `Increments_toConfig`. -/
lemma Increments_toConfig : ∀ {n : ℕ} {s1 s2 s3 : S17} {c1 c3 : Config 4 1},
    Increments (n + 1) s1 s2 → TryHalve s2 s3 →
    toConfig s1 c1 → toConfig s3 c3 → c1 -[M]->* c3 := by
  intro n
  induction n with
  | zero =>
      intro s1 s2 s3 c1 c3 h12 h23 t1 t3
      cases h12 with
      | succ h1 hrest =>
          cases hrest
          exact Increment_toConfig h1 h23 t1 t3
  | succ n ih =>
      intro s1 s2 s3 c1 c3 h12 h23 t1 t3
      cases h12 with
      | succ h1 hrest =>
          obtain ⟨c6, t6⟩ := Increments_precond_toConfig hrest
          exact (Increment_toConfig h1 (toConfig_TryHalve_id t6) t1 t6).trans
            (ih hrest h23 t6 t3)

/-- Coq `ZIH_toConfig`. -/
lemma ZIH_toConfig {n : ℕ} {s1 s2 s3 s4 : S17} {c1 c4 : Config 4 1}
    (Z12 : Zero s1 s2) (I23 : Increments n s2 s3) (H34 : Halve s3 s4)
    (t1 : toConfig s1 c1) (t4 : toConfig s4 c4) : c1 -[M]->* c4 := by
  rcases n with _ | n
  · cases I23
    exact Zero_toConfig Z12 (Halve_TryHalve H34) t1 t4
  · obtain ⟨c5, t5⟩ := Increments_precond_toConfig I23
    exact (Zero_toConfig Z12 (toConfig_TryHalve_id t5) t1 t5).trans
      (Increments_toConfig I23 (Halve_TryHalve H34) t5 t4)

/-- Coq `OZIH_toConfig`. -/
lemma OZIH_toConfig {n : ℕ} {s1 s2 s3 s4 s5 : S17} {c1 c5 : Config 4 1}
    (O12 : Overflow s1 s2) (Z23 : Zero s2 s3) (I34 : Increments n s3 s4)
    (H45 : Halve s4 s5) (t1 : toConfig s1 c1) (t5 : toConfig s5 c5) :
    c1 -[M]->* c5 := by
  rcases n with _ | n
  · cases I34
    exact Overflow_toConfig O12 Z23 (Halve_TryHalve H45) t1 t5
  · obtain ⟨c3, t3⟩ := Increments_precond_toConfig I34
    exact (Overflow_toConfig O12 Z23 (toConfig_TryHalve_id t3) t1 t3).trans
      (Increments_toConfig I34 (Halve_TryHalve H45) t3 t5)

/-- Coq `embanked_toConfig`. -/
lemma embanked_toConfig {s1 s7 : S17} {c1 c7 : Config 4 1}
    {s_1 h_1 s_2 h_2 : ℕ}
    (He : Embanked s1 s7 s_1 h_1 s_2 h_2)
    (t1 : toConfig s1 c1) (t7 : toConfig s7 c7) : c1 -[M]->* c7 := by
  obtain ⟨n1, s1, s6, s7, s8, s_1, h_1, s_2, h_2, hwemb, I67, Z78, hge, a70,
    a7, hwf7, hs7s, hs7n, hleq⟩ := He
  obtain ⟨m1, m2, s1, s2, s3, s4, s5, s6, Z12, I23, H34, I45, H56, hwf1, hs1s,
    hs1n, hs1l, hs1a0_odd, hs1a0_lt, hs1a1_lt, hwf6, hs6s, hs6l, n34, n56, n3e,
    n4e, n5e, n6e, a60, a6⟩ := hwemb
  obtain ⟨c4, t4⟩ := Increments_precond_toConfig I45
  have step1 : c1 -[M]->* c4 := ZIH_toConfig Z12 I23 H34 t1 t4
  rcases n1 with _ | n1
  · cases I67
    exact step1.trans (Increments_toConfig I45 (Halve_TryHalve H56) t4 t7)
  · obtain ⟨c6, t6⟩ := Increments_precond_toConfig I67
    exact step1.trans
      ((Increments_toConfig I45 (Halve_TryHalve H56) t4 t6).trans
        (Increments_toConfig I67 (toConfig_TryHalve_id t7) t6 t7))

/-- Coq `embanked_precond_toConfig`. -/
lemma embanked_precond_toConfig {e ne : S17} {s_1 h_1 s_2 h_2 : ℕ}
    (He : Embanked e ne s_1 h_1 s_2 h_2) : ∃ c, toConfig e c := by
  obtain ⟨n1, e, s6, ne, s8, s_1, h_1, s_2, h_2, hwemb, _, _, _, _, _, _, _,
    _, _⟩ := He
  obtain ⟨m1, m2, e, s2, s3, s4, s5, s6, Z12, _, _, _, _, _, _, _, _, _, _, _,
    _, _, _, _, _, _, _, _, _, _, _⟩ := hwemb
  exact Zero_precond_toConfig Z12

/-- Coq `embanked_postcond_toConfig`. -/
lemma embanked_postcond_toConfig {e ne : S17} {s_1 h_1 s_2 h_2 : ℕ}
    (He : Embanked e ne s_1 h_1 s_2 h_2) : ∃ c, toConfig ne c := by
  obtain ⟨n1, e, s6, ne, s8, s_1, h_1, s_2, h_2, hwemb, I67, Z78, _, _, _, _,
    _, _, _⟩ := He
  exact Zero_precond_toConfig Z78

/-- Coq `embanked_batch_precond_toConfig`. -/
lemma embanked_batch_precond_toConfig {i : ℕ} {e ne : S17} {h_1 h_2 : ℕ}
    (Heb : EmbankedBatch i e ne h_1 h_2) : ∃ c, toConfig e c := by
  cases Heb with
  | zero He Ha => exact embanked_precond_toConfig He
  | one He Ha => exact embanked_precond_toConfig He
  | ss He Ha Heb => exact embanked_precond_toConfig He

/-- Coq `embanked_batch_postcond_toConfig`. -/
lemma embanked_batch_postcond_toConfig {i : ℕ} {e ne : S17} {h_1 h_2 : ℕ}
    (Heb : EmbankedBatch i e ne h_1 h_2) : ∃ c, toConfig ne c := by
  induction Heb with
  | zero He Ha => exact embanked_postcond_toConfig He
  | one He Ha => exact embanked_postcond_toConfig He
  | ss He Ha Heb ih => exact ih

/-- Coq `embanked_batch_toConfig`. -/
lemma embanked_batch_toConfig {i : ℕ} {e ne : S17} {h_1 h_2 : ℕ}
    {c1 c2 : Config 4 1}
    (Heb : EmbankedBatch i e ne h_1 h_2)
    (t1 : toConfig e c1) (t2 : toConfig ne c2) : c1 -[M]->* c2 := by
  induction Heb generalizing c1 c2 with
  | zero He Ha => exact embanked_toConfig He t1 t2
  | one He Ha => exact embanked_toConfig He t1 t2
  | ss He Ha Heb ih =>
      obtain ⟨c3, t3⟩ := embanked_batch_precond_toConfig Heb
      exact (embanked_toConfig He t1 t3).trans (ih t3 t2)

/-- Coq `N'steps_postcond_toConfig`. -/
lemma NSteps_postcond_toConfig {e ne : S17} {h1a h2a h1b h2b : ℕ}
    (HN : NSteps e h1a h2a ne h1b h2b) : ∃ c, toConfig ne c := by
  cases HN with
  | refl Heb => exact embanked_batch_postcond_toConfig Heb
  | step _ Heb => exact embanked_batch_postcond_toConfig Heb

/-- Coq `N'steps_toConfig`. -/
lemma NSteps_toConfig {e ne : S17} {h1a h2a h1b h2b : ℕ}
    {c1 c2 : Config 4 1}
    (HN : NSteps e h1a h2a ne h1b h2b)
    (t1 : toConfig e c1) (t2 : toConfig ne c2) : c1 -[M]->* c2 := by
  induction HN generalizing c1 c2 with
  | refl Heb =>
      rw [toConfig_functional t1 t2]
      exact Machine.EvStep.refl
  | step HN Heb ih =>
      obtain ⟨c3, t3⟩ := embanked_batch_precond_toConfig Heb
      exact (ih t1 t3).trans (embanked_batch_toConfig Heb t3 t2)

/-- Coq `ZIHIO_emb_toConfig`. -/
lemma ZIHIO_emb_toConfig {k : ℕ} {e ne ne' : S17} {s_1 h_1 s_2 h_2 : ℕ}
    {c1 c2 : Config 4 1}
    (HZ : ZIHIO k e ne) (He : Embanked ne ne' s_1 h_1 s_2 h_2)
    (t1 : toConfig e c1) (t2 : toConfig ne' c2) : c1 -[M]->* c2 := by
  obtain ⟨n1, n2, e, z2, z3, z4, z5, ne, Z12, I23, H34, I45, O56, _, _, _, _,
    _, _, _, _⟩ := HZ
  obtain ⟨c5, t5⟩ := Increments_precond_toConfig I45
  have step1 : c1 -[M]->* c5 := ZIH_toConfig Z12 I23 H34 t1 t5
  obtain ⟨p1, ne, w6, ne', w8, ws1, wh1, ws2, wh2, hwemb, I67, Z78, hge, a70,
    a7, hwf7, hs7s, hs7n, hleq⟩ := He
  obtain ⟨q1, q2, ne, v2, v3, v4, v5, w6, Z12b, I23b, H34b, I45b, H56b, _, _,
    _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _⟩ := hwemb
  obtain ⟨c6, t6⟩ := Overflow_precond_toConfig O56
  have step2 : c5 -[M]->* c6 :=
    Increments_toConfig I45 (toConfig_TryHalve_id t6) t5 t6
  obtain ⟨c4', t4'⟩ := Increments_precond_toConfig I45b
  have step3 : c6 -[M]->* c4' := OZIH_toConfig O56 Z12b I23b H34b t6 t4'
  refine step1.trans (step2.trans (step3.trans ?_))
  rcases p1 with _ | p1
  · cases I67
    exact Increments_toConfig I45b (Halve_TryHalve H56b) t4' t2
  · obtain ⟨c6', t6'⟩ := Increments_precond_toConfig I67
    exact (Increments_toConfig I45b (Halve_TryHalve H56b) t4' t6').trans
      (Increments_toConfig I67 (toConfig_TryHalve_id t2) t6' t2)

/-- Coq `ZIHIO_embanked_batch_toConfig`. -/
lemma ZIHIO_embanked_batch_toConfig {i k : ℕ} {e ne ne' : S17} {h_1 h_2 : ℕ}
    {c1 c2 : Config 4 1}
    (HZ : ZIHIO k e ne) (Heb : EmbankedBatch i ne ne' h_1 h_2)
    (t1 : toConfig e c1) (t2 : toConfig ne' c2) : c1 -[M]->* c2 := by
  cases Heb with
  | zero He Ha => exact ZIHIO_emb_toConfig HZ He t1 t2
  | one He Ha => exact ZIHIO_emb_toConfig HZ He t1 t2
  | ss He Ha Heb =>
      obtain ⟨c', t'⟩ := embanked_batch_precond_toConfig Heb
      exact (ZIHIO_emb_toConfig HZ He t1 t').trans
        (embanked_batch_toConfig Heb t' t2)


/-- Coq `Sk_closed`: one full `Base k → Base (k+1)` round trip on the tape. -/
lemma Sk_closed {k : ℕ} (hk : k ≠ 0) {b : S17} {c : Config 4 1}
    (Hb : BaseS k b) (C : toConfig b c) :
    ∃ b' c', BaseS (k + 1) b' ∧ toConfig b' c' ∧ (c -[M]->* c') := by
  obtain ⟨e, ne, HN, Heb, HA, Ha, n'ne, HebB, Hl', Ha0', Ha1', Ha', Ha_last'⟩ :=
    Sk_to_E'' Hb hk
  obtain ⟨c1, C1⟩ := embanked_batch_postcond_toConfig Heb
  have c_c1 : c -[M]->* c1 := embanked_batch_toConfig Heb C C1
  obtain ⟨c2, C2⟩ := embanked_batch_precond_toConfig HebB
  have c1_c2 : c1 -[M]->* c2 := NSteps_toConfig HN C1 C2
  obtain ⟨c3, C3⟩ := embanked_batch_postcond_toConfig HebB
  have c2_c3 : c2 -[M]->* c3 := embanked_batch_toConfig HebB C2 C3
  obtain ⟨ez, HZ⟩ := E''_Overflow hk ⟨ne, HebB⟩ Hl' Ha0' Ha1' Ha' Ha_last'
  obtain ⟨nez, Hemb⟩ := ZIHIO_emb hk HZ
  obtain ⟨nez2, HebC, HlC, Ha0C, Ha1C, HaC⟩ :=
    ZIHIO_embanked_batch hk HZ Hemb
  obtain ⟨b', h_1, h_2, HebD, Hb'⟩ := last_step HebC HlC Ha0C Ha1C HaC
  obtain ⟨c4, C4⟩ := embanked_batch_postcond_toConfig HebC
  have c3_c4 : c3 -[M]->* c4 := ZIHIO_embanked_batch_toConfig HZ HebC C3 C4
  obtain ⟨c5, C5⟩ := embanked_batch_postcond_toConfig HebD
  have c4_c5 : c4 -[M]->* c5 := embanked_batch_toConfig HebD C4 C5
  exact ⟨b', c5, Hb', C5,
    c_c1.trans (c1_c2.trans (c2_c3.trans (c3_c4.trans c4_c5)))⟩


/-! ### The final assembly (Coq lines 6690–6866) -/

/-- `n`-fold application of the machine step (computable). -/
private def stepN : ℕ → Config 4 1 → Option (Config 4 1)
  | 0, c => some c
  | n + 1, c => (Machine.step M c).bind (stepN n)

/-- A successful `stepN` run yields an `EvStep` reachability. -/
private lemma stepN_evstep : ∀ (n : ℕ) {c d : Config 4 1},
    stepN n c = some d → c -[M]->* d
  | 0, c, d, h => by
      simp only [stepN, Option.some.injEq] at h
      subst h
      exact Machine.EvStep.refl
  | n + 1, c, d, h => by
      rw [stepN] at h
      cases hc : Machine.step M c with
      | none => rw [hc] at h; simp at h
      | some c1 =>
          rw [hc] at h
          exact Machine.EvStep.step hc (stepN_evstep n h)

set_option maxRecDepth 2048 in
/-- Coq `base`: the blank tape reaches `lower [0, 4, 2, 0]` in 205 steps. -/
lemma base : init -[M]->* lower [0, 4, 2, 0] := by
  refine stepN_evstep 205 ?_
  decide

/-- Coq `Base_1`. -/
def Base1 : S17 := (1, [4, 2, 0])

/-- Coq `Base_1_spec`. -/
lemma Base1_spec : BaseS 1 Base1 := by
  refine BaseS.intro _ rfl ?_ (by rw [toL_eq_length]; rfl)
  intro i
  match i with
  | 0 => rfl
  | 1 => rfl
  | 2 => rfl
  | (n + 3) =>
      have h1 : ai (n + 3) Base1 = 0 := by
        simp [ai, Base1]
      rw [h1, if_neg (by omega)]

/-- Coq `Base_1_toConfig`. -/
lemma Base1_toConfig : toConfig Base1 (lower [0, 4, 2, 0]) :=
  toConfig.intro 0 [4, 2, 0]

/-! ### `Base k` configs at distinct `k` have distinct tapes (Coq `Base_ne`) -/

/-- `pow10L` shifts `nth` by `2a`. -/
lemma pow10L_nth_shift (a : ℕ) (n : ℕ) (l : ListBlank (Symbol 1)) :
    (pow10L a l).nth (2 * a + n) = l.nth n := by
  induction a with
  | zero => rw [show 2 * 0 + n = n by omega]; rfl
  | succ a ih =>
      show (ListBlank.cons (0 : Symbol 1) (ListBlank.cons (1 : Symbol 1) (pow10L a l))).nth
        (2 * (a + 1) + n) = l.nth n
      rw [show 2 * (a + 1) + n = 2 * a + n + 1 + 1 by omega,
        ListBlank.nth_succ, ListBlank.tail_cons,
        ListBlank.nth_succ, ListBlank.tail_cons]
      exact ih

/-- Even positions inside a `pow10L` block read `𝟘`. -/
lemma pow10L_nth_even (a : ℕ) (j : ℕ) (l : ListBlank (Symbol 1)) (h : j < a) :
    (pow10L a l).nth (2 * j) = (0 : Symbol 1) := by
  induction a generalizing j with
  | zero => omega
  | succ a ih =>
      match j with
      | 0 =>
          show (ListBlank.cons (0 : Symbol 1) (ListBlank.cons (1 : Symbol 1) (pow10L a l))).nth 0 = (0 : Symbol 1)
          rw [ListBlank.nth_zero, ListBlank.head_cons]
      | j + 1 =>
          show (ListBlank.cons (0 : Symbol 1) (ListBlank.cons (1 : Symbol 1) (pow10L a l))).nth
            (2 * (j + 1)) = (0 : Symbol 1)
          rw [show 2 * (j + 1) = 2 * j + 1 + 1 by omega,
            ListBlank.nth_succ, ListBlank.tail_cons,
            ListBlank.nth_succ, ListBlank.tail_cons]
          exact ih j (by omega)

/-- The head-block distinguisher: `lowerL'` separates lists whose head
exponents differ, provided the smaller one has a successor entry. -/
lemma lowerL'_head_ne {a a' : ℕ} {t t' : List ℕ} (h : a < a')
    (ht : t ≠ []) : lowerL' (a :: t) ≠ lowerL' (a' :: t') := by
  intro heq
  have h1 : (lowerL' (a :: t)).nth (2 * a + 1) = (1 : Symbol 1) := by
    show (ListBlank.cons (1 : Symbol 1) (pow10L a (lowerL' t))).nth (2 * a + 1) = (1 : Symbol 1)
    rw [ListBlank.nth_succ, ListBlank.tail_cons,
      show 2 * a = 2 * a + 0 by omega, pow10L_nth_shift]
    obtain ⟨y, t2, rfl⟩ := List.exists_cons_of_ne_nil ht
    show (ListBlank.cons (1 : Symbol 1) (pow10L y (lowerL' t2))).nth 0 = (1 : Symbol 1)
    rw [ListBlank.nth_zero, ListBlank.head_cons]
  have h2 : (lowerL' (a' :: t')).nth (2 * a + 1) = (0 : Symbol 1) := by
    show (ListBlank.cons (1 : Symbol 1) (pow10L a' (lowerL' t'))).nth (2 * a + 1) = (0 : Symbol 1)
    rw [ListBlank.nth_succ, ListBlank.tail_cons]
    exact pow10L_nth_even a' a _ h
  rw [heq, h2] at h1
  exact absurd h1 (by decide)

/-- Coq `Base_ne`: consecutive base camps have distinct tape configs. -/
lemma Base_ne {k : ℕ} (hk : k ≠ 0) {b b' : S17} {c c' : Config 4 1}
    (Hb : BaseS k b) (Hb' : BaseS (k + 1) b')
    (C : toConfig b c) (C' : toConfig b' c') : c ≠ c' := by
  obtain ⟨hb0, hba, hbl⟩ := baseS_inv Hb
  obtain ⟨hb0', hba', hbl'⟩ := baseS_inv Hb'
  obtain ⟨x, xs, hbeq, rfl⟩ := toConfig_inv C
  obtain ⟨x', xs', hbeq', rfl⟩ := toConfig_inv C'
  rw [hbeq] at hb0 hba hbl
  rw [hbeq'] at hb0' hba' hbl'
  obtain rfl : x = 0 := by simpa using hb0
  obtain rfl : x' = 0 := by simpa using hb0'
  rw [toL_eq_length] at hbl hbl'
  -- decompose the digit lists
  rcases xs with _ | ⟨a, t⟩
  · simp at hbl
  rcases xs' with _ | ⟨a', t'⟩
  · simp at hbl'
  · have ha : a = 2 ^ (k * 2) := by
      have := hba 0
      rw [if_pos (by omega)] at this
      simpa [ai] using this
    have ha' : a' = 2 ^ ((k + 1) * 2) := by
      have := hba' 0
      rw [if_pos (by omega)] at this
      simpa [ai] using this
    have hlt : a < a' := by
      rw [ha, ha']
      exact Nat.pow_lt_pow_right (by omega) (by omega)
    have ht : t ≠ [] := by
      intro hnil
      rw [hnil] at hbl
      simp at hbl
      omega
    have hne := lowerL'_head_ne (t' := t') hlt ht
    intro heq
    apply hne
    -- extract the left `ListBlank` from the config equality
    have htape : Tape.mk' (lowerL' (a :: t)).tail
          (ListBlank.cons (lowerL' (a :: t)).head ∅)
        = Tape.mk' (lowerL' (a' :: t')).tail
          (ListBlank.cons (lowerL' (a' :: t')).head ∅) :=
      congrArg (fun cfg : Config 4 1 => cfg.2) heq
    have hL : (lowerL' (a :: t)).tail = (lowerL' (a' :: t')).tail := by
      have := congrArg Turing.Tape.left htape
      simpa [Tape.mk'_left] using this
    have hH : (lowerL' (a :: t)).head = (lowerL' (a' :: t')).head := by
      have := congrArg Turing.Tape.head htape
      simpa [Tape.mk'_head, ListBlank.head_cons] using this
    calc lowerL' (a :: t)
        = ((lowerL' (a :: t)).tail).cons ((lowerL' (a :: t)).head) :=
          (ListBlank.cons_head_tail _).symm
      _ = ((lowerL' (a' :: t')).tail).cons ((lowerL' (a' :: t')).head) := by
          rw [hH, hL]
      _ = lowerL' (a' :: t') := ListBlank.cons_head_tail _

/-- Turn a nontrivial reachability into strict progress. -/
lemma evstep_progress {c c' : Config 4 1} (h : c -[M]->* c') (hne : c ≠ c') :
    c -[M]->+ c' := by
  cases h with
  | refl => exact absurd rfl hne
  | step h1 h2 => exact Trans.trans (Machine.Progress.single h1) h2

/-- Skelet #17 does not halt (Coq `nonhalt`). -/
theorem nonHalting : ¬ M.halts init := by
  have cs : ClosedSet M
      (fun c => ∃ k b, k ≠ 0 ∧ BaseS k b ∧ toConfig b c) init := by
    refine ⟨?_, ?_⟩
    · rintro ⟨c, k, b, hk, Hb, Hc⟩
      obtain ⟨b', c', Hb', Hc', hcc⟩ := Sk_closed hk Hb Hc
      exact ⟨⟨c', k + 1, b', by omega, Hb', Hc'⟩,
        evstep_progress hcc (Base_ne hk Hb Hb' Hc Hc')⟩
    · exact ⟨⟨lower [0, 4, 2, 0], 1, Base1, by omega, Base1_spec,
        Base1_toConfig⟩, base⟩
  exact cs.nonHalting

end Deciders.Skelet.Skelet17
