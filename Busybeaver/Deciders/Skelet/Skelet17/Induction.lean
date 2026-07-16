import Busybeaver.Deciders.Skelet.Skelet17.Abstract

/-!
# Skelet #17 — level 6: the `Base k → Base (k+1)` induction

Port of Coq `Section Sk` (lines 4276–6324): the family `Base k` of milestone
configurations `(1, [2^2k, 2^(2k-1), …, 2, 0])` and the machinery showing each
is reachable from the previous one.
-/

namespace Deciders.Skelet.Skelet17

/-- Coq `Base` (Section hypothesis `k ≠ 0` is threaded explicitly). -/
inductive BaseS (k : ℕ) : S17 → Prop
  | intro (s : S17)
      (a0 : s.1 = 1)
      (a : ∀ i, ai i s = if i < k * 2 then 2 ^ (k * 2 - i) else 0)
      (l : toL s = k * 2 + 1) :
      BaseS k s

lemma baseS_inv {k : ℕ} {s : S17} (h : BaseS k s) :
    s.1 = 1 ∧ (∀ i, ai i s = if i < k * 2 then 2 ^ (k * 2 - i) else 0) ∧
      toL s = k * 2 + 1 := by
  cases h with | intro a0 a l => exact ⟨a0, a, l⟩

/-- Entries of a `Base` list are all even. -/
lemma baseS_allEven {k : ℕ} {x : ℕ} {xs : List ℕ}
    (ha : ∀ i, ai i (x, xs) = if i < k * 2 then 2 ^ (k * 2 - i) else 0) :
    AllEven xs := by
  intro a hmem
  obtain ⟨i, hi, rfl⟩ := List.mem_iff_getElem.1 hmem
  have h1 := ha i
  simp only [ai] at h1
  rw [List.getD_eq_getElem _ _ hi] at h1
  rw [h1]
  split_ifs with hc
  · exact pow2_even (by omega)
  · exact ⟨0, rfl⟩

/-- Coq `Base_embanked` (the first embanked step out of a base camp). -/
lemma Base_embanked {k : ℕ} (hk : k ≠ 0) {s1 : S17} (HB : BaseS k s1) :
    ∃ s7 s_1 s_2,
      Embanked s1 s7 s_1 (2 ^ (k * 2) - 1) s_2 (2 ^ (k * 2)) ∧
      Add2 (k * 2 + 1) s1 s7 := by
  obtain ⟨x, xs⟩ := s1
  obtain ⟨ha0, ha, hal⟩ := baseS_inv HB
  simp only at ha0
  subst ha0
  rw [toL_def] at hal
  -- list structure: `xs = xs.dropLast ++ [0]`
  have hxs_ne : xs ≠ [] := by
    intro h
    rw [h] at hal
    simp at hal
  have hlast : xs.getLast hxs_ne = 0 := by
    have h1 : xs.getLast hxs_ne = xs.getD (k * 2) 0 := by
      rw [List.getLast_eq_getElem, List.getD_eq_getElem _ _ (by omega)]
      congr 1
      omega
    have h2 := ha (k * 2)
    simp only [ai] at h2
    rw [h1, h2, if_neg (by omega)]
  have hxs_eq : xs = xs.dropLast ++ [0] := by
    conv_lhs => rw [← List.dropLast_append_getLast hxs_ne]
    rw [hlast]
  have hdl_len : xs.dropLast.length = k * 2 := by
    rw [List.length_dropLast, hal]
    omega
  have hnz : Nonzero xs.dropLast := by
    intro a hmem
    obtain ⟨i, hi, rfl⟩ := List.mem_iff_getElem.1 hmem
    rw [hdl_len] at hi
    have hgd : xs.dropLast[i] = xs.getD i 0 := by
      rw [List.getElem_dropLast, List.getD_eq_getElem _ _ (by omega)]
    have h2 := ha i
    simp only [ai] at h2
    rw [hgd, h2, if_pos hi]
    exact (Nat.two_pow_pos _).ne'
  have hev : AllEven xs := baseS_allEven ha
  -- preconditions of the weakly-embanked chain
  have hwf1 : WF1 (1, xs) := by
    rw [hxs_eq]
    exact WF1.intro 1 xs.dropLast 0 hnz
  have htn : toN (1, xs) = 0 := toN_allEven hev
  have hts : toS (1, xs) = false := by
    obtain ⟨I1, _⟩ := toN_zero_shape (by rwa [toN_def] at htn)
    rw [toS_def, I1]
    have hh : (List.replicate xs.length false).headD false = false := by
      cases h : xs.length <;> simp [List.replicate_succ]
    rw [hh]
    decide
  have hpow2k : 0 < 2 ^ (k * 2) := Nat.two_pow_pos _
  have hpow2k1 : 0 < 2 ^ (k * 2 + 1) := Nat.two_pow_pos _
  have hpow2ks : (2:ℕ) ^ (k * 2 + 1) = 2 ^ (k * 2) + 2 ^ (k * 2) := two_pow_succ' _
  have hpow2km : (2:ℕ) ^ (k * 2) = 2 ^ (k * 2 - 1) + 2 ^ (k * 2 - 1) := by
    conv_lhs => rw [show k * 2 = (k * 2 - 1) + 1 by omega]
    exact two_pow_succ' _
  have ha1 : ai 0 (1, xs) = 2 ^ (k * 2) := by
    rw [ha 0, if_pos (by omega)]
    norm_num
  have ha2 : ai 1 (1, xs) = 2 ^ (k * 2 - 1) := by
    rw [ha 1, if_pos (by omega)]
  have htl : toL (1, xs) = k * 2 + 1 := by rw [toL_def, hal]
  obtain ⟨s6, s_1, h_1, s_2, h_2, Hwemb⟩ := weakly_embanked_precond hwf1 hts htn
    (by omega) (by exact ⟨0, rfl⟩) (by rw [htl]; omega)
    (by rw [ha1, htl]
        simp only [show k * 2 + 1 - 1 = k * 2 by omega]
        omega)
  obtain ⟨-, -, -, -, -, -, -, -, -, -, n34, n56, n3e, n4e, n5e, n6e, a60, a6⟩ :=
    weaklyEmbanked_fields Hwemb
  rw [htl] at n3e n4e n5e n6e a60
  rw [ha1] at n5e n6e
  rw [ha2] at a60
  simp only [show (1:ℕ) / 2 = 0 by omega, Nat.add_zero,
    show k * 2 + 1 - 1 = k * 2 by omega, show k * 2 + 1 - 2 = k * 2 - 1 by omega]
    at n3e n4e n5e n6e a60
  -- counter values
  have hs_1 : s_1 = 2 ^ (k * 2 + 1) - 1 := by omega
  have hh_1 : h_1 = 2 ^ (k * 2) - 1 := by omega
  have hs_2 : s_2 = 2 ^ (k * 2 + 1) := by omega
  have hh_2 : h_2 = 2 ^ (k * 2) := by omega
  -- evaluate a60's divpow2r terms
  have e50 : divpow2r (2 ^ (k * 2 + 1)) 0 = 2 ^ (k * 2) := by
    have := divpow2r_pow2 0 (k * 2 + 1) (by omega)
    simpa [show k * 2 + 1 - (0 + 1) = k * 2 by omega] using this
  have e40 : divpow2r (2 ^ (k * 2) - 1) 0 = 2 ^ (k * 2 - 1) := by
    have := divpow2r_pow2sub1 0 (k * 2) (by omega)
    simpa [show k * 2 - (0 + 1) = k * 2 - 1 by omega] using this
  have e31 : divpow2r (2 ^ (k * 2 + 1) - 1) 1 = 2 ^ (k * 2 - 1) := by
    have := divpow2r_pow2sub1 1 (k * 2 + 1) (by omega)
    simpa [show k * 2 + 1 - (1 + 1) = k * 2 - 1 by omega] using this
  rw [hs_1, hh_1, hs_2] at a60
  rw [e50, e40, e31] at a60
  have ha60 : s6.1 = 2 ^ (k * 2) + 1 := by omega
  -- promote to embanked
  obtain ⟨s7, Hemb⟩ := embanked_precond Hwemb (by omega)
  obtain ⟨a70, a7, hwf7, hs7s, hs7n, hleq⟩ := embanked_fields Hemb
  rw [htl] at a70 a7
  rw [hs7n, hs_1, hh_1, hs_2, hh_2] at a70
  simp only [show k * 2 + 1 - 2 = k * 2 - 1 by omega] at a70
  -- `Add2 (k*2+1)`
  have HAdd : Add2 (k * 2 + 1) (1, xs) s7 := by
    refine Add2.intro _ _ _ fun j => ?_
    match j with
    | 0 =>
        simp only [ai']
        rw [if_neg (by omega : ¬(0:ℕ) = k * 2 + 1)]
        rw [e50, e40, e31, ha2] at a70
        omega
    | (j + 1) =>
        simp only [ai']
        have haj := a7 j
        rw [hs_1, hh_1, hs_2, hh_2] at haj
        rw [ha (j + 2)] at haj
        rw [ha j]
        simp only [show k * 2 + 1 - 1 = k * 2 by omega] at haj
        rcases Nat.lt_trichotomy (j + 1) (k * 2) with hr | hr | hr
        · have d1 : divpow2r (2 ^ (k * 2 + 1)) (j + 1) = 2 ^ (k * 2 - j - 1) := by
            have := divpow2r_pow2 (j + 1) (k * 2 + 1) (by omega)
            simpa [show k * 2 + 1 - (j + 1 + 1) = k * 2 - j - 1 by omega] using this
          have d2 : divpow2r (2 ^ (k * 2)) j = 2 ^ (k * 2 - j - 1) := by
            have := divpow2r_pow2 j (k * 2) (by omega)
            simpa [show k * 2 - (j + 1) = k * 2 - j - 1 by omega] using this
          have d3 : divpow2r (2 ^ (k * 2) - 1) (j + 1) = 2 ^ (k * 2 - j - 2) := by
            have := divpow2r_pow2sub1 (j + 1) (k * 2) (by omega)
            simpa [show k * 2 - (j + 1 + 1) = k * 2 - j - 2 by omega] using this
          rw [d1, d2, d3] at haj
          rw [if_pos (by omega : j < k * 2), if_neg (by omega : ¬(j + 1 : ℕ) = k * 2 + 1)]
          have hp1 : (2:ℕ) ^ (k * 2 - j) = 2 ^ (k * 2 - j - 1) + 2 ^ (k * 2 - j - 1) := by
            conv_lhs => rw [show k * 2 - j = (k * 2 - j - 1) + 1 by omega]
            exact two_pow_succ' _
          rcases Nat.lt_trichotomy (j + 2) (k * 2) with hr2 | hr2 | hr2
          · rw [if_neg (by omega : ¬(j + 2 : ℕ) = k * 2), if_pos (by omega)] at haj
            have hp2 : (2:ℕ) ^ (k * 2 - j - 1)
                = 2 ^ (k * 2 - j - 2) + 2 ^ (k * 2 - j - 2) := by
              conv_lhs => rw [show k * 2 - j - 1 = (k * 2 - j - 2) + 1 by omega]
              exact two_pow_succ' _
            have he : k * 2 - (j + 2) = k * 2 - j - 2 := by omega
            rw [he] at haj
            omega
          · rw [if_pos (by omega : (j + 2 : ℕ) = k * 2), if_neg (by omega)] at haj
            have : k * 2 - j - 2 = 0 := by omega
            rw [this] at haj
            have : (2:ℕ) ^ (0:ℕ) = 1 := rfl
            omega
          · omega
        · have d1 : divpow2r (2 ^ (k * 2 + 1)) (j + 1) = 1 := by
            have := divpow2r_pow2 (j + 1) (k * 2 + 1) (by omega)
            simpa [show k * 2 + 1 - (j + 1 + 1) = 0 by omega] using this
          have d2 : divpow2r (2 ^ (k * 2)) j = 1 := by
            have := divpow2r_pow2 j (k * 2) (by omega)
            simpa [show k * 2 - (j + 1) = 0 by omega] using this
          have d3 : divpow2r (2 ^ (k * 2) - 1) (j + 1) = 0 :=
            divpow2r_pow2sub1_small (by omega)
          rw [d1, d2, d3, if_neg (by omega : ¬(j + 2 : ℕ) = k * 2),
            if_neg (by omega : ¬(j + 2) < k * 2)] at haj
          rw [if_pos (by omega : j < k * 2),
            if_neg (by omega : ¬(j + 1 : ℕ) = k * 2 + 1),
            show k * 2 - j = 1 by omega]
          omega
        · rcases Nat.lt_trichotomy j (k * 2) with hr2 | hr2 | hr2
          · omega
          · have d1 : divpow2r (2 ^ (k * 2 + 1)) (j + 1) = 1 := by
              rw [show j + 1 = k * 2 + 1 by omega]
              exact divpow2r_pow2_1 _
            have d2 : divpow2r (2 ^ (k * 2)) j = 1 := by
              rw [show j = k * 2 by omega]
              exact divpow2r_pow2_1 _
            have d3 : divpow2r (2 ^ (k * 2) - 1) (j + 1) = 0 :=
              divpow2r_pow2sub1_small (by omega)
            rw [d1, d2, d3, if_neg (by omega : ¬(j + 2 : ℕ) = k * 2),
              if_neg (by omega : ¬(j + 2) < k * 2)] at haj
            rw [if_neg (by omega : ¬j < k * 2), if_pos (by omega : j + 1 = k * 2 + 1)]
            omega
          · have d1 : divpow2r (2 ^ (k * 2 + 1)) (j + 1) = 0 :=
              divpow2r_pow2_small (by omega)
            have d2 : divpow2r (2 ^ (k * 2)) j = 0 :=
              divpow2r_pow2_small (by omega)
            have d3 : divpow2r (2 ^ (k * 2) - 1) (j + 1) = 0 :=
              divpow2r_pow2sub1_small (by omega)
            rw [d1, d2, d3, if_neg (by omega : ¬(j + 2 : ℕ) = k * 2),
              if_neg (by omega : ¬(j + 2) < k * 2)] at haj
            rw [if_neg (by omega : ¬j < k * 2),
              if_neg (by omega : ¬(j + 1 : ℕ) = k * 2 + 1)]
            omega
  refine ⟨s7, s_1, s_2, ?_, HAdd⟩
  rw [← hh_1, ← hh_2]
  exact Hemb

/-- Coq `Base_embanked_batch`. -/
lemma Base_embanked_batch {k : ℕ} (hk : k ≠ 0) {e : S17} (HB : BaseS k e) :
    ∃ ne, EmbankedBatch (k * 2 + 1) e ne (2 ^ (k * 2) - 1) (2 ^ (k * 2)) ∧
      toL ne = k * 2 + 1 ∧ ai' 0 ne = 1 ∧ ai' 1 ne = 2 ^ (k * 2) + 2 ∧
      Add2s (k * 2 + 1) e ne := by
  obtain ⟨ne0, s_1, s_2, He, Ha⟩ := Base_embanked hk HB
  obtain ⟨ne, Hne⟩ := embanked_embanked_batch He Ha
  obtain ⟨ha0, ha, hal⟩ := baseS_inv HB
  obtain ⟨Ha0, Ha1⟩ := embanked_batch_a0_a1 Hne
  have hmod : (k * 2 + 1) % 2 = 1 := by omega
  refine ⟨ne, Hne, ?_, ?_, ?_, embanked_batch_Add2s Hne⟩
  · rw [← embanked_batch_len Hne, hal]
  · rw [Ha0, hmod]
    simp only [ai']
    omega
  · rw [Ha1, hmod]
    simp only [ai']
    have := ha 0
    rw [if_pos (by omega)] at this
    simp only [Nat.sub_zero] at this
    omega

/-- Coq `embanked_batch_precond''`. -/
lemma embanked_batch_precond'' {k : ℕ} {i : ℕ} {e ne : S17} {h_1 h_2 : ℕ}
    (Heb : EmbankedBatch i e ne h_1 h_2)
    (hl : toL ne = k * 2 + 1)
    (Ha0 : ai' 0 ne < 2 ^ (k * 2) * 2 - 1)
    (Ha1 : ai' 1 ne < 2 ^ (k * 2) * 3) :
    ∃ n'ne, match i % 2 with
      | 0 => EmbankedBatch (ctzS (h_1 - 1)) ne n'ne (h_1 - 1) h_2
      | _ => EmbankedBatch (ctzS h_2 + 1) ne n'ne h_1 (h_2 + 1) := by
  refine embanked_batch_precond' Heb ?_ ?_
  · rw [hl]
    have : (2:ℕ) ^ (k * 2 + 1) = 2 ^ (k * 2) + 2 ^ (k * 2) := two_pow_succ' _
    omega
  · rw [hl]
    simp only [show k * 2 + 1 - 1 = k * 2 by omega]
    omega

/-- Proposition 4.1, 2-step case (Coq `embanked_4batch`): when
`ctzS m, ctzS (m+1)` have parities `0, 1`, four batches advance
`(h₁, h₂) = (2^2k-1-m, 2^2k+m)` to `m+2` with predictable `ai` deltas. -/
lemma embanked_4batch {k : ℕ} {m i0 : ℕ} {e0 e1 : S17}
    (hm : m + 3 < 2 ^ (k * 2))
    (hc0 : ctzS m % 2 = 0) (hc1 : ctzS (m + 1) % 2 = 1)
    (Heb1 : EmbankedBatch i0 e0 e1 (2 ^ (k * 2) - 1 - m) (2 ^ (k * 2) + m))
    (hi0 : i0 % 2 = 1)
    (hl1 : toL e1 = k * 2 + 1)
    (ha10 : ai' 0 e1 = 1 + m * 2)
    (ha11 : ai' 1 e1 = 2 ^ (k * 2) + 2 + m * 2) :
    ∃ e2 i2 e3 i3 e4 i4 e5 i5,
      EmbankedBatch i2 e1 e2 (2 ^ (k * 2) - 1 - m) (2 ^ (k * 2) + (m + 1)) ∧
      EmbankedBatch i3 e2 e3 (2 ^ (k * 2) - 1 - m) (2 ^ (k * 2) + (m + 2)) ∧
      EmbankedBatch i4 e3 e4 (2 ^ (k * 2) - 1 - (m + 1)) (2 ^ (k * 2) + (m + 2)) ∧
      EmbankedBatch i5 e4 e5 (2 ^ (k * 2) - 1 - (m + 2)) (2 ^ (k * 2) + (m + 2)) ∧
      i5 % 2 = 1 ∧ toL e5 = k * 2 + 1 ∧
      ai' 0 e5 = 1 + (m + 2) * 2 ∧ ai' 1 e5 = 2 ^ (k * 2) + 2 + (m + 2) * 2 ∧
      (∀ i, ai i e5 + 2 * (m / 2 ^ i) = ai i e1 + 2 * ((m + 2) / 2 ^ i)) := by
  have hpk : 0 < 2 ^ (k * 2) := Nat.two_pow_pos _
  have hk0 : 0 < k * 2 := by
    by_contra h
    have hz : k * 2 = 0 := by omega
    rw [hz] at hm
    simp at hm
  have hc0a : ctzS (2 ^ (k * 2) + m) = ctzS m := ctzS_add (by omega)
  have hc1a : ctzS (2 ^ (k * 2) + (m + 1)) = ctzS (m + 1) := ctzS_add (by omega)
  have hc2a : ctzS (2 ^ (k * 2) - 1 - m - 1) = ctzS m := by
    rw [show 2 ^ (k * 2) - 1 - m - 1 = 2 ^ (k * 2) - m - 2 by omega]
    exact ctzS_sub (by omega) (by omega)
  have hc3a : ctzS (2 ^ (k * 2) - 1 - (m + 1) - 1) = ctzS (m + 1) := by
    rw [show 2 ^ (k * 2) - 1 - (m + 1) - 1 = 2 ^ (k * 2) - (m + 1) - 2 by omega]
    exact ctzS_sub (by omega) (by omega)
  -- step 1
  obtain ⟨e2, hb2⟩ := embanked_batch_precond'' (k := k) Heb1 hl1
    (by omega) (by omega)
  rw [hi0] at hb2
  have Hb2 : EmbankedBatch (ctzS m + 1) e1 e2
      (2 ^ (k * 2) - 1 - m) (2 ^ (k * 2) + (m + 1)) := by
    have h : EmbankedBatch (ctzS (2 ^ (k * 2) + m) + 1) e1 e2
        (2 ^ (k * 2) - 1 - m) (2 ^ (k * 2) + m + 1) := hb2
    rwa [hc0a] at h
  have hi2 : (ctzS m + 1) % 2 = 1 := by omega
  have hl2 : toL e2 = k * 2 + 1 := by rw [← embanked_batch_len Hb2, hl1]
  obtain ⟨Ha20, Ha21⟩ := embanked_batch_a0_a1 Hb2
  rw [hi2, ha10] at Ha20
  rw [hi2, ha11] at Ha21
  -- step 2
  obtain ⟨e3, hb3⟩ := embanked_batch_precond'' (k := k) Hb2 hl2
    (by omega) (by omega)
  rw [hi2] at hb3
  have Hb3 : EmbankedBatch (ctzS (m + 1) + 1) e2 e3
      (2 ^ (k * 2) - 1 - m) (2 ^ (k * 2) + (m + 2)) := by
    have h : EmbankedBatch (ctzS (2 ^ (k * 2) + (m + 1)) + 1) e2 e3
        (2 ^ (k * 2) - 1 - m) (2 ^ (k * 2) + (m + 1) + 1) := hb3
    rwa [hc1a] at h
  have hi3 : (ctzS (m + 1) + 1) % 2 = 0 := by omega
  have hl3 : toL e3 = k * 2 + 1 := by rw [← embanked_batch_len Hb3, hl2]
  obtain ⟨Ha30, Ha31⟩ := embanked_batch_a0_a1 Hb3
  rw [hi3, Ha20] at Ha30
  rw [hi3, Ha21] at Ha31
  -- step 3
  obtain ⟨e4, hb4⟩ := embanked_batch_precond'' (k := k) Hb3 hl3
    (by omega) (by omega)
  rw [hi3] at hb4
  have Hb4 : EmbankedBatch (ctzS m) e3 e4
      (2 ^ (k * 2) - 1 - (m + 1)) (2 ^ (k * 2) + (m + 2)) := by
    have h : EmbankedBatch (ctzS (2 ^ (k * 2) - 1 - m - 1)) e3 e4
        (2 ^ (k * 2) - 1 - m - 1) (2 ^ (k * 2) + (m + 2)) := hb4
    rw [hc2a] at h
    rwa [show 2 ^ (k * 2) - 1 - m - 1 = 2 ^ (k * 2) - 1 - (m + 1) by omega] at h
  have hl4 : toL e4 = k * 2 + 1 := by rw [← embanked_batch_len Hb4, hl3]
  obtain ⟨Ha40, Ha41⟩ := embanked_batch_a0_a1 Hb4
  rw [hc0, Ha30] at Ha40
  rw [hc0, Ha31] at Ha41
  -- step 4
  obtain ⟨e5, hb5⟩ := embanked_batch_precond'' (k := k) Hb4 hl4
    (by omega) (by omega)
  rw [hc0] at hb5
  have Hb5 : EmbankedBatch (ctzS (m + 1)) e4 e5
      (2 ^ (k * 2) - 1 - (m + 2)) (2 ^ (k * 2) + (m + 2)) := by
    have h : EmbankedBatch (ctzS (2 ^ (k * 2) - 1 - (m + 1) - 1)) e4 e5
        (2 ^ (k * 2) - 1 - (m + 1) - 1) (2 ^ (k * 2) + (m + 2)) := hb5
    rw [hc3a] at h
    rwa [show 2 ^ (k * 2) - 1 - (m + 1) - 1 = 2 ^ (k * 2) - 1 - (m + 2) by omega] at h
  have hl5 : toL e5 = k * 2 + 1 := by rw [← embanked_batch_len Hb5, hl4]
  obtain ⟨Ha50, Ha51⟩ := embanked_batch_a0_a1 Hb5
  rw [hc1, Ha40] at Ha50
  rw [hc1, Ha41] at Ha51
  -- the ai balance
  have Ha : ∀ i, ai i e5 + 2 * (m / 2 ^ i) = ai i e1 + 2 * ((m + 2) / 2 ^ i) := by
    intro i
    have h2 := add2s_inv (embanked_batch_Add2s Hb2) (i + 1)
    have h3 := add2s_inv (embanked_batch_Add2s Hb3) (i + 1)
    have h4 := add2s_inv (embanked_batch_Add2s Hb4) (i + 1)
    have h5 := add2s_inv (embanked_batch_Add2s Hb5) (i + 1)
    simp only [ai'] at h2 h3 h4 h5
    have hs1 := le_ctzS_sum i m
    have hs2 := le_ctzS_sum i (m + 1)
    rw [show m + 1 + 1 = m + 2 by omega] at hs2
    split_ifs at h2 h3 h4 h5 hs1 hs2 <;> omega
  exact ⟨e2, _, e3, _, e4, _, e5, _, Hb2, Hb3, Hb4, Hb5, by omega, hl5,
    by omega, by omega, Ha⟩

set_option maxHeartbeats 1000000 in
/-- Proposition 4.1, 4-step case (Coq `embanked_8batch`): parities
`0,0,0,1` for `ctzS m … ctzS (m+3)` give eight batches advancing by `m+4`. -/
lemma embanked_8batch {k : ℕ} {m i0 : ℕ} {e0 e1 : S17}
    (hm : m + 5 < 2 ^ (k * 2))
    (hc0 : ctzS m % 2 = 0) (hc1 : ctzS (m + 1) % 2 = 0)
    (hc2 : ctzS (m + 2) % 2 = 0) (hc3 : ctzS (m + 3) % 2 = 1)
    (Heb1 : EmbankedBatch i0 e0 e1 (2 ^ (k * 2) - 1 - m) (2 ^ (k * 2) + m))
    (hi0 : i0 % 2 = 1)
    (hl1 : toL e1 = k * 2 + 1)
    (ha10 : ai' 0 e1 = 1 + m * 2)
    (ha11 : ai' 1 e1 = 2 ^ (k * 2) + 2 + m * 2) :
    ∃ e2 i2 e3 i3 e4 i4 e5 i5 e6 i6 e7 i7 e8 i8 e9 i9,
      EmbankedBatch i2 e1 e2 (2 ^ (k * 2) - 1 - m) (2 ^ (k * 2) + (m + 1)) ∧
      EmbankedBatch i3 e2 e3 (2 ^ (k * 2) - 1 - m) (2 ^ (k * 2) + (m + 2)) ∧
      EmbankedBatch i4 e3 e4 (2 ^ (k * 2) - 1 - m) (2 ^ (k * 2) + (m + 3)) ∧
      EmbankedBatch i5 e4 e5 (2 ^ (k * 2) - 1 - m) (2 ^ (k * 2) + (m + 4)) ∧
      EmbankedBatch i6 e5 e6 (2 ^ (k * 2) - 1 - (m + 1)) (2 ^ (k * 2) + (m + 4)) ∧
      EmbankedBatch i7 e6 e7 (2 ^ (k * 2) - 1 - (m + 2)) (2 ^ (k * 2) + (m + 4)) ∧
      EmbankedBatch i8 e7 e8 (2 ^ (k * 2) - 1 - (m + 3)) (2 ^ (k * 2) + (m + 4)) ∧
      EmbankedBatch i9 e8 e9 (2 ^ (k * 2) - 1 - (m + 4)) (2 ^ (k * 2) + (m + 4)) ∧
      i9 % 2 = 1 ∧ toL e9 = k * 2 + 1 ∧
      ai' 0 e9 = 1 + (m + 4) * 2 ∧ ai' 1 e9 = 2 ^ (k * 2) + 2 + (m + 4) * 2 ∧
      (∀ i, ai i e9 + 2 * (m / 2 ^ i) = ai i e1 + 2 * ((m + 4) / 2 ^ i)) := by
  have hpk : 0 < 2 ^ (k * 2) := Nat.two_pow_pos _
  have hk0 : 0 < k * 2 := by
    by_contra h
    have hz : k * 2 = 0 := by omega
    rw [hz] at hm
    simp at hm
  have hA0 : ctzS (2 ^ (k * 2) + m) = ctzS m := ctzS_add (by omega)
  have hA1 : ctzS (2 ^ (k * 2) + (m + 1)) = ctzS (m + 1) := ctzS_add (by omega)
  have hA2 : ctzS (2 ^ (k * 2) + (m + 2)) = ctzS (m + 2) := ctzS_add (by omega)
  have hA3 : ctzS (2 ^ (k * 2) + (m + 3)) = ctzS (m + 3) := ctzS_add (by omega)
  have hS0 : ctzS (2 ^ (k * 2) - 1 - m - 1) = ctzS m := by
    rw [show 2 ^ (k * 2) - 1 - m - 1 = 2 ^ (k * 2) - m - 2 by omega]
    exact ctzS_sub (by omega) (by omega)
  have hS1 : ctzS (2 ^ (k * 2) - 1 - (m + 1) - 1) = ctzS (m + 1) := by
    rw [show 2 ^ (k * 2) - 1 - (m + 1) - 1 = 2 ^ (k * 2) - (m + 1) - 2 by omega]
    exact ctzS_sub (by omega) (by omega)
  have hS2 : ctzS (2 ^ (k * 2) - 1 - (m + 2) - 1) = ctzS (m + 2) := by
    rw [show 2 ^ (k * 2) - 1 - (m + 2) - 1 = 2 ^ (k * 2) - (m + 2) - 2 by omega]
    exact ctzS_sub (by omega) (by omega)
  have hS3 : ctzS (2 ^ (k * 2) - 1 - (m + 3) - 1) = ctzS (m + 3) := by
    rw [show 2 ^ (k * 2) - 1 - (m + 3) - 1 = 2 ^ (k * 2) - (m + 3) - 2 by omega]
    exact ctzS_sub (by omega) (by omega)
  -- four h₂-increment steps
  obtain ⟨e2, hb2⟩ := embanked_batch_precond'' (k := k) Heb1 hl1 (by omega) (by omega)
  rw [hi0] at hb2
  have Hb2 : EmbankedBatch (ctzS m + 1) e1 e2
      (2 ^ (k * 2) - 1 - m) (2 ^ (k * 2) + (m + 1)) := by
    have h : EmbankedBatch (ctzS (2 ^ (k * 2) + m) + 1) e1 e2
        (2 ^ (k * 2) - 1 - m) (2 ^ (k * 2) + m + 1) := hb2
    rwa [hA0] at h
  have hi2 : (ctzS m + 1) % 2 = 1 := by omega
  have hl2 : toL e2 = k * 2 + 1 := by rw [← embanked_batch_len Hb2, hl1]
  obtain ⟨Ha20, Ha21⟩ := embanked_batch_a0_a1 Hb2
  rw [hi2, ha10] at Ha20
  rw [hi2, ha11] at Ha21
  obtain ⟨e3, hb3⟩ := embanked_batch_precond'' (k := k) Hb2 hl2 (by omega) (by omega)
  rw [hi2] at hb3
  have Hb3 : EmbankedBatch (ctzS (m + 1) + 1) e2 e3
      (2 ^ (k * 2) - 1 - m) (2 ^ (k * 2) + (m + 2)) := by
    have h : EmbankedBatch (ctzS (2 ^ (k * 2) + (m + 1)) + 1) e2 e3
        (2 ^ (k * 2) - 1 - m) (2 ^ (k * 2) + (m + 1) + 1) := hb3
    rwa [hA1] at h
  have hi3 : (ctzS (m + 1) + 1) % 2 = 1 := by omega
  have hl3 : toL e3 = k * 2 + 1 := by rw [← embanked_batch_len Hb3, hl2]
  obtain ⟨Ha30, Ha31⟩ := embanked_batch_a0_a1 Hb3
  rw [hi3, Ha20] at Ha30
  rw [hi3, Ha21] at Ha31
  obtain ⟨e4, hb4⟩ := embanked_batch_precond'' (k := k) Hb3 hl3 (by omega) (by omega)
  rw [hi3] at hb4
  have Hb4 : EmbankedBatch (ctzS (m + 2) + 1) e3 e4
      (2 ^ (k * 2) - 1 - m) (2 ^ (k * 2) + (m + 3)) := by
    have h : EmbankedBatch (ctzS (2 ^ (k * 2) + (m + 2)) + 1) e3 e4
        (2 ^ (k * 2) - 1 - m) (2 ^ (k * 2) + (m + 2) + 1) := hb4
    rwa [hA2] at h
  have hi4 : (ctzS (m + 2) + 1) % 2 = 1 := by omega
  have hl4 : toL e4 = k * 2 + 1 := by rw [← embanked_batch_len Hb4, hl3]
  obtain ⟨Ha40, Ha41⟩ := embanked_batch_a0_a1 Hb4
  rw [hi4, Ha30] at Ha40
  rw [hi4, Ha31] at Ha41
  obtain ⟨e5, hb5⟩ := embanked_batch_precond'' (k := k) Hb4 hl4 (by omega) (by omega)
  rw [hi4] at hb5
  have Hb5 : EmbankedBatch (ctzS (m + 3) + 1) e4 e5
      (2 ^ (k * 2) - 1 - m) (2 ^ (k * 2) + (m + 4)) := by
    have h : EmbankedBatch (ctzS (2 ^ (k * 2) + (m + 3)) + 1) e4 e5
        (2 ^ (k * 2) - 1 - m) (2 ^ (k * 2) + (m + 3) + 1) := hb5
    rwa [hA3] at h
  have hi5 : (ctzS (m + 3) + 1) % 2 = 0 := by omega
  have hl5 : toL e5 = k * 2 + 1 := by rw [← embanked_batch_len Hb5, hl4]
  obtain ⟨Ha50, Ha51⟩ := embanked_batch_a0_a1 Hb5
  rw [hi5, Ha40] at Ha50
  rw [hi5, Ha41] at Ha51
  -- four h₁-decrement steps
  obtain ⟨e6, hb6⟩ := embanked_batch_precond'' (k := k) Hb5 hl5 (by omega) (by omega)
  rw [hi5] at hb6
  have Hb6 : EmbankedBatch (ctzS m) e5 e6
      (2 ^ (k * 2) - 1 - (m + 1)) (2 ^ (k * 2) + (m + 4)) := by
    have h : EmbankedBatch (ctzS (2 ^ (k * 2) - 1 - m - 1)) e5 e6
        (2 ^ (k * 2) - 1 - m - 1) (2 ^ (k * 2) + (m + 4)) := hb6
    rw [hS0] at h
    rwa [show 2 ^ (k * 2) - 1 - m - 1 = 2 ^ (k * 2) - 1 - (m + 1) by omega] at h
  have hl6 : toL e6 = k * 2 + 1 := by rw [← embanked_batch_len Hb6, hl5]
  obtain ⟨Ha60, Ha61⟩ := embanked_batch_a0_a1 Hb6
  rw [hc0, Ha50] at Ha60
  rw [hc0, Ha51] at Ha61
  obtain ⟨e7, hb7⟩ := embanked_batch_precond'' (k := k) Hb6 hl6 (by omega) (by omega)
  rw [hc0] at hb7
  have Hb7 : EmbankedBatch (ctzS (m + 1)) e6 e7
      (2 ^ (k * 2) - 1 - (m + 2)) (2 ^ (k * 2) + (m + 4)) := by
    have h : EmbankedBatch (ctzS (2 ^ (k * 2) - 1 - (m + 1) - 1)) e6 e7
        (2 ^ (k * 2) - 1 - (m + 1) - 1) (2 ^ (k * 2) + (m + 4)) := hb7
    rw [hS1] at h
    rwa [show 2 ^ (k * 2) - 1 - (m + 1) - 1 = 2 ^ (k * 2) - 1 - (m + 2) by omega] at h
  have hl7 : toL e7 = k * 2 + 1 := by rw [← embanked_batch_len Hb7, hl6]
  obtain ⟨Ha70, Ha71⟩ := embanked_batch_a0_a1 Hb7
  rw [hc1, Ha60] at Ha70
  rw [hc1, Ha61] at Ha71
  obtain ⟨e8, hb8⟩ := embanked_batch_precond'' (k := k) Hb7 hl7 (by omega) (by omega)
  rw [hc1] at hb8
  have Hb8 : EmbankedBatch (ctzS (m + 2)) e7 e8
      (2 ^ (k * 2) - 1 - (m + 3)) (2 ^ (k * 2) + (m + 4)) := by
    have h : EmbankedBatch (ctzS (2 ^ (k * 2) - 1 - (m + 2) - 1)) e7 e8
        (2 ^ (k * 2) - 1 - (m + 2) - 1) (2 ^ (k * 2) + (m + 4)) := hb8
    rw [hS2] at h
    rwa [show 2 ^ (k * 2) - 1 - (m + 2) - 1 = 2 ^ (k * 2) - 1 - (m + 3) by omega] at h
  have hl8 : toL e8 = k * 2 + 1 := by rw [← embanked_batch_len Hb8, hl7]
  obtain ⟨Ha80, Ha81⟩ := embanked_batch_a0_a1 Hb8
  rw [hc2, Ha70] at Ha80
  rw [hc2, Ha71] at Ha81
  obtain ⟨e9, hb9⟩ := embanked_batch_precond'' (k := k) Hb8 hl8 (by omega) (by omega)
  rw [hc2] at hb9
  have Hb9 : EmbankedBatch (ctzS (m + 3)) e8 e9
      (2 ^ (k * 2) - 1 - (m + 4)) (2 ^ (k * 2) + (m + 4)) := by
    have h : EmbankedBatch (ctzS (2 ^ (k * 2) - 1 - (m + 3) - 1)) e8 e9
        (2 ^ (k * 2) - 1 - (m + 3) - 1) (2 ^ (k * 2) + (m + 4)) := hb9
    rw [hS3] at h
    rwa [show 2 ^ (k * 2) - 1 - (m + 3) - 1 = 2 ^ (k * 2) - 1 - (m + 4) by omega] at h
  have hl9 : toL e9 = k * 2 + 1 := by rw [← embanked_batch_len Hb9, hl8]
  obtain ⟨Ha90, Ha91⟩ := embanked_batch_a0_a1 Hb9
  rw [hc3, Ha80] at Ha90
  rw [hc3, Ha81] at Ha91
  -- the ai balance, paired batch by batch
  have Ha : ∀ i, ai i e9 + 2 * (m / 2 ^ i) = ai i e1 + 2 * ((m + 4) / 2 ^ i) := by
    intro i
    have h2 := add2s_inv (embanked_batch_Add2s Hb2) (i + 1)
    have h3 := add2s_inv (embanked_batch_Add2s Hb3) (i + 1)
    have h4 := add2s_inv (embanked_batch_Add2s Hb4) (i + 1)
    have h5 := add2s_inv (embanked_batch_Add2s Hb5) (i + 1)
    have h6 := add2s_inv (embanked_batch_Add2s Hb6) (i + 1)
    have h7 := add2s_inv (embanked_batch_Add2s Hb7) (i + 1)
    have h8 := add2s_inv (embanked_batch_Add2s Hb8) (i + 1)
    have h9 := add2s_inv (embanked_batch_Add2s Hb9) (i + 1)
    simp only [ai'] at h2 h3 h4 h5 h6 h7 h8 h9
    have hs1 := le_ctzS_sum i m
    have hs2 := le_ctzS_sum i (m + 1)
    have hs3 := le_ctzS_sum i (m + 2)
    have hs4 := le_ctzS_sum i (m + 3)
    rw [show m + 1 + 1 = m + 2 by omega] at hs2
    rw [show m + 2 + 1 = m + 3 by omega] at hs3
    rw [show m + 3 + 1 = m + 4 by omega] at hs4
    -- pair the batches: (b2,b6) → ctzS m; (b3,b7) → ctzS (m+1); etc.
    have q0 : (if i + 1 ≤ ctzS m + 1 ∧ (i + 1) % 2 = (ctzS m + 1) % 2 then 2 else 0)
        + (if i + 1 ≤ ctzS m ∧ (i + 1) % 2 = ctzS m % 2 then 2 else 0)
        = if i ≤ ctzS m then 2 else 0 := by
      split_ifs <;> omega
    have q1 : (if i + 1 ≤ ctzS (m + 1) + 1 ∧ (i + 1) % 2 = (ctzS (m + 1) + 1) % 2 then 2 else 0)
        + (if i + 1 ≤ ctzS (m + 1) ∧ (i + 1) % 2 = ctzS (m + 1) % 2 then 2 else 0)
        = if i ≤ ctzS (m + 1) then 2 else 0 := by
      split_ifs <;> omega
    have q2 : (if i + 1 ≤ ctzS (m + 2) + 1 ∧ (i + 1) % 2 = (ctzS (m + 2) + 1) % 2 then 2 else 0)
        + (if i + 1 ≤ ctzS (m + 2) ∧ (i + 1) % 2 = ctzS (m + 2) % 2 then 2 else 0)
        = if i ≤ ctzS (m + 2) then 2 else 0 := by
      split_ifs <;> omega
    have q3 : (if i + 1 ≤ ctzS (m + 3) + 1 ∧ (i + 1) % 2 = (ctzS (m + 3) + 1) % 2 then 2 else 0)
        + (if i + 1 ≤ ctzS (m + 3) ∧ (i + 1) % 2 = ctzS (m + 3) % 2 then 2 else 0)
        = if i ≤ ctzS (m + 3) then 2 else 0 := by
      split_ifs <;> omega
    omega
  exact ⟨e2, _, e3, _, e4, _, e5, _, e6, _, e7, _, e8, _, e9, _,
    Hb2, Hb3, Hb4, Hb5, Hb6, Hb7, Hb8, Hb9, by omega, hl9,
    by omega, by omega, Ha⟩

/-! ### `ctzS` parity patterns and the chain structure (Coq lines 5097–5255) -/

/-- Coq `ctzS_chain`: the positions reachable by 2- and 4-jumps. -/
inductive CtzSChain : ℕ → Prop
  | zero : CtzSChain 0
  | s2 {n : ℕ} : CtzSChain n → ctzS n % 2 = 0 → ctzS (n + 1) % 2 = 1 →
      CtzSChain (n + 2)
  | s4 {n : ℕ} : CtzSChain n → ctzS n % 2 = 0 → ctzS (n + 1) % 2 = 0 →
      ctzS (n + 2) % 2 = 0 → ctzS (n + 3) % 2 = 1 → CtzSChain (n + 4)

lemma ctzS_even_0 {n : ℕ} (h : n % 2 = 0) : ctzS n = 0 := by
  apply (ctzS_spec n 0).2
  simpa using h

lemma ctzS_mod4eq1 {n : ℕ} (h : n % 4 = 1) : ctzS n = 1 := by
  apply (ctzS_spec n 1).2
  norm_num
  omega

lemma ctzS_odd_odd {n : ℕ} (h : ctzS n % 2 = 1) : n % 2 = 1 := by
  rcases Nat.mod_two_eq_zero_or_one n with h0 | h0
  · rw [ctzS_even_0 h0] at h
    omega
  · exact h0

/-- Coq `ctzS_chain_spec` (via mod-4 analysis, simpler than the original). -/
lemma ctzS_chain_spec : ∀ {n : ℕ}, ctzS n % 2 = 1 → CtzSChain (n + 1) := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro h
    have hodd : n % 2 = 1 := ctzS_odd_odd h
    match n, h, hodd, ih with
    | 0, h, hodd, _ => omega
    | 1, h, hodd, _ =>
        have h0 : ctzS 0 % 2 = 0 := by rw [ctzS_even_0 (by omega)]
        exact CtzSChain.s2 CtzSChain.zero h0 h
    | (m + 2), h, hodd, ih =>
        have hm_odd : m % 2 = 1 := by omega
        by_cases hpar : ctzS m % 2 = 1
        · have hc := ih m (by omega) hpar
          have h1 : ctzS (m + 1) % 2 = 0 := by rw [ctzS_even_0 (by omega)]
          have h2 : ctzS (m + 1 + 1) % 2 = 1 := by
            rw [show m + 1 + 1 = m + 2 by omega]
            exact h
          have := CtzSChain.s2 hc h1 h2
          rwa [show m + 1 + 2 = m + 2 + 1 by omega] at this
        · have hpar0 : ctzS m % 2 = 0 := by omega
          have hm4 : m % 4 = 3 := by
            rcases (by omega : m % 4 = 1 ∨ m % 4 = 3) with h4 | h4
            · exfalso
              have := ctzS_mod4eq1 h4
              omega
            · exact h4
          obtain ⟨m', rfl⟩ : ∃ m', m = m' + 3 := ⟨m - 3, by omega⟩
          have hc' : ctzS (m' + 1) % 2 = 1 := by
            rw [ctzS_mod4eq1 (by omega)]
          have hcc := ih (m' + 1) (by omega) hc'
          have h1 : ctzS (m' + 2) % 2 = 0 := by rw [ctzS_even_0 (by omega)]
          have h2 : ctzS (m' + 2 + 1) % 2 = 0 := by
            rw [show m' + 2 + 1 = m' + 3 by omega]
            exact hpar0
          have h3 : ctzS (m' + 2 + 2) % 2 = 0 := by
            rw [ctzS_even_0 (by omega)]
          have h4 : ctzS (m' + 2 + 3) % 2 = 1 := by
            rw [show m' + 2 + 3 = m' + 3 + 2 by omega]
            exact h
          have := CtzSChain.s4 hcc h1 h2 h3 h4
          rwa [show m' + 2 + 4 = m' + 3 + 2 + 1 by omega] at this

/-- Coq `N'steps`: a nonempty run of embanked batches with tracked `(h₁, h₂)`. -/
inductive NSteps : S17 → ℕ → ℕ → S17 → ℕ → ℕ → Prop
  | refl {i : ℕ} {e ne : S17} {h1 h2 : ℕ} :
      EmbankedBatch i e ne h1 h2 → NSteps ne h1 h2 ne h1 h2
  | step {i : ℕ} {e ne nne : S17} {h1 h2 h1a h2a h1b h2b : ℕ} :
      NSteps e h1 h2 ne h1a h2a → EmbankedBatch i ne nne h1b h2b →
      NSteps e h1 h2 nne h1b h2b

/-- Coq `embanked_batches` (Propositions 4.2/4.3): sweep `m` along a
`ctzS`-chain. -/
lemma embanked_batches {k : ℕ} {Sk : S17} (HBase : BaseS k Sk) (hk : k ≠ 0)
    {m : ℕ} (hm : m < 2 ^ (k * 2) - 1) (hcc : CtzSChain m) :
    ∃ e ne,
      NSteps e (2 ^ (k * 2) - 1) (2 ^ (k * 2)) ne
        (2 ^ (k * 2) - 1 - m) (2 ^ (k * 2) + m) ∧
      EmbankedBatch (k * 2 + 1) Sk e (2 ^ (k * 2) - 1) (2 ^ (k * 2)) ∧
      Add2s (k * 2 + 1) Sk e ∧
      (∃ e' i', EmbankedBatch i' e' ne (2 ^ (k * 2) - 1 - m) (2 ^ (k * 2) + m) ∧
        i' % 2 = 1) ∧
      toL ne = k * 2 + 1 ∧ ai' 0 ne = 1 + m * 2 ∧
      ai' 1 ne = 2 ^ (k * 2) + 2 + m * 2 ∧
      (∀ i, ai i ne = ai i e + 2 * (m / 2 ^ i)) := by
  induction hcc with
  | zero =>
      obtain ⟨e, Heb, hl, ha0, ha1, hadd2s⟩ := Base_embanked_batch hk HBase
      have Heb' : EmbankedBatch (k * 2 + 1) Sk e
          (2 ^ (k * 2) - 1 - 0) (2 ^ (k * 2) + 0) := by
        rwa [Nat.sub_zero, Nat.add_zero]
      refine ⟨e, e, NSteps.refl Heb', Heb, hadd2s,
        ⟨Sk, k * 2 + 1, Heb', by omega⟩, hl, by simpa using ha0,
        by simpa using ha1, fun i => by simp⟩
  | @s2 n hchain hc0 hc1 ih =>
      obtain ⟨e, ne, HN, Heb0, Hadd2s0, ⟨e', i', Heb', Hi'⟩, hl, ha0, ha1, Ha⟩ :=
        ih (by omega)
      obtain ⟨e2, i2, e3, i3, e4, i4, e5, i5, Heb2, Heb3, Heb4, Heb5, Hi5, Hl5,
        Ha50, Ha51, Ha5⟩ :=
        embanked_4batch (by omega) hc0 hc1 Heb' Hi' hl ha0 ha1
      refine ⟨e, e5,
        (((HN.step Heb2).step Heb3).step Heb4).step Heb5,
        Heb0, Hadd2s0, ⟨e4, i5, Heb5, Hi5⟩, Hl5, by omega, by omega, ?_⟩
      intro i
      have h1 := Ha i
      have h2 := Ha5 i
      omega
  | @s4 n hchain hc0 hc1 hc2 hc3 ih =>
      obtain ⟨e, ne, HN, Heb0, Hadd2s0, ⟨e', i', Heb', Hi'⟩, hl, ha0, ha1, Ha⟩ :=
        ih (by omega)
      obtain ⟨e2, i2, e3, i3, e4, i4, e5, i5, e6, i6, e7, i7, e8, i8, e9, i9,
        Heb2, Heb3, Heb4, Heb5, Heb6, Heb7, Heb8, Heb9, Hi9, Hl9, Ha90, Ha91,
        Ha9⟩ :=
        embanked_8batch (by omega) hc0 hc1 hc2 hc3 Heb' Hi' hl ha0 ha1
      refine ⟨e, e9,
        (((((((HN.step Heb2).step Heb3).step Heb4).step Heb5).step
          Heb6).step Heb7).step Heb8).step Heb9,
        Heb0, Hadd2s0, ⟨e8, i9, Heb9, Hi9⟩, Hl9, by omega, by omega, ?_⟩
      intro i
      have h1 := Ha i
      have h2 := Ha9 i
      omega

/-- Coq `pow22k_lower_bound`. -/
lemma pow22k_lower_bound {k : ℕ} (hk : k ≠ 0) : 4 ≤ 2 ^ (k * 2) := by
  have : (2:ℕ) ^ 2 ≤ 2 ^ (k * 2) := Nat.pow_le_pow_right (by omega) (by omega)
  omega

/-- Coq `Sk_to_E'` (Corollary 4.2): sweep all the way to `m = 2^2k - 2`. -/
lemma Sk_to_E' {k : ℕ} {Sk : S17} (HBase : BaseS k Sk) (hk : k ≠ 0) :
    ∃ e ne,
      NSteps e (2 ^ (k * 2) - 1) (2 ^ (k * 2)) ne 1 (2 ^ (k * 2) * 2 - 2) ∧
      EmbankedBatch (k * 2 + 1) Sk e (2 ^ (k * 2) - 1) (2 ^ (k * 2)) ∧
      Add2s (k * 2 + 1) Sk e ∧
      (∃ e' i', EmbankedBatch i' e' ne 1 (2 ^ (k * 2) * 2 - 2) ∧ i' % 2 = 1) ∧
      toL ne = k * 2 + 1 ∧ ai' 0 ne = 2 ^ (k * 2) * 2 - 3 ∧
      ai' 1 ne = 2 ^ (k * 2) * 3 - 2 ∧
      (∀ i, ai i ne = ai i e + 2 * ((2 ^ (k * 2) - 2) / 2 ^ i)) := by
  have hp4 := pow22k_lower_bound hk
  have hchain : CtzSChain (2 ^ (k * 2) - 2) := by
    have he : 2 ^ (k * 2) - 2 = (2 ^ (k * 2) - 3) + 1 := by omega
    rw [he]
    apply ctzS_chain_spec
    have hsub : ctzS (2 ^ (k * 2) - 1 - 2) = ctzS 1 :=
      ctzS_sub (by omega) (by omega)
    rw [show 2 ^ (k * 2) - 3 = 2 ^ (k * 2) - 1 - 2 by omega, hsub,
      ctzS_mod4eq1 (by omega)]
  obtain ⟨e, ne, HN, Heb0, Hadd2s0, ⟨e', i', Heb', Hi'⟩, hl, ha0, ha1, Ha⟩ :=
    embanked_batches HBase hk (m := 2 ^ (k * 2) - 2) (by omega) hchain
  rw [show 2 ^ (k * 2) - 1 - (2 ^ (k * 2) - 2) = 1 by omega,
    show 2 ^ (k * 2) + (2 ^ (k * 2) - 2) = 2 ^ (k * 2) * 2 - 2 by omega] at HN Heb'
  exact ⟨e, ne, HN, Heb0, Hadd2s0, ⟨e', i', Heb', Hi'⟩, hl, by omega, by omega, Ha⟩

/-- Coq `pow2sub_div_pow2`. -/
lemma pow2sub_div_pow2 {i j c : ℕ} (hj : j ≤ i) (hc1 : 0 < c) (hc2 : c ≤ 2 ^ j) :
    (2 ^ i - c) / 2 ^ j = 2 ^ (i - j) - 1 := by
  have hpj : 0 < 2 ^ j := Nat.two_pow_pos j
  have hpij : 0 < 2 ^ (i - j) := Nat.two_pow_pos _
  have hsplit : (2:ℕ) ^ i = 2 ^ j * 2 ^ (i - j) := by
    rw [← pow_add]
    congr 1
    omega
  have hmulsub : (2:ℕ) ^ j * (2 ^ (i - j) - 1) = 2 ^ j * 2 ^ (i - j) - 2 ^ j := by
    rw [Nat.mul_sub, Nat.mul_one]
  have hAK : (2:ℕ) ^ j ≤ 2 ^ j * 2 ^ (i - j) := Nat.le_mul_of_pos_right _ hpij
  rw [show (2:ℕ) ^ i - c = 2 ^ j * (2 ^ (i - j) - 1) + (2 ^ j - c) by omega,
    Nat.mul_add_div hpj, Nat.div_eq_of_lt (by omega)]
  omega

/-- Coq `pow2sub2_div_pow2`. -/
lemma pow2sub2_div_pow2 {i j : ℕ} (hj : j ≤ i) (h1 : 1 ≤ j) :
    (2 ^ i - 2) / 2 ^ j = 2 ^ (i - j) - 1 := by
  apply pow2sub_div_pow2 hj (by omega)
  have : (2:ℕ) ^ 1 ≤ 2 ^ j := Nat.pow_le_pow_right (by omega) h1
  simpa using this

/-- Coq `Sk_to_E''`: one more batch reaches `(1, 2^(2k+1) - 1)` with fully
computed digit profile. -/
lemma Sk_to_E'' {k : ℕ} {Sk : S17} (HBase : BaseS k Sk) (hk : k ≠ 0) :
    ∃ e ne,
      NSteps e (2 ^ (k * 2) - 1) (2 ^ (k * 2)) ne 1 (2 ^ (k * 2) * 2 - 2) ∧
      EmbankedBatch (k * 2 + 1) Sk e (2 ^ (k * 2) - 1) (2 ^ (k * 2)) ∧
      Add2s (k * 2 + 1) Sk e ∧
      (∀ i, ai i ne = ai i e + 2 * ((2 ^ (k * 2) - 2) / 2 ^ i)) ∧
      ∃ n'ne,
        EmbankedBatch 1 ne n'ne 1 (2 ^ (k * 2) * 2 - 1) ∧
        toL n'ne = k * 2 + 1 ∧
        ai' 0 n'ne = 2 ^ (k * 2) * 2 - 3 ∧
        ai' 1 n'ne = 2 ^ (k * 2) * 3 ∧
        (∀ i, 2 ≤ i → i ≤ k * 2 →
          ai' i n'ne = 2 ^ (k * 2 + 1 - i) * 3 - (1 - i % 2) * 2) ∧
        ai' (k * 2 + 1) n'ne = 2 := by
  have hp4 := pow22k_lower_bound hk
  obtain ⟨e, ne, HN, Heb0, Hadd2s0, ⟨e', i', Heb', Hi'⟩, hl, ha0, ha1, Ha⟩ :=
    Sk_to_E' HBase hk
  obtain ⟨n'ne, Heb⟩ := embanked_batch_precond'' (k := k) Heb' hl
    (by omega) (by omega)
  rw [Hi'] at Heb
  have hctz : ctzS (2 ^ (k * 2) * 2 - 2) = 0 := by
    have he : (2:ℕ) ^ (k * 2) * 2 = 2 ^ (k * 2 + 1) := by
      rw [pow_succ]
    rw [show 2 ^ (k * 2) * 2 - 2 = 2 ^ (k * 2 + 1) - 0 - 2 by omega]
    rw [ctzS_sub (by omega) (by
      have : (4:ℕ) ≤ 2 ^ (k * 2 + 1) := by
        have := Nat.pow_le_pow_right (by omega : 1 ≤ 2)
          (by omega : k * 2 ≤ k * 2 + 1)
        omega
      omega)]
    exact ctzS_even_0 (by omega)
  have HebF : EmbankedBatch 1 ne n'ne 1 (2 ^ (k * 2) * 2 - 1) := by
    have h : EmbankedBatch (ctzS (2 ^ (k * 2) * 2 - 2) + 1) ne n'ne 1
        (2 ^ (k * 2) * 2 - 2 + 1) := Heb
    rw [hctz] at h
    rwa [show 2 ^ (k * 2) * 2 - 2 + 1 = 2 ^ (k * 2) * 2 - 1 by omega] at h
  obtain ⟨Ha0', Ha1'⟩ := embanked_batch_a0_a1 HebF
  simp only [show (1:ℕ) % 2 = 1 by omega] at Ha0' Ha1'
  have hbase := baseS_inv HBase
  obtain ⟨hb0, hba, hbl⟩ := hbase
  refine ⟨e, ne, HN, Heb0, Hadd2s0, Ha, n'ne, HebF, ?_, by omega, by omega,
    ?_, ?_⟩
  · rw [← embanked_batch_len HebF, hl]
  · -- interior digits
    intro i h2i hik
    obtain ⟨j, rfl⟩ : ∃ j, i = j + 2 := ⟨i - 2, by omega⟩
    have hAdd1 := add2s_inv (embanked_batch_Add2s HebF) (j + 2)
    rw [if_neg (by omega)] at hAdd1
    have hAdd0 := add2s_inv Hadd2s0 (j + 2)
    have hai := Ha (j + 1)
    have hdiv : (2 ^ (k * 2) - 2) / 2 ^ (j + 1) = 2 ^ (k * 2 - (j + 1)) - 1 :=
      pow2sub2_div_pow2 (by omega) (by omega)
    have hb := hba (j + 1)
    rw [if_pos (by omega)] at hb
    simp only [ai'] at hAdd1 hAdd0 ⊢
    rw [hdiv] at hai
    rw [hb] at hAdd0
    have hpow : 0 < 2 ^ (k * 2 - (j + 1)) := Nat.two_pow_pos _
    have hexp : k * 2 + 1 - (j + 2) = k * 2 - (j + 1) := by omega
    rw [hexp]
    split_ifs at hAdd0 with hc <;> omega
  · -- the top digit
    have hAdd1 := add2s_inv (embanked_batch_Add2s HebF) (k * 2 + 1)
    rw [if_neg (by omega)] at hAdd1
    have hAdd0 := add2s_inv Hadd2s0 (k * 2 + 1)
    rw [if_pos (by omega)] at hAdd0
    have hai := Ha (k * 2)
    have hdiv : (2 ^ (k * 2) - 2) / 2 ^ (k * 2) = 0 := by
      apply Nat.div_eq_of_lt
      omega
    have hb := hba (k * 2)
    rw [if_neg (by omega)] at hb
    obtain ⟨j, hj⟩ : ∃ j, k * 2 + 1 = j + 1 := ⟨k * 2, rfl⟩
    simp only [ai'] at hAdd1 hAdd0 ⊢
    rw [hdiv] at hai
    rw [hb] at hAdd0
    omega

/-- Coq `ai_out_of_bound_0`. -/
lemma ai_out_of_bound {i : ℕ} {s : S17} (h : toL s ≤ i) : ai i s = 0 := by
  obtain ⟨x, xs⟩ := s
  rw [toL_def] at h
  simp only [ai]
  exact List.getD_eq_default _ _ (by omega)

/-- Coq `ZIHIO`: the overflow chain that grows the counter to `2k+3` digits. -/
inductive ZIHIO (k : ℕ) : S17 → S17 → Prop
  | intro (n1 n2 : ℕ) (s1 s2 s3 s4 s5 s6 : S17)
      (Z12 : Zero s1 s2) (I23 : Increments n1 s2 s3) (H34 : Halve s3 s4)
      (I45 : Increments (n2 + 1) s4 s5) (O56 : Overflow s5 s6)
      (hwf6 : WF1 s6) (hs6 : toS s6 = false) (hn6 : toN s6 = 0)
      (hl6 : toL s6 = k * 2 + 3) (ha60 : s6.1 = 1)
      (ha61 : ai 0 s6 = 2 ^ (k * 2 + 2) - 4)
      (ha6 : ∀ i, 2 ≤ i → i ≤ k * 2 + 2 →
        ai' i s6 = 2 ^ (k * 2 + 3 - i) - i % 2 * 2)
      (ha6last : ai' (k * 2 + 3) s6 = 0) :
      ZIHIO k s1 s6

set_option maxHeartbeats 1000000 in
/-- Coq `E''_Overflow`: from the `Sk_to_E''` profile the overflow chain fires. -/
lemma E''_Overflow {k : ℕ} (hk : k ≠ 0) {s1 : S17}
    (Heb : ∃ s0, EmbankedBatch 1 s0 s1 1 (2 ^ (k * 2) * 2 - 1))
    (hl1' : toL s1 = k * 2 + 1)
    (ha10 : ai' 0 s1 = 2 ^ (k * 2) * 2 - 3)
    (ha11 : ai' 1 s1 = 2 ^ (k * 2) * 3)
    (ha1 : ∀ i, 2 ≤ i → i ≤ k * 2 →
      ai' i s1 = 2 ^ (k * 2 + 1 - i) * 3 - (1 - i % 2) * 2)
    (ha1' : ai' (k * 2 + 1) s1 = 2) :
    ∃ s6, ZIHIO k s1 s6 := by
  have hp4 := pow22k_lower_bound hk
  have hpw1 : (2:ℕ) ^ (k * 2) * 2 = 2 ^ (k * 2 + 1) := by rw [pow_succ]
  have hpw2 : (2:ℕ) ^ (k * 2 + 1) * 2 = 2 ^ (k * 2 + 2) := (pow_succ 2 (k * 2 + 1)).symm
  have hpw3 : (2:ℕ) ^ (k * 2 + 2) * 2 = 2 ^ (k * 2 + 3) := (pow_succ 2 (k * 2 + 2)).symm
  obtain ⟨s0, Heb⟩ := Heb
  obtain ⟨hwf1, hs1, hn1, hl1, ha10_odd⟩ := embanked_batch_postcond Heb
  simp only [ai'] at ha10 ha11 ha1'
  -- Zero
  obtain ⟨s2, Z12, hwf2⟩ := Zero_precond hwf1 hs1 hn1
  have hs2 := Zero_sgn Z12
  have hn2 := Zero_n Z12
  have hl2 := Zero_len Z12
  have ha20 := Zero_a0 Z12
  have ha21 := Zero_a1 Z12 hl1
  have ha2 := Zero_a Z12
  rw [hl1'] at hn2 hl2 ha2
  rw [hpw1] at ha10
  have hn2' : toN s2 = 2 ^ (k * 2 + 1) - 1 := hn2
  have hn2_odd : Odd (toN s2) := by
    rw [hn2']
    refine ⟨2 ^ (k * 2) - 1, ?_⟩
    have h2 : (2:ℕ) ^ (k * 2 + 1) = 2 ^ (k * 2) + 2 ^ (k * 2) := two_pow_succ' _
    omega
  have hpk1 : 0 < 2 ^ (k * 2 + 1) := Nat.two_pow_pos _
  have hpk2 : 0 < 2 ^ (k * 2 + 2) := Nat.two_pow_pos _
  have hpks : (2:ℕ) ^ (k * 2 + 1) = 2 ^ (k * 2) + 2 ^ (k * 2) := two_pow_succ' _
  have hpks2 : (2:ℕ) ^ (k * 2 + 2) = 2 ^ (k * 2 + 1) + 2 ^ (k * 2 + 1) :=
    two_pow_succ' _
  -- Increments (dec) by fst s2
  obtain ⟨s3, I23, hwf3⟩ := Increments_dec_precond2 s2.1 hwf2 hs2
    (by omega) (le_refl _)
  have hs3 := Increments_sgn I23
  have hn3 := Increments_n I23
  have hl3 := Increments_len I23
  have ha30 := Increments_a0 I23
  have ha3 := Increments_a I23
  rw [hs2] at hn3 ha30 ha3
  simp only [Bool.false_eq_true, if_false] at hn3 ha30 ha3
  have ha30_0 : s3.1 = 0 := by omega
  have hn3' : toN s3 = 3 := by omega
  -- Halve
  obtain ⟨s4, H34, hwf4⟩ := Halve_precond2 hwf3 ha30_0 (by omega)
  have hs4 := Halve_sgn H34
  have hn4 := Halve_n H34
  have hl4 := Halve_len H34
  have ha40 := Halve_a0 H34
  have ha4 := Halve_a H34
  have hs3' : toS s3 = false := by rw [← hs3]; exact hs2
  have hs4' : toS s4 = true := by rw [← hs4, hs3']; rfl
  have hn4' : toN s4 = 1 := by omega
  have hl4' : toL s4 = k * 2 + 2 := by omega
  -- ai 0 s3
  have hdpA0 : divpow2r (2 ^ (k * 2 + 1) - 1) 0 = 2 ^ (k * 2) := by
    have := divpow2r_pow2sub1 0 (k * 2 + 1) (by omega)
    simpa using this
  have hdp30 : divpow2r 3 0 = 2 := by rw [divpow2r_zero]
  have ha31 := ha3 0
  rw [hn2', hn3', hdpA0, hdp30, ← ha21, ha11] at ha31
  have ha31' : ai 0 s3 = 2 ^ (k * 2 + 2) - 2 := by omega
  -- Increments (inc) by 2^(k*2+2) - 2
  obtain ⟨s5, I45, hwf5⟩ := Increments_inc_precond2 (2 ^ (k * 2 + 2) - 2)
    hwf4 hs4'
    (by rw [hl4', hn4', show k * 2 + 2 - 2 = k * 2 by omega]; omega)
    (by rw [hl4', hn4']; omega)
    (by omega)
  have hs5 := Increments_sgn I45
  have hn5 := Increments_n I45
  have hl5 := Increments_len I45
  have ha50 := Increments_a0 I45
  have ha5 := Increments_a I45
  rw [hs4'] at hn5 ha50 ha5
  simp only [if_true] at hn5 ha50 ha5
  have ha50' : s5.1 = 1 := by omega
  have hn5' : toN s5 = 2 ^ (k * 2 + 2) - 1 := by omega
  have hl5' : toL s5 = k * 2 + 2 := by omega
  have hs5' : toS s5 = true := by rw [← hs5]; exact hs4'
  -- Overflow
  obtain ⟨s6, O56, hwf6⟩ := Overflow_precond hwf5 hs5'
    (by rw [hl5']; exact hn5') ha50'
  have hs6 := Overflow_sgn O56
  have hn6 := Overflow_n O56
  have hl6 := Overflow_len O56
  have ha60 := Overflow_a0 O56
  have ha6 := Overflow_a O56
  have ha60' : s6.1 = 1 := by omega
  have hl6' : toL s6 = k * 2 + 3 := by omega
  rw [hl5'] at ha6
  simp only [show k * 2 + 2 - 1 = k * 2 + 1 by omega] at ha6
  -- divpow2r evaluation kit
  have hdpB : ∀ j, j + 1 ≤ k * 2 + 2 →
      divpow2r (2 ^ (k * 2 + 2) - 1) j = 2 ^ (k * 2 + 2 - (j + 1)) :=
    fun j hj => divpow2r_pow2sub1 j (k * 2 + 2) hj
  have hdpA : ∀ j, j + 1 ≤ k * 2 + 1 →
      divpow2r (2 ^ (k * 2 + 1) - 1) j = 2 ^ (k * 2 + 1 - (j + 1)) :=
    fun j hj => divpow2r_pow2sub1 j (k * 2 + 1) hj
  have hdpAs : ∀ j, k * 2 + 1 ≤ j → divpow2r (2 ^ (k * 2 + 1) - 1) j = 0 :=
    fun j hj => divpow2r_pow2sub1_small hj
  have hdp1 : ∀ j, 1 ≤ j → divpow2r 1 j = 0 := by
    intro j hj
    apply divpow2r_small
    have : (2:ℕ) ^ 1 ≤ 2 ^ j := Nat.pow_le_pow_right (by omega) hj
    omega
  have hdp3 : ∀ j, 2 ≤ j → divpow2r 3 j = 0 := by
    intro j hj
    apply divpow2r_small
    have : (2:ℕ) ^ 2 ≤ 2 ^ j := Nat.pow_le_pow_right (by omega) hj
    omega
  have hdp31 : divpow2r 3 1 = 1 := by
    unfold divpow2r
    norm_num
  have hdp10 : divpow2r 1 0 = 1 := by rw [divpow2r_zero]
  -- `ai 0 s6 = 2^(k*2+2) - 4`
  have ha61' : ai 0 s6 = 2 ^ (k * 2 + 2) - 4 := by
    have h6 := ha6 0
    rw [if_neg (by omega)] at h6
    have h5 := ha5 0
    rw [hn4', hn5', hdp10, hdpB 0 (by omega)] at h5
    have h4 : ai 0 s4 = ai 1 s3 := ha4 0
    have h3 := ha3 1
    rw [hn2', hn3', hdpA 1 (by omega), hdp31] at h3
    have h2 := ha2 1
    rw [if_neg (by omega)] at h2
    have h1 := ha1 2 (by omega) (by omega)
    simp only [ai'] at h1
    rw [show k * 2 + 1 - 2 = k * 2 - 1 by omega] at h1
    have hpkm : (2:ℕ) ^ (k * 2) = 2 ^ (k * 2 - 1) + 2 ^ (k * 2 - 1) := by
      conv_lhs => rw [show k * 2 = (k * 2 - 1) + 1 by omega]
      exact two_pow_succ' _
    have he1 : k * 2 + 1 - (1 + 1) = k * 2 - 1 := by omega
    have he2 : k * 2 + 2 - (0 + 1) = k * 2 + 1 := by omega
    rw [he1] at h3
    rw [he2] at h5
    have := Nat.two_pow_pos (k * 2 - 1)
    omega
  -- top digit vanishes
  have ha6last' : ai' (k * 2 + 3) s6 = 0 := by
    simp only [ai']
    have h6 := ha6 (k * 2 + 2)
    rw [if_neg (by omega)] at h6
    have h5 := ha5 (k * 2 + 2)
    rw [hn4', hn5', hdp1 _ (by omega),
      divpow2r_pow2sub1_small (by omega : k * 2 + 2 ≤ k * 2 + 2)] at h5
    have h4 := ha4 (k * 2 + 2)
    have h3 := ha3 (k * 2 + 3)
    rw [hn2', hn3', hdpAs _ (by omega), hdp3 _ (by omega)] at h3
    have h2 := ha2 (k * 2 + 3)
    rw [if_neg (by omega)] at h2
    have h1o : ai (k * 2 + 3) s1 = 0 := ai_out_of_bound (by omega)
    have h1o2 : ai (k * 2 + 2 + 1) s3 = ai (k * 2 + 3) s3 := by
      rw [show k * 2 + 2 + 1 = k * 2 + 3 by omega]
    omega
  -- interior digits
  have ha6i : ∀ i, 2 ≤ i → i ≤ k * 2 + 2 →
      ai' i s6 = 2 ^ (k * 2 + 3 - i) - i % 2 * 2 := by
    intro t h2t htk
    obtain ⟨u, rfl⟩ : ∃ u, t = u + 1 := ⟨t - 1, by omega⟩
    simp only [ai']
    have h6 := ha6 u
    have h5 := ha5 u
    rw [hn4', hn5', hdp1 _ (by omega), hdpB u (by omega)] at h5
    have h4 := ha4 u
    have h3 := ha3 (u + 1)
    rw [hn2', hn3', hdp3 _ (by omega)] at h3
    have h2 := ha2 (u + 1)
    rcases (by omega : u + 2 ≤ k * 2 ∨ u = k * 2 - 1 ∨ u = k * 2 ∨ u = k * 2 + 1)
      with hcase | hcase | hcase | hcase
    · -- interior
      rw [hdpA (u + 1) (by omega)] at h3
      rw [if_neg (by omega)] at h2
      rw [if_neg (by omega)] at h6
      have h1 := ha1 (u + 2) (by omega) (by omega)
      simp only [ai'] at h1
      have hE1 : k * 2 + 1 - (u + 1 + 1) = k * 2 - 1 - u := by omega
      have hE2 : k * 2 + 2 - (u + 1) = k * 2 + 1 - u := by omega
      have hE3 : k * 2 + 1 - (u + 2) = k * 2 - 1 - u := by omega
      have hE4 : k * 2 + 3 - (u + 1) = k * 2 + 2 - u := by omega
      rw [hE1] at h3
      rw [hE2] at h5
      rw [hE3] at h1
      rw [hE4]
      have hq1 : (2:ℕ) ^ (k * 2 - u) = 2 ^ (k * 2 - 1 - u) + 2 ^ (k * 2 - 1 - u) := by
        conv_lhs => rw [show k * 2 - u = (k * 2 - 1 - u) + 1 by omega]
        exact two_pow_succ' _
      have hq2 : (2:ℕ) ^ (k * 2 + 1 - u) = 2 ^ (k * 2 - u) + 2 ^ (k * 2 - u) := by
        conv_lhs => rw [show k * 2 + 1 - u = (k * 2 - u) + 1 by omega]
        exact two_pow_succ' _
      have hq3 : (2:ℕ) ^ (k * 2 + 2 - u)
          = 2 ^ (k * 2 + 1 - u) + 2 ^ (k * 2 + 1 - u) := by
        conv_lhs => rw [show k * 2 + 2 - u = (k * 2 + 1 - u) + 1 by omega]
        exact two_pow_succ' _
      have := Nat.two_pow_pos (k * 2 - 1 - u)
      omega
    · -- u = k*2 - 1
      subst hcase
      rw [hdpA (k * 2 - 1 + 1) (by omega)] at h3
      rw [if_pos (by omega : k * 2 - 1 + 1 = k * 2 + 1 - 1)] at h2
      rw [if_neg (by omega)] at h6
      rw [show k * 2 + 1 - (k * 2 - 1 + 1 + 1) = 0 by omega, pow_zero] at h3
      rw [show k * 2 - 1 + 1 = k * 2 by omega] at h2 h3 h4
      rw [show k * 2 + 2 - (k * 2 - 1 + 1) = 2 by omega,
        show (2:ℕ) ^ 2 = 4 by norm_num] at h5
      rw [show k * 2 + 3 - (k * 2 - 1 + 1) = 3 by omega,
        show (2:ℕ) ^ 3 = 8 by norm_num]
      have hu2 : (k * 2 - 1 + 1) % 2 = 0 := by omega
      rw [hu2]
      omega
    · -- u = k*2
      subst hcase
      rw [hdpAs (k * 2 + 1) (by omega)] at h3
      rw [if_neg (by omega)] at h2
      rw [if_neg (by omega)] at h6
      have h1o : ai (k * 2 + 1) s1 = 0 := ai_out_of_bound (by omega)
      rw [show k * 2 + 2 - (k * 2 + 1) = 1 by omega, pow_one] at h5
      rw [show k * 2 + 3 - (k * 2 + 1) = 2 by omega,
        show (2:ℕ) ^ 2 = 4 by norm_num]
      have hu2 : (k * 2 + 1) % 2 = 1 := by omega
      rw [hu2]
      omega
    · -- u = k*2 + 1
      subst hcase
      rw [hdpAs (k * 2 + 2) (by omega)] at h3
      rw [if_neg (by omega)] at h2
      rw [if_pos (by omega)] at h6
      have h1o : ai (k * 2 + 1 + 1) s1 = 0 := ai_out_of_bound (by omega)
      rw [show k * 2 + 2 - (k * 2 + 1 + 1) = 0 by omega, pow_zero] at h5
      rw [show k * 2 + 3 - (k * 2 + 1 + 1) = 1 by omega, pow_one]
      have hu2 : (k * 2 + 1 + 1) % 2 = 0 := by omega
      rw [hu2]
      omega
  -- package
  rw [show 2 ^ (k * 2 + 2) - 2 = (2 ^ (k * 2 + 2) - 3) + 1 by omega] at I45
  exact ⟨s6, ZIHIO.intro s2.1 (2 ^ (k * 2 + 2) - 3) s1 s2 s3 s4 s5 s6
    Z12 I23 H34 I45 O56 hwf6 hs6 hn6 hl6' ha60' ha61' ha6i ha6last'⟩

lemma zihio_inv {k : ℕ} {e ne : S17} (h : ZIHIO k e ne) :
    WF1 ne ∧ toS ne = false ∧ toN ne = 0 ∧ toL ne = k * 2 + 3 ∧ ne.1 = 1 ∧
      ai 0 ne = 2 ^ (k * 2 + 2) - 4 ∧
      (∀ i, 2 ≤ i → i ≤ k * 2 + 2 → ai' i ne = 2 ^ (k * 2 + 3 - i) - i % 2 * 2) ∧
      ai' (k * 2 + 3) ne = 0 := by
  cases h with
  | intro n1 n2 s1 s2 s3 s4 s5 s6 Z12 I23 H34 I45 O56 hwf6 hs6 hn6 hl6 ha60
      ha61 ha6 ha6last =>
    exact ⟨hwf6, hs6, hn6, hl6, ha60, ha61, ha6, ha6last⟩

set_option maxHeartbeats 1000000 in
/-- Coq `ZIHIO_emb`. -/
lemma ZIHIO_emb {k : ℕ} (_hk : k ≠ 0) {e ne : S17} (HZ : ZIHIO k e ne) :
    ∃ ne', Embanked ne ne' (2 ^ (k * 2 + 3) - 1) (2 ^ (k * 2 + 2) - 1)
      (2 ^ (k * 2 + 3) - 4) (2 ^ (k * 2 + 2) - 2) := by
  obtain ⟨hwf, hs, hn, hl, ha0, ha1, ha, halast⟩ := zihio_inv HZ
  have hp1 : 0 < 2 ^ (k * 2 + 1) := Nat.two_pow_pos _
  have hp2 : 0 < 2 ^ (k * 2 + 2) := Nat.two_pow_pos _
  have hps1 : (2:ℕ) ^ (k * 2 + 2) = 2 ^ (k * 2 + 1) + 2 ^ (k * 2 + 1) :=
    two_pow_succ' _
  have hps2 : (2:ℕ) ^ (k * 2 + 3) = 2 ^ (k * 2 + 2) + 2 ^ (k * 2 + 2) :=
    two_pow_succ' _
  have ha2v : ai 1 ne = 2 ^ (k * 2 + 1) := by
    have h2 := ha 2 (by omega) (by omega)
    simp only [ai'] at h2
    rw [h2, show k * 2 + 3 - 2 = k * 2 + 1 by omega]
    omega
  obtain ⟨s6, s_1, h_1, s_2, h_2, Hwemb⟩ := weakly_embanked_precond hwf hs hn
    (by omega) (by rw [ha0]; exact ⟨0, rfl⟩)
    (by rw [ha0, hl]
        have : (4:ℕ) ≤ 2 ^ (k * 2 + 3) := by
          have := Nat.pow_le_pow_right (by omega : 1 ≤ 2)
            (by omega : 2 ≤ k * 2 + 3)
          omega
        omega)
    (by rw [ha1, hl, show k * 2 + 3 - 1 = k * 2 + 2 by omega]
        omega)
  obtain ⟨-, -, -, -, -, -, -, -, -, -, n34, n56, n3e, n4e, n5e, n6e, a60, a6⟩ :=
    weaklyEmbanked_fields Hwemb
  rw [hl, ha0] at n3e n4e
  rw [hl] at n5e n6e a60
  rw [ha1] at n5e n6e
  simp only [show (1:ℕ) / 2 = 0 by omega, Nat.add_zero,
    show k * 2 + 3 - 1 = k * 2 + 2 by omega,
    show k * 2 + 3 - 2 = k * 2 + 1 by omega] at n3e n4e n5e n6e a60
  have hs_1 : s_1 = 2 ^ (k * 2 + 3) - 1 := by omega
  have hh_1 : h_1 = 2 ^ (k * 2 + 2) - 1 := by omega
  have hs_2 : s_2 = 2 ^ (k * 2 + 3) - 4 := by omega
  have hh_2 : h_2 = 2 ^ (k * 2 + 2) - 2 := by omega
  -- side condition: `s6.1 = 2^(k*2+2) - 1 ≥ h_2`
  have e40 : divpow2r (2 ^ (k * 2 + 2) - 1) 0 = 2 ^ (k * 2 + 1) := by
    have := divpow2r_pow2sub1 0 (k * 2 + 2) (by omega)
    simpa using this
  have e31 : divpow2r (2 ^ (k * 2 + 3) - 1) 1 = 2 ^ (k * 2 + 1) := by
    have := divpow2r_pow2sub1 1 (k * 2 + 3) (by omega)
    simpa [show k * 2 + 3 - (1 + 1) = k * 2 + 1 by omega] using this
  have e50 : divpow2r (2 ^ (k * 2 + 3) - 4) 0 = 2 ^ (k * 2 + 2) - 2 := by
    rw [divpow2r_zero]
    omega
  rw [hs_1, hh_1, hs_2, ha2v, e40, e31, e50] at a60
  obtain ⟨s7, Hemb⟩ := embanked_precond Hwemb (by omega)
  rw [hs_1, hh_1, hs_2, hh_2] at Hemb
  exact ⟨s7, Hemb⟩

set_option maxHeartbeats 2000000 in
/-- Coq `ZIHIO_emb_Add2`. -/
lemma ZIHIO_emb_Add2 {k : ℕ} (hk : k ≠ 0) {e ne ne' : S17} (HZ : ZIHIO k e ne)
    (He : Embanked ne ne' (2 ^ (k * 2 + 3) - 1) (2 ^ (k * 2 + 2) - 1)
      (2 ^ (k * 2 + 3) - 4) (2 ^ (k * 2 + 2) - 2)) :
    Add2 (k * 2 + 1) ne ne' := by
  obtain ⟨hwf, hs, hn, hl, ha0, ha1, ha, halast⟩ := zihio_inv HZ
  have hp4 := pow22k_lower_bound hk
  obtain ⟨a70, a7, hwf7, hs7s, hs7n, hleq⟩ := embanked_fields He
  rw [hl] at a70 a7
  rw [hs7n] at a70
  simp only [show k * 2 + 3 - 1 = k * 2 + 2 by omega,
    show k * 2 + 3 - 2 = k * 2 + 1 by omega] at a70 a7
  have hp1 : 0 < 2 ^ (k * 2 + 1) := Nat.two_pow_pos _
  have hp0 : 0 < 2 ^ (k * 2) := Nat.two_pow_pos _
  have hps0 : (2:ℕ) ^ (k * 2 + 1) = 2 ^ (k * 2) + 2 ^ (k * 2) := two_pow_succ' _
  have hps1 : (2:ℕ) ^ (k * 2 + 2) = 2 ^ (k * 2 + 1) + 2 ^ (k * 2 + 1) :=
    two_pow_succ' _
  have hps2 : (2:ℕ) ^ (k * 2 + 3) = 2 ^ (k * 2 + 2) + 2 ^ (k * 2 + 2) :=
    two_pow_succ' _
  -- divpow2r kit for the four counters
  have hdA : ∀ j, j + 1 ≤ k * 2 + 3 →
      divpow2r (2 ^ (k * 2 + 3) - 1) j = 2 ^ (k * 2 + 3 - (j + 1)) :=
    fun j hj => divpow2r_pow2sub1 j _ hj
  have hdAs : ∀ j, k * 2 + 3 ≤ j → divpow2r (2 ^ (k * 2 + 3) - 1) j = 0 :=
    fun j hj => divpow2r_pow2sub1_small hj
  have hdB : ∀ j, j + 1 ≤ k * 2 + 2 →
      divpow2r (2 ^ (k * 2 + 2) - 1) j = 2 ^ (k * 2 + 2 - (j + 1)) :=
    fun j hj => divpow2r_pow2sub1 j _ hj
  have hdBs : ∀ j, k * 2 + 2 ≤ j → divpow2r (2 ^ (k * 2 + 2) - 1) j = 0 :=
    fun j hj => divpow2r_pow2sub1_small hj
  have hhalf1 : (2 ^ (k * 2 + 3) - 4) / 2 = 2 ^ (k * 2 + 2) - 2 := by omega
  have hhalf2 : (2 ^ (k * 2 + 2) - 2) / 2 = 2 ^ (k * 2 + 1) - 1 := by omega
  have hdH : ∀ j, divpow2r (2 ^ (k * 2 + 2) - 2) (j + 1)
      = divpow2r (2 ^ (k * 2 + 1) - 1) j := by
    intro j
    rw [← divpow2r_div2, hhalf2]
  have hdS : ∀ j, divpow2r (2 ^ (k * 2 + 3) - 4) (j + 2)
      = divpow2r (2 ^ (k * 2 + 1) - 1) j := by
    intro j
    rw [← divpow2r_div2, hhalf1, ← divpow2r_div2, hhalf2]
  have hdC : ∀ j, j + 1 ≤ k * 2 + 1 →
      divpow2r (2 ^ (k * 2 + 1) - 1) j = 2 ^ (k * 2 + 1 - (j + 1)) :=
    fun j hj => divpow2r_pow2sub1 j _ hj
  have hdCs : ∀ j, k * 2 + 1 ≤ j → divpow2r (2 ^ (k * 2 + 1) - 1) j = 0 :=
    fun j hj => divpow2r_pow2sub1_small hj
  have hdS1 : divpow2r (2 ^ (k * 2 + 3) - 4) 1 = 2 ^ (k * 2 + 1) - 1 := by
    unfold divpow2r
    norm_num
    omega
  have hdS0 : divpow2r (2 ^ (k * 2 + 3) - 4) 0 = 2 ^ (k * 2 + 2) - 2 := by
    rw [divpow2r_zero]
    omega
  have hdH0 : divpow2r (2 ^ (k * 2 + 2) - 2) 0 = 2 ^ (k * 2 + 1) - 1 := by
    rw [divpow2r_zero]
    omega
  refine Add2.intro _ _ _ fun t => ?_
  match t with
  | 0 =>
      simp only [ai']
      rw [if_neg (by omega)]
      have h2v : ai 1 ne = 2 ^ (k * 2 + 1) := by
        have h2 := ha 2 (by omega) (by omega)
        simp only [ai'] at h2
        rw [h2, show k * 2 + 3 - 2 = k * 2 + 1 by omega]
        omega
      rw [h2v, hdS0, hdB 0 (by omega), hdA 1 (by omega)] at a70
      simp only [show k * 2 + 2 - (0 + 1) = k * 2 + 1 by omega,
        show k * 2 + 3 - (1 + 1) = k * 2 + 1 by omega] at a70
      omega
  | (j + 1) =>
      simp only [ai']
      have haj := a7 j
      match j with
      | 0 =>
          rw [if_neg (by omega)]
          simp only [Nat.zero_add] at haj
          rw [if_neg (by omega), hdS1, hdH0, hdB 1 (by omega),
            hdA 2 (by omega)] at haj
          have h3v : ai 2 ne = 2 ^ (k * 2) - 2 := by
            have h3 := ha 3 (by omega) (by omega)
            simp only [ai'] at h3
            rw [h3, show k * 2 + 3 - 3 = k * 2 by omega]
          rw [h3v] at haj
          simp only [show k * 2 + 2 - (1 + 1) = k * 2 by omega] at haj
          rw [ha1]
          omega
      | (u + 1) =>
          -- ai-index j = u+1 ≥ 1; use the halving bridges
          rw [show u + 1 + 1 = u + 2 by omega] at haj
          rw [hdS u, hdH u] at haj
          rcases (by omega : u + 1 + 1 ≤ k * 2 - 1 ∨ u + 1 = k * 2 - 1 ∨
              u + 1 = k * 2 ∨ u + 1 = k * 2 + 1 ∨ u + 1 = k * 2 + 2 ∨
              k * 2 + 3 ≤ u + 1) with hc | hc | hc | hc | hc | hc
          · -- general interior
            rw [if_neg (by omega)]
            rw [if_neg (by omega), hdC u (by omega), hdA (u + 2 + 1) (by omega),
              hdB (u + 2) (by omega)] at haj
            have hv1 : ai (u + 2 + 1) ne = ai' (u + 2 + 2) ne := rfl
            have h1 := ha (u + 4) (by omega) (by omega)
            simp only [ai'] at h1
            rw [show u + 2 + 1 = u + 3 by omega] at haj
            rw [show k * 2 + 3 - (u + 3 + 1) = k * 2 + 3 - (u + 4) by omega] at haj
            rw [h1] at haj
            have h2 := ha (u + 2) (by omega) (by omega)
            simp only [ai'] at h2
            rw [h2]
            rw [show k * 2 + 2 - (u + 3) = k * 2 + 3 - (u + 4) by omega] at haj
            have hq1 : (2:ℕ) ^ (k * 2 + 3 - (u + 2))
                = 2 ^ (k * 2 + 1 - (u + 1)) + 2 ^ (k * 2 + 1 - (u + 1)) := by
              rw [show k * 2 + 3 - (u + 2) = (k * 2 + 1 - (u + 1)) + 1 by omega]
              exact two_pow_succ' _
            rw [hq1]
            have hm : (u + 4) % 2 = (u + 2) % 2 := by omega
            rw [hm] at haj
            have := Nat.two_pow_pos (k * 2 + 3 - (u + 4))
            have hmb : (u + 2) % 2 ≤ 1 := by omega
            have h2p : (2:ℕ) ^ (k * 2 + 3 - (u + 4)) ≥ 2 := by
              have : (2:ℕ) ^ 1 ≤ 2 ^ (k * 2 + 3 - (u + 4)) :=
                Nat.pow_le_pow_right (by omega) (by omega)
              simpa using this
            omega
          · -- u+1 = k*2 - 1 (ai'-index k*2)
            rw [if_neg (by omega)]
            rw [if_neg (by omega), hdC u (by omega), hdA (u + 2 + 1) (by omega),
              hdB (u + 2) (by omega)] at haj
            have h1 := ha (u + 4) (by omega) (by omega)
            simp only [ai'] at h1
            rw [show u + 2 + 1 = u + 3 by omega, h1] at haj
            have h2 := ha (u + 2) (by omega) (by omega)
            simp only [ai'] at h2
            rw [h2]
            have e1 : k * 2 + 3 - (u + 4) = 1 := by omega
            have e2 : k * 2 + 1 - (u + 1) = 2 := by omega
            have e3 : k * 2 + 2 - (u + 2 + 1) = 1 := by omega
            have e4 : k * 2 + 3 - (u + 2) = 3 := by omega
            rw [e1] at haj
            rw [e2] at haj
            rw [e3] at haj
            rw [e4]
            have hm : (u + 4) % 2 = (u + 2) % 2 := by omega
            rw [hm] at haj
            have hmb : (u + 2) % 2 = 0 := by omega
            rw [hmb] at haj ⊢
            norm_num at haj ⊢
            omega
          · -- u+1 = k*2 (ai'-index k*2+1, the bump)
            rw [if_pos (by omega)]
            rw [if_pos (by omega), hdC u (by omega), hdA (u + 2 + 1) (by omega),
              hdB (u + 2) (by omega)] at haj
            have h1 : ai (u + 2 + 1) ne = 0 := by
              have hh := halast
              simp only [ai'] at hh
              rw [show u + 2 + 1 = k * 2 + 2 by omega]
              exact hh
            rw [h1] at haj
            have h2 := ha (u + 2) (by omega) (by omega)
            simp only [ai'] at h2
            rw [h2]
            have e1 : k * 2 + 1 - (u + 1) = 1 := by omega
            have e2 : k * 2 + 2 - (u + 2 + 1) = 0 := by omega
            have e3 : k * 2 + 3 - (u + 2) = 2 := by omega
            rw [e1] at haj
            rw [e2, pow_zero] at haj
            rw [e3]
            have hmb : (u + 2) % 2 = 1 := by omega
            rw [hmb]
            norm_num at haj ⊢
            omega
          · -- u+1 = k*2+1 (ai'-index k*2+2)
            rw [if_neg (by omega)]
            rw [if_neg (by omega), hdC u (by omega), hdBs (u + 2) (by omega),
              hdAs (u + 2 + 1) (by omega)] at haj
            have h1 : ai (u + 2 + 1) ne = 0 := by
              rw [show u + 2 + 1 = k * 2 + 3 by omega]
              exact ai_out_of_bound (by omega)
            rw [h1] at haj
            have h2 := ha (u + 2) (by omega) (by omega)
            simp only [ai'] at h2
            rw [h2]
            have e1 : k * 2 + 1 - (u + 1) = 0 := by omega
            have e2 : k * 2 + 3 - (u + 2) = 1 := by omega
            rw [e1, pow_zero] at haj
            rw [e2]
            have hmb : (u + 2) % 2 = 0 := by omega
            rw [hmb]
            norm_num at haj ⊢
            omega
          · -- u+1 = k*2+2 (ai'-index k*2+3)
            rw [if_neg (by omega)]
            rw [if_neg (by omega), hdCs u (by omega), hdBs (u + 2) (by omega),
              hdAs (u + 2 + 1) (by omega)] at haj
            have h1 : ai (u + 2 + 1) ne = 0 := by
              rw [show u + 2 + 1 = k * 2 + 4 by omega]
              exact ai_out_of_bound (by omega)
            rw [h1] at haj
            have h2 : ai (u + 1) ne = 0 := by
              have hh := halast
              simp only [ai'] at hh
              rw [show u + 1 = k * 2 + 2 by omega]
              exact hh
            rw [h2]
            omega
          · -- beyond
            rw [if_neg (by omega)]
            rw [if_neg (by omega), hdCs u (by omega), hdBs (u + 2) (by omega),
              hdAs (u + 2 + 1) (by omega)] at haj
            have h1 : ai (u + 2 + 1) ne = 0 := ai_out_of_bound (by omega)
            have h2 : ai (u + 1) ne = 0 := ai_out_of_bound (by omega)
            rw [h1] at haj
            rw [h2]
            omega

/-- Coq `ZIHIO_embanked_batch`: the ZIHIO-produced embanked step extends to a
full batch at index `k*2+1`, and the resulting configuration has the clean
doubled digit profile. -/
lemma ZIHIO_embanked_batch {k : ℕ} (hk : k ≠ 0) {e ne ne' : S17}
    (HZ : ZIHIO k e ne)
    (He : Embanked ne ne' (2 ^ (k * 2 + 3) - 1) (2 ^ (k * 2 + 2) - 1)
      (2 ^ (k * 2 + 3) - 4) (2 ^ (k * 2 + 2) - 2)) :
    ∃ n'ne, EmbankedBatch (k * 2 + 1) ne n'ne
        (2 ^ (k * 2 + 2) - 1) (2 ^ (k * 2 + 2) - 2) ∧
      toL n'ne = k * 2 + 3 ∧
      ai' 0 n'ne = 1 ∧
      ai' 1 n'ne = 2 ^ (k * 2 + 2) - 2 ∧
      (∀ i, 2 ≤ i →
        ai' i n'ne = if i < k * 2 + 3 then 2 ^ (k * 2 + 3 - i) else 0) := by
  have Ha := ZIHIO_emb_Add2 hk HZ He
  obtain ⟨n'ne, Heb⟩ := embanked_embanked_batch He Ha
  obtain ⟨hwf, hs, hn, hl, ha0, ha1, ha, halast⟩ := zihio_inv HZ
  have hlen := embanked_batch_len Heb
  have hln : toL n'ne = k * 2 + 3 := by rw [← hlen, hl]
  have hpar : (k * 2 + 1) % 2 = 1 := by omega
  have hp2 : (4:ℕ) ≤ 2 ^ (k * 2 + 2) := by
    calc (4:ℕ) = 2 ^ 2 := by norm_num
    _ ≤ 2 ^ (k * 2 + 2) := Nat.pow_le_pow_right (by omega) (by omega)
  obtain ⟨hb0, hb1⟩ := embanked_batch_a0_a1 Heb
  rw [hpar] at hb0 hb1
  have HA := embanked_batch_Add2s Heb
  refine ⟨n'ne, Heb, hln, ?_, ?_, ?_⟩
  · simp only [ai'] at hb0 ⊢
    rw [hb0, ha0]
  · simp only [ai'] at hb1 ⊢
    rw [hb1, ha1]
    omega
  · intro i hi
    obtain ⟨m, rfl⟩ : ∃ m, i = m + 2 := ⟨i - 2, by omega⟩
    have hadd := add2s_inv HA (m + 2)
    rw [hpar] at hadd
    rcases (by omega : m + 2 ≤ k * 2 + 2 ∨ m + 2 = k * 2 + 3 ∨
        k * 2 + 4 ≤ m + 2) with hc | hc | hc
    · have hv := ha (m + 2) (by omega) (by omega)
      rw [if_pos (by omega : m + 2 < k * 2 + 3)]
      rw [hv] at hadd
      have hpw : (2:ℕ) ≤ 2 ^ (k * 2 + 3 - (m + 2)) := by
        calc (2:ℕ) = 2 ^ 1 := by norm_num
        _ ≤ 2 ^ (k * 2 + 3 - (m + 2)) :=
          Nat.pow_le_pow_right (by omega) (by omega)
      split_ifs at hadd <;> omega
    · rw [if_neg (by omega)]
      rw [hc] at hadd ⊢
      rw [halast] at hadd
      split_ifs at hadd <;> omega
    · rw [if_neg (by omega)]
      have hv : ai' (m + 2) ne = 0 := by
        simp only [ai']
        exact ai_out_of_bound (by omega)
      rw [hv] at hadd
      split_ifs at hadd <;> omega

/-- Coq `last_step`: from the post-ZIHIO batch profile, one more batch lands
exactly on `Base (k+1)`. -/
lemma last_step {k : ℕ} {e ne : S17}
    (Heb : EmbankedBatch (k * 2 + 1) e ne
      (2 ^ (k * 2 + 2) - 1) (2 ^ (k * 2 + 2) - 2))
    (hl : toL ne = k * 2 + 3)
    (ha0 : ai' 0 ne = 1)
    (ha1 : ai' 1 ne = 2 ^ (k * 2 + 2) - 2)
    (ha : ∀ i, 2 ≤ i →
      ai' i ne = if i < k * 2 + 3 then 2 ^ (k * 2 + 3 - i) else 0) :
    ∃ b h_1 h_2, EmbankedBatch 1 ne b h_1 h_2 ∧ BaseS (k + 1) b := by
  have hp2 : (4:ℕ) ≤ 2 ^ (k * 2 + 2) := by
    calc (4:ℕ) = 2 ^ 2 := by norm_num
    _ ≤ 2 ^ (k * 2 + 2) := Nat.pow_le_pow_right (by omega) (by omega)
  have hp3 : (2:ℕ) ^ (k * 2 + 3) = 2 ^ (k * 2 + 2) + 2 ^ (k * 2 + 2) :=
    two_pow_succ' _
  obtain ⟨b, hb⟩ := embanked_batch_precond' Heb
    (by rw [hl, ha0]; omega)
    (by rw [hl, show k * 2 + 3 - 1 = k * 2 + 2 by omega, ha1]; omega)
  rw [show (k * 2 + 1) % 2 = 1 by omega] at hb
  have hctz : ctzS (2 ^ (k * 2 + 2) - 2) = 0 := by
    have h := ctzS_sub (i := k * 2 + 2) (m := 0) (by omega) (by omega)
    rw [show 2 ^ (k * 2 + 2) - 0 - 2 = 2 ^ (k * 2 + 2) - 2 by omega] at h
    rw [h]
    exact (ctzS_spec 0 0).2 (by norm_num)
  have hb1 : EmbankedBatch 1 ne b
      (2 ^ (k * 2 + 2) - 1) (2 ^ (k * 2 + 2) - 1) := by
    have h : EmbankedBatch (ctzS (2 ^ (k * 2 + 2) - 2) + 1) ne b
        (2 ^ (k * 2 + 2) - 1) (2 ^ (k * 2 + 2) - 2 + 1) := hb
    rw [hctz, show 2 ^ (k * 2 + 2) - 2 + 1 = 2 ^ (k * 2 + 2) - 1 by omega] at h
    exact h
  have HA := embanked_batch_Add2s hb1
  have hlen := embanked_batch_len hb1
  refine ⟨b, _, _, hb1, BaseS.intro _ ?_ ?_ ?_⟩
  · -- head counter
    have h0 := add2s_inv HA 0
    rw [if_neg (by omega)] at h0
    simp only [ai'] at h0 ha0
    omega
  · -- digit profile
    intro i
    have hi := add2s_inv HA (i + 1)
    match i with
    | 0 =>
        rw [if_pos (by omega)] at hi
        simp only [ai'] at hi ha1
        rw [if_pos (by omega : 0 < (k + 1) * 2),
          show (k + 1) * 2 - 0 = k * 2 + 2 by omega]
        omega
    | (m + 1) =>
        rw [if_neg (by omega)] at hi
        simp only [ai'] at hi
        have hv := ha (m + 2) (by omega)
        simp only [ai'] at hv
        by_cases hc : m + 2 < k * 2 + 3
        · rw [if_pos hc] at hv
          rw [if_pos (by omega : m + 1 < (k + 1) * 2),
            show (k + 1) * 2 - (m + 1) = k * 2 + 3 - (m + 2) by omega]
          omega
        · rw [if_neg hc] at hv
          rw [if_neg (by omega : ¬(m + 1 < (k + 1) * 2))]
          omega
  · rw [← hlen, hl]
    omega

end Deciders.Skelet.Skelet17
