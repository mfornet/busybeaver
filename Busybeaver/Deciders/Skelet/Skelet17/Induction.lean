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

end Deciders.Skelet.Skelet17
