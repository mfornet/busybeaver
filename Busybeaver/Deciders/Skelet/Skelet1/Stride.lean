import Busybeaver.Deciders.Skelet.Skelet1.Sim
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Cases

/-!
# Skelet #1 — the "stride" acceleration

This file continues the Lean port of `Coq-BB5/BusyCoq/Skelet1.v`, developing the
`stride` acceleration rule on the right symbolic tape and its correctness
theorem `stride_correct`.
-/

namespace Deciders.Skelet.Skelet1

open Turing TM.Table

/-- `max_stride` (Coq `max_stride`): the maximum number of times the stride rule
can be applied.  Not used for correctness. -/
def max_stride (xs : ℕ) : Rtape → Option ℕ
  | [Rsym.P] => none
  | Rsym.P :: _ => some 0
  | [] => some 0
  | Rsym.xs xs' :: t => max_stride (xs + xs') t
  | Rsym.D :: t => max_stride 0 t
  | Rsym.Cr :: t =>
    match max_stride 0 t with
    | some n' => some (min xs (n' / 4))
    | none => some xs
  | Rsym.Gs _ :: t => max_stride 0 t

/-- `stride` (Coq `stride`): accelerated repeated application of the stride rule.
`n` plays the role of Coq's `positive` and should be thought of as `≥ 1`. -/
def stride (xs n : ℕ) : Rtape → Option Rtape
  | [Rsym.P] => some (rxs xs [Rsym.P])
  | Rsym.P :: _ => none
  | [] => none
  | Rsym.xs xs' :: t => stride (xs + xs') n t
  | Rsym.D :: t =>
    match stride 0 n t with
    | some t => some (rxs xs (Rsym.D :: t))
    | none => none
  | Rsym.Cr :: t =>
    if n ≤ xs then
      match stride 0 (4 * n) t with
      | some t => some (rxs (xs - n) (Rsym.Cr :: rxs (2 * n) t))
      | none => none
    else none
  | Rsym.Gs gs :: t =>
    match stride 0 n t with
    | some t => some (rxs xs (Grs gs t))
    | none => none

/-- A continuation-passing implementation of `stride`, corresponding to Coq's
`stride'`.  It is useful when partially evaluating a stride through an explicit
prefix whose suffix is still symbolic. -/
def strideK (xs n : ℕ) (t : Rtape) (k : Rtape → Rtape) : Option Rtape :=
  match t with
  | [Rsym.P] => some (k (rxs xs [Rsym.P]))
  | Rsym.P :: _ => none
  | [] => none
  | Rsym.xs xs' :: t => strideK (xs + xs') n t k
  | Rsym.D :: t => strideK 0 n t (fun t => k (rxs xs (Rsym.D :: t)))
  | Rsym.Cr :: t =>
    if n ≤ xs then
      strideK 0 (4 * n) t (fun t => k (rxs (xs - n) (Rsym.Cr :: rxs (2 * n) t)))
    else none
  | Rsym.Gs gs :: t => strideK 0 n t (fun t => k (rxs xs (Grs gs t)))
termination_by t.length

lemma strideK_spec (t : Rtape) (xs n : ℕ) (k : Rtape → Rtape) :
    strideK xs n t k = Option.map k (stride xs n t) := by
  induction t generalizing xs n k with
  | nil => simp [strideK, stride]
  | cons a t ih =>
    cases a with
    | xs m =>
        simp only [strideK, stride]
        exact ih (xs + m) n k
    | D =>
        simp only [strideK, stride]
        rw [ih]
        cases stride 0 n t <;> rfl
    | Cr =>
        simp only [strideK, stride]
        split <;> rename_i hn
        · rw [ih]
          cases stride 0 (4 * n) t <;> rfl
        · rfl
    | P => cases t <;> simp [strideK, stride]
    | Gs gs =>
        simp only [strideK, stride]
        rw [ih]
        cases stride 0 n t <;> rfl

/-- `stride_level` (Coq `stride_level`): the number of `r_C` symbols. -/
def stride_level : Rtape → ℕ
  | [] => 0
  | Rsym.Cr :: t => stride_level t + 1
  | _ :: t => stride_level t

/-! ## Algebraic lemmas about the smart constructors. -/

lemma rxs_rxs (n m : ℕ) (t : Rtape) : rxs n (rxs m t) = rxs (n + m) t := by
  induction' n with n ih generalizing t;
  · cases t <;> aesop;
  · cases t <;> simp_all +arith +decide [ rxs ];
    · cases m <;> simp +arith +decide [ Nat.add_comm ];
    · cases m <;> cases ‹Rsym› <;> simp +arith +decide [ * ]

lemma Fls_Fls (n m : ℕ) (t : Ltape) : Fls n (Fls m t) = Fls (n + m) t := by
  induction' n with n ih generalizing m t;
  · aesop;
  · cases t <;> simp_all +arith +decide [ Fls ];
    · cases m <;> simp +arith +decide;
    · cases m <;> cases ‹Lsym› <;> simp +arith +decide [ * ]

lemma Grs_Grs (n m : ℕ) (t : Rtape) : Grs n (Grs m t) = Grs (n + m) t := by
  induction' n with n ih generalizing m t;
  · cases m <;> aesop;
  · cases t <;> simp_all +arith +decide [ Grs ];
    · cases m <;> simp +arith +decide;
    · cases m <;> cases ‹Rsym› <;> simp +arith +decide [ * ]

lemma stride_rxs (t : Rtape) (xs xs' n : ℕ) :
    stride xs n (rxs xs' t) = stride (xs + xs') n t := by
      induction' xs' with xs' xs' ih generalizing xs n t;
      · cases t <;> rfl;
      · cases t <;> simp_all +decide [ rxs ];
        · exact (Option.map_inj_right fun x y a => a).mp rfl;
        · cases ‹Rsym› <;> simp +decide [ stride ];
          ac_rfl

/-! ## Structural lemmas about `stride`. -/

lemma stride_more (t t' : Rtape) (xs xs' n : ℕ) (h : stride xs' n t = some t') :
    stride (xs + xs') n t = some (rxs xs t') := by
      -- By definition of stride, we can split into cases based on the structure of the Rtape.
      induction' t with t ih generalizing xs xs' n;
      · cases h;
      · cases t;
        · unfold stride at h ⊢; simp_all +decide [ Nat.add_assoc ] ;
        · cases h' : stride 0 n ih <;> simp_all +decide [ stride ];
          subst h;
          expose_names; exact Eq.symm (rxs_rxs xs xs' (Rsym.D :: val));
        · simp +decide [ stride ] at h ⊢;
          cases h' : stride 0 ( 4 * n ) ih <;> simp_all +decide [ Nat.add_sub_assoc ];
          grind +suggestions;
        · cases ih <;> simp_all +decide [ stride ];
          subst h;
          exact Eq.symm (rxs_rxs xs xs' [Rsym.P]);
        · cases h' : stride 0 n ih <;> simp_all +decide [ stride ];
          rw [ ← h, rxs_rxs ]

lemma stride_Grs (t t' : Rtape) (xs gs n : ℕ) (h : stride 0 n t = some t') :
    stride xs n (Grs gs t) = some (rxs xs (Grs gs t')) := by
      induction' gs with gs gs_ih generalizing t t' xs;
      · simpa [Grs] using (stride_more t t' xs 0 n h);
      · rcases t with ( _ | ⟨ hd, t ⟩ );
        · cases h;
        · rcases hd with ( _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | hd );
          all_goals rw [ Grs ];
          all_goals simp_all +decide [ stride ];
          all_goals rcases h' : stride 0 n t with ( _ | t'' ) <;> simp +decide [ h' ] at h ⊢;
          all_goals rw [ ← h ];
          exact List.toList_toArray;
          all_goals rw [ ← Grs_Grs ];
          all_goals rfl;

lemma stride_add (t t2 : Rtape) (xs n m : ℕ) (h : stride xs (n + m) t = some t2) :
    ∃ t1, stride xs n t = some t1 ∧ stride 0 m t1 = some t2 := by
      induction' t with t ih generalizing xs n m t2;
      · cases h;
      · cases t;
        · simp_all +arith +decide [ stride ];
        · cases h' : stride 0 ( n + m ) ih <;> simp_all +decide [ stride ];
          rename_i k;
          obtain ⟨ t1, ht1 ⟩ := ‹∀ ( t2 : Rtape ) ( xs n m : ℕ ), stride xs ( n + m ) ih = some t2 → ∃ t1, stride xs n ih = some t1 ∧ stride 0 m t1 = some t2› k 0 n m h';
          simp_all +decide;
          rw [ stride_rxs ];
          rw [ stride ] ; aesop;
        · by_cases h₁ : n + m ≤ xs <;> simp +decide [ h₁, stride ] at h ⊢;
          obtain ⟨t1, ht1⟩ : ∃ t1, stride 0 (4 * n) ih = some t1 ∧ stride 0 (4 * m) t1 = some (match stride 0 (4 * (n + m)) ih with | some t => t | none => []) := by
            rename_i h₂;
            specialize h₂ (match stride 0 (4 * (n + m)) ih with | some t => t | none => []) 0 (4 * n) (4 * m);
            exact h₂ ( by rw [ show 4 * n + 4 * m = 4 * ( n + m ) by ring ] ; cases h : stride 0 ( 4 * ( n + m ) ) ih <;> simp +decide [ h ] at * );
          use rxs (xs - n) (Rsym.Cr :: rxs (2 * n) t1);
          rw [ stride_rxs ];
          rw [ stride ];
          rw [ stride_rxs ];
          rw [ stride_more ];
          any_goals exact rxs ( 2 * n ) ( match stride 0 ( 4 * ( n + m ) ) ih with | some t => t | none => [] );
          · rw [ ht1.1 ];
            rw [ show xs - n = xs - ( n + m ) + m by omega ] ; simp +decide [ rxs_rxs ] ;
            exact ⟨ by linarith, by rw [ show 2 * m + 2 * n = 2 * ( n + m ) by ring ] ; cases h' : stride 0 ( 4 * ( n + m ) ) ih <;> aesop ⟩;
          · exact stride_more _ _ _ _ _ ht1.2;
        · cases ih <;> simp_all +decide [ stride ];
          rcases xs with ( _ | xs ) <;> simp_all +decide [ rxs ];
          · subst h; exact Option.mem_def.mp rfl;
          · subst h; simp +decide [ stride ] ;
            rfl;
        · rename_i k hk;
          obtain ⟨t1, ht1⟩ : ∃ t1, stride 0 (n + m) ih = some t1 ∧ t2 = rxs xs (Grs hk t1) := by
            rw [ stride ] at h;
            cases h' : stride 0 ( n + m ) ih <;> aesop;
          obtain ⟨t1', ht1'⟩ := k t1 0 n m ht1.left;
          use rxs xs (Grs hk t1');
          simp_all +decide [ stride_Grs, stride_rxs ];
          rw [ stride ] ; aesop

/-- Split a known long stride while exposing the first part through `strideK`.
This is the key bookkeeping operation used by the universe-cycle evaluator. -/
lemma prepare_strideK (t t' : Rtape) (xs n₁ n₂ : ℕ)
    (h : stride 0 (n₁ + n₂) t = some t') :
    ∃ t₁, (∀ k : Rtape → Rtape,
      strideK xs n₁ t k = some (k (rxs xs t₁))) ∧
      stride 0 n₂ t₁ = some t' := by
  obtain ⟨t₁, h₁, h₂⟩ := stride_add t t' 0 n₁ n₂ h
  refine ⟨t₁, ?_, h₂⟩
  intro k
  rw [strideK_spec]
  have hm := stride_more t t₁ xs 0 n₁ h₁
  simp only [Nat.add_zero] at hm
  rw [hm]
  rfl

lemma stride_level_rxs (xs : ℕ) (t : Rtape) :
    stride_level (rxs xs t) = stride_level t := by
      induction' xs with xs ih generalizing t;
      · cases t <;> rfl;
      · cases t <;> simp_all +decide [ rxs ];
        · rfl;
        · cases ‹Rsym› <;> simp +decide [ stride_level ]

lemma stride_level_Grs (xs : ℕ) (t : Rtape) :
    stride_level (Grs xs t) = stride_level t := by
      induction' xs with xs ih generalizing t;
      · rfl;
      · cases t <;> simp +arith +decide [ Grs ];
        · rfl;
        · rename_i h t;
          cases h <;> simp +arith +decide [ stride_level ]

lemma stride_same_level (t t' : Rtape) (xs n : ℕ) (h : stride xs n t = some t') :
    stride_level t = stride_level t' := by
      induction' t with t ih generalizing xs n t';
      · cases h;
      · cases t;
        · expose_names; exact Nat.add_right_cancel (congrFun (congrArg HAdd.hAdd (tail_ih t' (xs + n_1) n h)) xs);
        · cases h' : stride 0 n ih <;> simp_all +decide [ stride ];
          subst h;
          rename_i k hk;
          exact k _ _ _ h' ▸ by cases xs <;> rfl;
        · unfold stride at h;
          cases h' : stride 0 ( 4 * n ) ih <;> simp_all +decide;
          rw [ ← h.2, stride_level_rxs ];
          rw [ stride_level, stride_level, ‹∀ ( t' : Rtape ) ( xs n : ℕ ), stride xs n ih = some t' → stride_level ih = stride_level t'› _ _ _ h' ];
          rw [ stride_level_rxs ];
        · cases ih <;> simp_all +decide [ stride ];
          cases xs <;> aesop;
        · rename_i k hk;
          obtain ⟨t'', ht''⟩ : ∃ t'', stride 0 n ih = some t'' ∧ t' = rxs xs (Grs hk t'') := by
            rw [ stride ] at h;
            cases h' : stride 0 n ih <;> aesop;
          simp_all +decide [ stride_level_Grs, stride_level_rxs ];
          exact k _ _ _ ht''.1

/-! ## Correctness of `stride`. -/

/-- The tape-level induction hypothesis used by the head-case lemmas: `stride`
correctness holds for the tail tape `t`. -/
abbrev StrideIH (t : Rtape) : Prop :=
  ∀ (t' : Rtape) (xs : ℕ) (l : LB), stride xs 1 t = some t' →
    AR (lpow x xs ++ l) (liftR t) -[M]->* CL l (liftR t')

/-
Head case `Rsym.xs xs' :: t` (Coq `case_xs`).
-/
lemma stride_correct_xs (t : Rtape) (xs' : ℕ) (IHt : StrideIH t)
    (t' : Rtape) (xs : ℕ) (l : LB) (H : stride xs 1 (Rsym.xs xs' :: t) = some t') :
    AR (lpow x xs ++ l) (liftR (Rsym.xs xs' :: t)) -[M]->* CL l (liftR t') := by
  simp only [stride] at H
  have htail := IHt t' (xs + xs') l H
  have htail' :
      AR (lpow x xs' ++ (lpow x xs ++ l)) (liftR t) -[M]->*
        CL l (liftR t') := by
    convert htail using 1
    rw [← ListBlank.append_assoc', ← lpow_add, Nat.add_comm]
  exact (rule_xn_right xs' (lpow x xs ++ l) (liftR t)).trans htail'

/-
Head case `Rsym.D :: t` (Coq `case_D`).
-/
lemma stride_correct_D (t : Rtape) (IHt : StrideIH t)
    (t' : Rtape) (xs : ℕ) (l : LB) (H : stride xs 1 (Rsym.D :: t) = some t') :
    AR (lpow x xs ++ l) (liftR (Rsym.D :: t)) -[M]->* CL l (liftR t') := by
      obtain ⟨t1, ht1⟩ : ∃ t1, stride 0 1 t = some t1 ∧ t' = rxs xs (Rsym.D :: t1) := by
        rw [ stride ] at H;
        cases h : stride 0 1 t <;> aesop;
      have := IHt t1 0 ( Dl ++ ( lpow x xs ++ l ) ) ht1.1;
      convert rule_D_right ( lpow x xs ++ l ) ( liftR t ) |> Machine.EvStep.trans <| this |> Machine.EvStep.trans <| rule_D_left ( lpow x xs ++ l ) ( liftR t1 ) |> Machine.EvStep.trans <| rule_xn_left xs l ( Dr ++ liftR t1 ) using 1;
      · simp [liftR]
      · rw [ ht1.2, liftR_rxs ]
        simp [liftR]

/-
Head case `Rsym.Gs gs :: t` (Coq `case_Gs`).
-/
lemma stride_correct_Gs (t : Rtape) (gs : ℕ) (IHt : StrideIH t)
    (t' : Rtape) (xs : ℕ) (l : LB) (H : stride xs 1 (Rsym.Gs gs :: t) = some t') :
    AR (lpow x xs ++ l) (liftR (Rsym.Gs gs :: t)) -[M]->* CL l (liftR t') := by
      obtain ⟨t1, ht1⟩ : ∃ t1, stride 0 1 t = some t1 ∧ t' = rxs xs (Grs gs t1) := by
        rw [ stride ] at H;
        cases h : stride 0 1 t <;> aesop;
      have := IHt t1 0 ( lpow Gl gs ++ ( lpow x xs ++ l ) ) ht1.1;
      convert rule_Gn_right gs ( lpow x xs ++ l ) ( liftR t ) |> Machine.EvStep.trans <| this |> Machine.EvStep.trans <| rule_Gn_left gs ( lpow x xs ++ l ) ( liftR t1 ) |> Machine.EvStep.trans <| rule_xn_left xs l ( lpow Gr gs ++ liftR t1 ) using 1;
      · rfl
      · rw [ ht1.2, liftR_rxs ]
        rw [liftR_Grs]

/-
Head case `Rsym.P :: t` (Coq `case_P`); no tape-IH needed.
-/
lemma stride_correct_P (t : Rtape)
    (t' : Rtape) (xs : ℕ) (l : LB) (H : stride xs 1 (Rsym.P :: t) = some t') :
    AR (lpow x xs ++ l) (liftR (Rsym.P :: t)) -[M]->* CL l (liftR t') := by
      cases t <;> cases H;
      convert rule_P_R ( lpow x xs ++ l ) |> Machine.EvStep.trans <| rule_xn_left xs l ( P ++ RB ) using 1;
      · simp [liftR]
      · rw [liftR_rxs]; simp [liftR]

/-
Head case `Rsym.Cr :: t` (Coq's `r_C` case).  Requires the level-IH `IHk`
applicable to the tail (and its sub-strides at the same level).
-/
lemma stride_correct_Cr (k : ℕ) (t : Rtape) (hk : stride_level t = k)
    (IHk : ∀ (t t' : Rtape) (xs : ℕ) (l : LB), stride_level t = k →
      stride xs 1 t = some t' → AR (lpow x xs ++ l) (liftR t) -[M]->* CL l (liftR t'))
    (t' : Rtape) (xs : ℕ) (l : LB) (H : stride xs 1 (Rsym.Cr :: t) = some t') :
    AR (lpow x xs ++ l) (liftR (Rsym.Cr :: t)) -[M]->* CL l (liftR t') := by
  simp only [stride] at H
  split at H
  · rename_i hxs
    cases hfin : stride 0 (4 * 1) t with
    | none => simp [hfin] at H
    | some tfin =>
      simp [hfin] at H
      subst t'
      obtain ⟨u, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : xs ≠ 0)
      obtain ⟨t₁, ht₁, hrest₁⟩ :=
        stride_add t tfin 0 1 3 (by simpa using hfin)
      obtain ⟨t₂, ht₂, hrest₂⟩ :=
        stride_add t₁ tfin 0 1 2 (by simpa using hrest₁)
      obtain ⟨t₃, ht₃, ht₄⟩ :=
        stride_add t₂ tfin 0 1 1 (by simpa using hrest₂)
      have hlevel₁ : stride_level t₁ = k := by
        rw [← hk]
        exact (stride_same_level t t₁ 0 1 ht₁).symm
      have hlevel₂ : stride_level t₂ = k := by
        rw [← hlevel₁]
        exact (stride_same_level t₁ t₂ 0 1 ht₂).symm
      have hlevel₃ : stride_level t₃ = k := by
        rw [← hlevel₂]
        exact (stride_same_level t₂ t₃ 0 1 ht₃).symm
      have e₁ := IHk t t₁ 0 (C0 ++ (lpow x u ++ l)) hk ht₁
      have e₂ := IHk t₁ t₂ 0 (x ++ C1 ++ (lpow x u ++ l)) hlevel₁ ht₂
      have e₃ := IHk t₂ t₃ 0 (x ++ C2 ++ (lpow x u ++ l)) hlevel₂ ht₃
      have e₄ := IHk t₃ tfin 0 (x ++ x ++ C ++ (lpow x u ++ l)) hlevel₃ ht₄
      have steps :=
        (rule_C30 (lpow x u ++ l) (liftR t)).trans e₁ |>.trans
        (rule_C01 (lpow x u ++ l) (liftR t₁)) |>.trans e₂ |>.trans
        (rule_x_left (C1 ++ (lpow x u ++ l)) (liftR t₂)) |>.trans
        (rule_C12 (lpow x u ++ l) (x ++ liftR t₂)) |>.trans
        (rule_x_right (C2 ++ (lpow x u ++ l)) (liftR t₂)) |>.trans e₃ |>.trans
        (rule_x_left (C2 ++ (lpow x u ++ l)) (liftR t₃)) |>.trans
        (rule_C23 (lpow x u ++ l) (x ++ liftR t₃)) |>.trans
        (rule_x_right (x ++ C ++ (lpow x u ++ l)) (liftR t₃)) |>.trans e₄ |>.trans
        (rule_x_left (x ++ C ++ (lpow x u ++ l)) (liftR tfin)) |>.trans
        (rule_x_left (C ++ (lpow x u ++ l)) (x ++ liftR tfin)) |>.trans
        (rule_C_left (lpow x u ++ l) (x ++ x ++ liftR tfin)) |>.trans
        (rule_xn_left u l (C ++ x ++ x ++ liftR tfin))
      convert steps using 1
      · simp [liftR, lpow_succ, ListBlank.append_assoc']
      · simp only [Nat.succ_sub_one]
        simp [liftR, lpow, ListBlank.append_assoc', liftR_rxs]
  · simp at H

/-- Auxiliary form of `stride_correct` with the level as an explicit induction
parameter (Coq `stride_correct'`). -/
theorem stride_correct' (k : ℕ) (t t' : Rtape) (xs : ℕ) (l : LB)
    (hk : stride_level t = k) (h : stride xs 1 t = some t') :
    AR (lpow x xs ++ l) (liftR t) -[M]->* CL l (liftR t') := by
  induction k generalizing t t' xs l with
  | zero =>
    induction t generalizing t' xs l with
    | nil => simp [stride] at h
    | cons hd t iht =>
      cases hd with
      | xs xs' =>
        have hk' : stride_level t = 0 := by simpa [stride_level] using hk
        exact stride_correct_xs t xs' (fun a b c hh => iht a b c hk' hh) t' xs l h
      | D =>
        have hk' : stride_level t = 0 := by simpa [stride_level] using hk
        exact stride_correct_D t (fun a b c hh => iht a b c hk' hh) t' xs l h
      | Cr => simp [stride_level] at hk
      | P => exact stride_correct_P t t' xs l h
      | Gs gs =>
        have hk' : stride_level t = 0 := by simpa [stride_level] using hk
        exact stride_correct_Gs t gs (fun a b c hh => iht a b c hk' hh) t' xs l h
  | succ k IHk =>
    induction t generalizing t' xs l with
    | nil => simp [stride] at h
    | cons hd t iht =>
      cases hd with
      | xs xs' =>
        have hk' : stride_level t = k + 1 := by simpa [stride_level] using hk
        exact stride_correct_xs t xs' (fun a b c hh => iht a b c hk' hh) t' xs l h
      | D =>
        have hk' : stride_level t = k + 1 := by simpa [stride_level] using hk
        exact stride_correct_D t (fun a b c hh => iht a b c hk' hh) t' xs l h
      | Cr =>
        have hk' : stride_level t = k := by simpa [stride_level] using hk
        exact stride_correct_Cr k t hk' IHk t' xs l h
      | P => exact stride_correct_P t t' xs l h
      | Gs gs =>
        have hk' : stride_level t = k + 1 := by simpa [stride_level] using hk
        exact stride_correct_Gs t gs (fun a b c hh => iht a b c hk' hh) t' xs l h

/-- Correctness of the stride rule (Coq `stride_correct`). -/
theorem stride_correct (t t' : Rtape) (xs : ℕ) (l : LB)
    (h : stride xs 1 t = some t') :
    AR (lpow x xs ++ l) (liftR t) -[M]->* CL l (liftR t') :=
  stride_correct' _ t t' xs l rfl h

/-- The `xs = 0` specialisation (Coq `stride_correct_0`). -/
theorem stride_correct_0 (t t' : Rtape) (l : LB)
    (h : stride 0 1 t = some t') :
    AR l (liftR t) -[M]->* CL l (liftR t') := by
  have := stride_correct t t' 0 l h
  simpa using this

/-! ## The `step` wrapper: one stride, otherwise one `simple_step`. -/

/-- A symbolic configuration (Coq `conf`). -/
abbrev conf := Turing.Dir × Ltape × Rtape

/-- `try_stride` (Coq `try_stride`): if facing right, try one stride on the right
tape. -/
def try_stride : conf → Option conf
  | (.left, _, _) => none
  | (.right, l, r) =>
    match stride 0 1 r with
    | some r' => some (.left, l, r')
    | none => none

/-- `step` (Coq `step`): a stride if possible, else a single `simple_step`. -/
def step (c : conf) : Option conf :=
  match try_stride c with
  | some c' => some c'
  | none => simple_step c

/-- Soundness of `try_stride` (Coq `try_stride_spec`). -/
lemma try_stride_spec (c c' : conf) (h : try_stride c = some c') :
    lift c -[M]->* lift c' := by
  obtain ⟨d, l, r⟩ := c
  cases d with
  | left => simp [try_stride] at h
  | right =>
    simp only [try_stride] at h
    cases hs : stride 0 1 r with
    | none => rw [hs] at h; simp at h
    | some r' =>
      rw [hs] at h
      simp only [Option.some.injEq] at h
      subst h
      exact stride_correct_0 r r' (liftL l) hs

/-- Soundness of `step` (Coq `step_spec`). -/
lemma step_spec (c c' : conf) (h : step c = some c') :
    lift c -[M]->* lift c' := by
  simp only [step] at h
  cases hs : try_stride c with
  | some c1 =>
    rw [hs] at h
    simp only [Option.some.injEq] at h
    subst h
    exact try_stride_spec c c1 hs
  | none =>
    rw [hs] at h
    exact simple_step_spec c c' h

end Deciders.Skelet.Skelet1
