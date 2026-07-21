import Busybeaver.Deciders.Skelet.Skelet1.UniverseReplay
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Cases

/-!
# Skelet #1 — universe-cycle acceleration

This module derives the reusable universe-cycle iterator and optimized symbolic
step from the single-period replay.  The expensive replay itself lives in
`Skelet1UniverseReplay`, so edits to this layer reuse its compiled proof.
-/

namespace Deciders.Skelet.Skelet1

open Turing TM.Table

/-- `liftL` is congruent under a fixed prefix. -/
lemma liftL_append_congr (p a b : Ltape) (hab : liftL a = liftL b) :
    liftL (p ++ a) = liftL (p ++ b) := by
  induction p with
  | nil => simpa using hab
  | cons hd t ih => cases hd <;> simp only [List.cons_append, liftL, ih]

/-- `lpow b 1 = b`. -/
lemma lpow_one (b : List (Symbol 1)) : lpow b 1 = b := by
  simp [lpow]

/-- One `F` block equals `Fls 1` on the lift. -/
lemma liftL_Fls_one_eq (l : Ltape) : liftL (F ++ l) = liftL (Fls 1 l) := by
  rw [liftL_Fls, lpow_one, F]
  simp only [List.cons_append, List.nil_append, liftL]
  rw [Fl]
  simp only [List.append_assoc, ListBlank.append_assoc']

/-- One `G` block equals `Grs 1` on the lift. -/
lemma liftR_Grs_one_eq (r : Rtape) : liftR (G ++ r) = liftR (Grs 1 r) := by
  rw [liftR_Grs, lpow_one, G]
  simp only [List.cons_append, List.nil_append, liftR]
  rw [Gr]
  simp only [List.append_assoc, ListBlank.append_assoc']

/-- Coq `uni_cycle'`: the `uni_cycle` result phrased with the smart constructors
`Fls`/`Grs`. -/
theorem uni_cycle' (l : Ltape) (r r' : Rtape) (xs : ℕ)
    (h : stride 0 uni_T r = some r') :
    lift (.right, Lsym.D :: Lsym.C1 :: Lsym.xs (xs + (uni_P + 1)) :: J ++ l, r) -[M]->*
      lift (.right, Lsym.D :: Lsym.C1 :: Lsym.xs (xs + 1) :: J ++ Fls 1 l, Grs 1 r') := by
  refine (uni_cycle l r r' xs h).trans ?_
  have hcfg :
      lift (.right, Lsym.D :: Lsym.C1 :: Lsym.xs (xs + 1) :: J ++ F ++ l, G ++ r')
        = lift (.right, Lsym.D :: Lsym.C1 :: Lsym.xs (xs + 1) :: J ++ Fls 1 l, Grs 1 r') := by
    simp only [lift]
    have hL : liftL (Lsym.D :: Lsym.C1 :: Lsym.xs (xs + 1) :: J ++ F ++ l)
        = liftL (Lsym.D :: Lsym.C1 :: Lsym.xs (xs + 1) :: J ++ Fls 1 l) := by
      have := liftL_append_congr (Lsym.D :: Lsym.C1 :: Lsym.xs (xs + 1) :: J)
        (F ++ l) (Fls 1 l) (liftL_Fls_one_eq l)
      simpa [List.append_assoc] using this
    have hR : liftR (G ++ r') = liftR (Grs 1 r') := liftR_Grs_one_eq r'
    rw [hL, hR]
  rw [hcfg]
  exact Machine.EvStep.refl

/-
Coq `uni_cycles`: iterate `uni_cycle'` `n+1` times.
-/
/- Increase recursion depth for Lean tactics used in proofs. -/
theorem uni_cycles (n xs : ℕ) (l : Ltape) (r r' : Rtape)
    (h : stride 0 ((n + 1) * uni_T) r = some r') :
    lift (.right, Lsym.D :: Lsym.C1 :: Lsym.xs (xs + ((n + 1) * uni_P + 1)) :: J ++ l, r) -[M]->*
      lift (.right, Lsym.D :: Lsym.C1 :: Lsym.xs (xs + 1) :: J ++ Fls (n + 1) l,
        Grs (n + 1) r') := by
  induction n generalizing xs l r r' with
  | zero =>
      simpa using uni_cycle' l r r' xs h
  | succ n ih =>
      obtain ⟨r₁, hr₁, hr'⟩ :=
        stride_add r r' 0 ((n + 1) * uni_T) uni_T (by
          convert h using 1; ring_nf)
      have first := ih (xs := xs + uni_P) (l := l) (r := r) (r' := r₁) hr₁
      have htail : stride 0 uni_T (Grs (n + 1) r₁) = some (Grs (n + 1) r') := by
        simpa only [rxs] using stride_Grs r₁ r' 0 (n + 1) uni_T hr'
      have last := uni_cycle' (Fls (n + 1) l) (Grs (n + 1) r₁)
        (Grs (n + 1) r') xs htail
      convert first.trans last using 1 <;>
        (try simp only [Fls_Fls, Grs_Grs]) <;> congr 4 <;> ring_nf

/-! ## The `uni_cycle_count` bound. -/

/-- Coq `uni_cycle_count`. -/
def uni_cycle_count (xs : ℕ) (r : Rtape) : ℕ :=
  let xs_limit := (xs - 1) / uni_P
  if xs_limit = 0 then 0
  else
    match max_stride 0 r with
    | some strides => min xs_limit (strides / uni_T)
    | none => xs_limit

/-
Coq `uni_cycle_count_spec` (in `ℕ`, valid when the count is positive).
-/
lemma uni_cycle_count_spec (xs : ℕ) (r : Rtape) (h : 0 < uni_cycle_count xs r) :
    uni_cycle_count xs r * uni_P < xs := by
  have hle : uni_cycle_count xs r ≤ (xs - 1) / uni_P := by
    simp only [uni_cycle_count]
    split
    · simp
    · split <;> simp
  have hmul : uni_cycle_count xs r * uni_P ≤ xs - 1 :=
    le_trans (Nat.mul_le_mul_right uni_P hle) (Nat.div_mul_le_self (xs - 1) uni_P)
  have hxs : 0 < xs := by
    by_contra hx
    have hx0 : xs = 0 := Nat.eq_zero_of_not_pos hx
    subst xs
    simp [uni_cycle_count] at h
  exact lt_of_le_of_lt hmul (Nat.sub_lt hxs Nat.zero_lt_one)

/-! ## `strip_prefix` and `try_uni_cycle`. -/

/-- A decidable prefix-strip on lists (Coq `strip_prefix'` with `eqb_l`). -/
def stripPrefix {α : Type*} [DecidableEq α] : List α → List α → Option (List α)
  | [], ys => some ys
  | _ :: _, [] => none
  | xh :: xt, yh :: yt => if xh = yh then stripPrefix xt yt else none

lemma stripPrefix_spec {α : Type*} [DecidableEq α] (xs ys zs : List α)
    (h : stripPrefix xs ys = some zs) : ys = xs ++ zs := by
  induction' xs with x xs ih generalizing ys zs;
  · cases ys <;> cases h <;> rfl;
  · rcases ys with ( _ | ⟨ y, ys ⟩ ) <;> simp_all +decide [ stripPrefix ];
    exact ih _ _ h.2

/-- Coq `try_uni_cycle`. -/
def try_uni_cycle : conf → Option conf
  | (.right, Lsym.D :: Lsym.C1 :: Lsym.xs xs :: l, r) =>
    match stripPrefix J l with
    | some l =>
      match uni_cycle_count xs r with
      | 0 => none
      | n + 1 =>
        match stride 0 ((n + 1) * uni_T) r with
        | some r' =>
          some (.right, Lsym.D :: Lsym.C1 :: Lsym.xs (xs - (n + 1) * uni_P) ::
            J ++ Fls (n + 1) l, Grs (n + 1) r')
        | none => none
    | none => none
  | _ => none

lemma try_uni_cycle_spec (c c' : conf) (h : try_uni_cycle c = some c') :
    lift c -[M]->* lift c' := by
  obtain ⟨l0, r⟩ : ∃ l0 r, c = (.right, l0, r) := by
    rcases c with ⟨ _ | _, _ | _, _ | _ ⟩ <;> tauto;
  rcases r with ⟨ r, rfl ⟩;
  obtain ⟨l, xs, hl⟩ : ∃ l xs, l0 = Lsym.D :: Lsym.C1 :: Lsym.xs xs :: l := by
    rcases l0 with ( _ | ⟨ a, _ | ⟨ b, _ | ⟨ c, _ | l0 ⟩ ⟩ ⟩ ) <;> simp_all +decide [ try_uni_cycle ]; all_goals cases a <;> cases b <;> cases c <;> tauto;
  obtain ⟨l', hl'⟩ : ∃ l', stripPrefix J l = some l' := by
    unfold try_uni_cycle at h; aesop;
  obtain ⟨n, hn⟩ : ∃ n, uni_cycle_count xs r = n + 1 := by
    unfold try_uni_cycle at h; aesop;
  obtain ⟨r', hr'⟩ : ∃ r', stride 0 ((n + 1) * uni_T) r = some r' := by
    unfold try_uni_cycle at h; aesop;
  obtain ⟨c'', hc''⟩ : c' = (.right, Lsym.D :: Lsym.C1 :: Lsym.xs (xs - (n + 1) * uni_P) :: J ++ Fls (n + 1) l', Grs (n + 1) r') := by
    unfold try_uni_cycle at h; aesop;
  obtain ⟨u, hu⟩ : ∃ u, xs = u + ((n + 1) * uni_P + 1) := by
    have := uni_cycle_count_spec xs r ( by linarith );
    exact ⟨ xs - ( ( n + 1 ) * uni_P + 1 ), by rw [ Nat.sub_add_cancel ( by nlinarith ) ] ⟩;
  convert uni_cycles n u l' r r' hr' using 1;
  · have := stripPrefix_spec J l l' hl'; aesop;
  · simp +decide [hu];
    simp +decide [Nat.add_sub_assoc]

/-- Coq `fullstep`. -/
def fullstep (c : conf) : Option conf :=
  match try_uni_cycle c with
  | some c' => some c'
  | none => step c

lemma fullstep_spec (c c' : conf) (h : fullstep c = some c') :
    lift c -[M]->* lift c' := by
  unfold fullstep at h;
  grind +suggestions

end Deciders.Skelet.Skelet1
