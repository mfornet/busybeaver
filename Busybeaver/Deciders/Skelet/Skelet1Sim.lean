import Busybeaver.Deciders.Skelet.Skelet1
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Cases

/-!
# Skelet #1 — accelerated symbolic simulator

This file continues the Lean port of `Coq-BB5/BusyCoq/Skelet1.v`.  It sits on top
of the block-rule library in `Skelet1.lean` and develops the *symbolic tape*
(`Lsym`/`Rsym`), the lift back to concrete configurations (`lift`), and the
single accelerated step `simple_step` together with its soundness
(`simple_step_spec`).

Where the Coq development uses `positive`/`N` to guarantee that block-repeat
counts are `≥ 1`, we use `ℕ`.  The step function only ever *produces* strictly
positive counts (either literals, `n + 1`, or via the merging smart-constructors
`lxs`/`rxs`/…​ which drop a `0`), so canonical symbolic tapes never contain a
zero-count symbol.  For the few rules that decrement the matched head count we
match on `n + 1`, returning `none` on a (never-occurring) `0`; this keeps
`simple_step_spec` unconditionally true.
-/

namespace Deciders.Skelet.Skelet1

open Turing TM.Table

/-- Symbolic left-tape alphabet (Coq `lsym`). -/
inductive Lsym
  | xs (n : ℕ)
  | D | P
  | C0 | C1 | C2 | C3
  | F0 | F1 | F2 | F3
  | G0 | G1 | G2
  | Fs (n : ℕ) | Gs (n : ℕ) | Hs (n : ℕ)
deriving DecidableEq, Repr

/-- Symbolic right-tape alphabet (Coq `rsym`).  `Cr` is Coq's `r_C`. -/
inductive Rsym
  | xs (n : ℕ)
  | D | Cr | P
  | Gs (n : ℕ)
deriving DecidableEq, Repr

abbrev Ltape := List Lsym
abbrev Rtape := List Rsym

/-! ## Lift from symbolic tapes back to concrete `LB` tapes. -/

/-- `lpow b (n + m) = lpow b n ++ lpow b m`. -/
lemma lpow_add (b : List (Symbol 1)) (n m : ℕ) :
    lpow b (n + m) = lpow b n ++ lpow b m := by
  induction n with
  | zero => simp
  | succ n ih => rw [Nat.succ_add, lpow_succ, lpow_succ, ih, List.append_assoc]

/-- Lift of a symbolic left tape (head-nearest block at the front). -/
def liftL : Ltape → LB
  | [] => (∅ : LB)
  | Lsym.xs n :: t => lpow x n ++ liftL t
  | Lsym.D :: t => Dl ++ liftL t
  | Lsym.P :: t => P ++ liftL t
  | Lsym.C0 :: t => C0 ++ liftL t
  | Lsym.C1 :: t => C1 ++ liftL t
  | Lsym.C2 :: t => C2 ++ liftL t
  | Lsym.C3 :: t => C3 ++ liftL t
  | Lsym.F0 :: t => F0 ++ liftL t
  | Lsym.F1 :: t => F1 ++ liftL t
  | Lsym.F2 :: t => F2 ++ liftL t
  | Lsym.F3 :: t => F3 ++ liftL t
  | Lsym.G0 :: t => G0 ++ liftL t
  | Lsym.G1 :: t => G1 ++ liftL t
  | Lsym.G2 :: t => G2 ++ liftL t
  | Lsym.Fs n :: t => lpow Fl n ++ liftL t
  | Lsym.Gs n :: t => lpow Gl n ++ liftL t
  | Lsym.Hs n :: t => lpow Hl n ++ liftL t

/-- Lift of a symbolic right tape (head-nearest block at the front). -/
def liftR : Rtape → LB
  | [] => (∅ : LB)
  | Rsym.xs n :: t => lpow x n ++ liftR t
  | Rsym.D :: t => Dr ++ liftR t
  | Rsym.Cr :: t => C ++ liftR t
  | Rsym.P :: t => P ++ liftR t
  | Rsym.Gs n :: t => lpow Gr n ++ liftR t

/-- Lift a symbolic configuration (`right` = head faces right = `AR`,
`left` = `CL`). -/
def lift : Turing.Dir × Ltape × Rtape → Config 4 1
  | (.right, l, r) => AR (liftL l) (liftR r)
  | (.left, l, r) => CL (liftL l) (liftR r)

/-! ## Merging smart constructors (Coq `lxs`,`rxs`,`Fls`,`Gls`,`Grs`,`Hls`). -/

def lxs (n : ℕ) (l : Ltape) : Ltape :=
  match n with
  | 0 => l
  | n + 1 => match l with
    | Lsym.xs m :: l => Lsym.xs ((n + 1) + m) :: l
    | l => Lsym.xs (n + 1) :: l

def rxs (n : ℕ) (r : Rtape) : Rtape :=
  match n with
  | 0 => r
  | n + 1 => match r with
    | Rsym.xs m :: r => Rsym.xs ((n + 1) + m) :: r
    | r => Rsym.xs (n + 1) :: r

def Fls (n : ℕ) (l : Ltape) : Ltape :=
  match n with
  | 0 => l
  | n + 1 => match l with
    | Lsym.Fs m :: l => Lsym.Fs ((n + 1) + m) :: l
    | l => Lsym.Fs (n + 1) :: l

def Gls (n : ℕ) (l : Ltape) : Ltape :=
  match n with
  | 0 => l
  | n + 1 => match l with
    | Lsym.Gs m :: l => Lsym.Gs ((n + 1) + m) :: l
    | l => Lsym.Gs (n + 1) :: l

def Grs (n : ℕ) (r : Rtape) : Rtape :=
  match n with
  | 0 => r
  | n + 1 => match r with
    | Rsym.Gs m :: r => Rsym.Gs ((n + 1) + m) :: r
    | r => Rsym.Gs (n + 1) :: r

def Hls (n : ℕ) (l : Ltape) : Ltape :=
  match n with
  | 0 => l
  | n + 1 => match l with
    | Lsym.Hs m :: l => Lsym.Hs ((n + 1) + m) :: l
    | l => Lsym.Hs (n + 1) :: l

/-! ## Lift lemmas for the smart constructors. -/

lemma liftL_lxs (n : ℕ) (l : Ltape) : liftL (lxs n l) = lpow x n ++ liftL l := by
  cases n with
  | zero => simp [lxs]
  | succ k =>
    cases l with
    | nil => rfl
    | cons a l => cases a <;>
        simp only [lxs, liftL, lpow_add, List.append_assoc, ListBlank.append_assoc']

lemma liftR_rxs (n : ℕ) (r : Rtape) : liftR (rxs n r) = lpow x n ++ liftR r := by
  cases n with
  | zero => simp [rxs]
  | succ k =>
    cases r with
    | nil => rfl
    | cons a r => cases a <;>
        simp only [rxs, liftR, lpow_add, List.append_assoc, ListBlank.append_assoc']

lemma liftL_Fls (n : ℕ) (l : Ltape) : liftL (Fls n l) = lpow Fl n ++ liftL l := by
  cases n with
  | zero => simp [Fls]
  | succ k =>
    cases l with
    | nil => rfl
    | cons a l => cases a <;>
        simp only [Fls, liftL, lpow_add, List.append_assoc, ListBlank.append_assoc']

lemma liftL_Gls (n : ℕ) (l : Ltape) : liftL (Gls n l) = lpow Gl n ++ liftL l := by
  cases n with
  | zero => simp [Gls]
  | succ k =>
    cases l with
    | nil => rfl
    | cons a l => cases a <;>
        simp only [Gls, liftL, lpow_add, List.append_assoc, ListBlank.append_assoc']

lemma liftR_Grs (n : ℕ) (r : Rtape) : liftR (Grs n r) = lpow Gr n ++ liftR r := by
  cases n with
  | zero => simp [Grs]
  | succ k =>
    cases r with
    | nil => rfl
    | cons a r => cases a <;>
        simp only [Grs, liftR, lpow_add, List.append_assoc, ListBlank.append_assoc']

lemma liftL_Hls (n : ℕ) (l : Ltape) : liftL (Hls n l) = lpow Hl n ++ liftL l := by
  cases n with
  | zero => simp [Hls]
  | succ k =>
    cases l with
    | nil => rfl
    | cons a l => cases a <;>
        simp only [Hls, liftL, lpow_add, List.append_assoc, ListBlank.append_assoc']

/-! ## `unrxs`: peel one leading `x` off a right tape (Coq `unrxs`). -/

/-- Coq `unrxs`.  On `r_xs (n+1)` peel one `x`; on `r_Gs (n+1)` expand one `Gr`
block into `x^299 Dr x^30826 Dr x^72142 Dr x^3076 Dr x^1538 Dr` and peel the
leading `x`.  Returns `none` on a zero count (never occurs canonically). -/
def unrxs (r : Rtape) : Option Rtape :=
  match r with
  | Rsym.xs (n + 1) :: r => some (rxs n r)
  | Rsym.Gs (n + 1) :: r =>
      some (Rsym.xs 299 :: Rsym.D :: Rsym.xs 30826 :: Rsym.D :: Rsym.xs 72142 :: Rsym.D ::
            Rsym.xs 3076 :: Rsym.D :: Rsym.xs 1538 :: Rsym.D :: Grs n r)
  | _ => none

/-
Soundness of `unrxs`: peeling produces a tape whose lift, prefixed by one
`x` block, recovers the original lift.
-/
lemma unrxs_spec (r r' : Rtape) (h : unrxs r = some r') :
    liftR r = x ++ liftR r' := by
  cases r;
  · cases h;
  · rename_i a r;
    cases a <;> simp_all +decide [ unrxs ];
    · rename_i n;
      rcases n with ( _ | n ) <;> simp_all +decide;
      rw [ ← h, liftR_rxs ];
      simp only [liftR, lpow_succ, ListBlank.append_assoc']
    · cases ‹ℕ› <;> cases h;
      simp +decide [ liftR, Gr, liftR_Grs ];
      rw [ lpow_succ ];
      rw [ lpow_succ ];
      simp +decide [ List.append_assoc, ListBlank.append_assoc' ]

/-! ## The accelerated single step `simple_step` and its soundness. -/

/-- Coq `simple_step`.  One accelerated macro-step on symbolic configurations.
Counts that get decremented are matched as `n + 1` (so a spurious `0` count
yields `none`, keeping `simple_step_spec` unconditional). -/
def simple_step : Turing.Dir × Ltape × Rtape → Option (Turing.Dir × Ltape × Rtape)
  | (.right, l, r) =>
    match r with
    | [] =>
      match l with
      | Lsym.xs (n + 1) :: l => some (.left, lxs n l, [Rsym.Cr, Rsym.xs 1, Rsym.P])
      | Lsym.D :: l => some (.left, l, [Rsym.xs 1])
      | _ => none
    | Rsym.xs n :: r => some (.right, lxs n l, r)
    | Rsym.D :: r => some (.right, Lsym.D :: l, r)
    | Rsym.Cr :: r =>
      match l with
      | Lsym.xs (n + 1) :: l => some (.right, Lsym.C0 :: lxs n l, r)
      | Lsym.D :: l => some (.right, Lsym.xs 1 :: Lsym.P :: l, r)
      | Lsym.C0 :: l => some (.right, Lsym.G0 :: l, r)
      | Lsym.C2 :: l => some (.right, Lsym.F0 :: l, r)
      | _ => none
    | [Rsym.P] => some (.left, l, [Rsym.P])
    | Rsym.P :: Rsym.xs n :: r => some (.right, lxs n l, Rsym.P :: r)
    | Rsym.P :: Rsym.D :: Rsym.xs (n + 1) :: r =>
        some (.right, Lsym.D :: Lsym.C1 :: l, Rsym.P :: rxs n r)
    | Rsym.P :: Rsym.D :: Rsym.D :: r =>
      match unrxs r with
      | some r => some (.right, Lsym.D :: Lsym.C1 :: Lsym.C2 :: l, r)
      | none => none
    | Rsym.P :: Rsym.D :: Rsym.Cr :: r =>
      match unrxs r with
      | some r => some (.right, Lsym.D :: Lsym.G1 :: l, Rsym.P :: r)
      | none => none
    | Rsym.P :: Rsym.D :: Rsym.P :: r => some (.right, Lsym.D :: Lsym.C1 :: l, r)
    | Rsym.P :: Rsym.D :: Rsym.Gs n :: r =>
        some (.right, Hls n l, Rsym.P :: Rsym.D :: r)
    | Rsym.P :: Rsym.Cr :: r =>
      match unrxs r with
      | some r => some (.left, l, Rsym.P :: Rsym.D :: Rsym.P :: r)
      | none => none
    | Rsym.P :: Rsym.P :: r => some (.right, lxs 1 l, r)
    | Rsym.Gs n :: r => some (.right, Gls n l, r)
    | _ => none
  | (.left, l, r) =>
    match l with
    | [] =>
      match r with
      | Rsym.Cr :: r =>
        match unrxs r with
        | some r => some (.right, [Lsym.D, Lsym.C1], Rsym.P :: r)
        | none => none
      | _ => none
    | Lsym.xs n :: l => some (.left, l, rxs n r)
    | Lsym.D :: l => some (.left, l, Rsym.D :: r)
    | Lsym.P :: l => some (.left, l, Rsym.P :: r)
    | Lsym.C0 :: l => some (.right, Lsym.xs 1 :: Lsym.C1 :: l, r)
    | Lsym.C1 :: l => some (.right, Lsym.C2 :: l, r)
    | Lsym.C2 :: l => some (.right, Lsym.xs 1 :: Lsym.C3 :: l, r)
    | Lsym.C3 :: l => some (.left, l, Rsym.Cr :: r)
    | Lsym.F0 :: l => some (.right, Lsym.xs 1 :: Lsym.F1 :: l, r)
    | Lsym.F1 :: l => some (.right, Lsym.F2 :: l, r)
    | Lsym.F2 :: l => some (.right, Lsym.xs 1 :: Lsym.F3 :: l, r)
    | Lsym.F3 :: Lsym.xs (n + 1) :: l =>
        some (.right, Lsym.D :: Lsym.C1 :: Lsym.P :: lxs n l, r)
    | Lsym.G0 :: l => some (.right, Lsym.xs 1 :: Lsym.G1 :: l, r)
    | Lsym.G1 :: l => some (.right, Lsym.G2 :: l, r)
    | Lsym.G2 :: l => some (.right, Lsym.xs 1 :: Lsym.D :: Lsym.P :: l, r)
    | Lsym.Gs n :: l => some (.left, l, Grs n r)
    | _ => none

/-
Soundness of the `right`-facing cases of `simple_step`.
-/
lemma simple_step_spec_right (l : Ltape) (r : Rtape) (c' : Turing.Dir × Ltape × Rtape)
    (h : simple_step (.right, l, r) = some c') : lift (.right, l, r) -[M]->* lift c' := by
  rcases r with (_ | ⟨a, r⟩)
  · rcases l with (_ | ⟨a, l⟩)
    · simp [simple_step] at h
    · cases a <;> simp [simple_step] at h
      · rename_i n
        cases n with
        | zero => cases h
        | succ n =>
          simp at h
          subst c'
          simpa [lift, liftL, liftR, liftL_lxs, lpow_succ,
            ListBlank.append_assoc'] using rule_xR (liftL (lxs n l))
      · subst c'
        simpa [lift, liftL, liftR, RB, lpow_succ, lpow_zero,
          ListBlank.append_assoc'] using rule_DR (liftL l)
  · cases a with
    | xs n =>
      simp [simple_step] at h
      subst c'
      simpa [lift, liftR, liftL_lxs] using
        rule_xn_right n (liftL l) (liftR r)
    | D =>
      simp [simple_step] at h
      subst c'
      simpa [lift, liftL, liftR] using rule_D_right (liftL l) (liftR r)
    | Cr =>
      rcases l with (_ | ⟨a, l⟩)
      · cases h
      · cases a <;> simp [simple_step] at h
        · rename_i n
          cases n with
          | zero => cases h
          | succ n =>
            simp at h
            subst c'
            simpa [lift, liftL, liftR, liftL_lxs, lpow_succ,
              ListBlank.append_assoc'] using
              rule_C30 (liftL (lxs n l)) (liftR r)
        · subst c'
          simpa [lift, liftL, liftR, lpow_succ, lpow_zero,
            ListBlank.append_assoc'] using rule_DC (liftL l) (liftR r)
        · subst c'
          simpa [lift, liftL, liftR] using rule_C03 (liftL l) (liftR r)
        · subst c'
          simpa [lift, liftL, liftR] using rule_C2_C (liftL l) (liftR r)
    | P =>
      rcases r with (_ | ⟨a, r⟩)
      · simp [simple_step] at h
        subst c'
        simpa [lift, liftR, ListBlank.append_assoc'] using rule_P_R (liftL l)
      · cases a with
        | xs n =>
          simp [simple_step] at h
          subst c'
          simpa only [lift, liftR, liftL_lxs, ListBlank.append_assoc'] using
            rule_P_xn n (liftL l) (liftR r)
        | D =>
          rcases r with (_ | ⟨a, r⟩)
          · cases h
          · cases a with
            | xs n =>
              cases n with
              | zero => cases h
              | succ n =>
                simp [simple_step] at h
                subst c'
                simpa [lift, liftL, liftR, liftR_rxs, lpow_succ,
                  ListBlank.append_assoc'] using
                  rule_P_Dx (liftL l) (liftR (rxs n r))
            | D =>
              rcases hu : unrxs r with (_ | r') <;> simp [simple_step, hu] at h
              subst c'
              have hr := unrxs_spec r r' hu
              simpa [lift, liftL, liftR, hr, ListBlank.append_assoc'] using
                rule_P_DDx (liftL l) (liftR r')
            | Cr =>
              rcases hu : unrxs r with (_ | r') <;> simp [simple_step, hu] at h
              subst c'
              have hr := unrxs_spec r r' hu
              simpa [lift, liftL, liftR, hr, ListBlank.append_assoc'] using
                rule_P_DCx (liftL l) (liftR r')
            | P =>
              simp [simple_step] at h
              subst c'
              simpa only [lift, liftL, liftR, ListBlank.append_assoc'] using
                rule_P_DP (liftL l) (liftR r)
            | Gs n =>
              simp [simple_step] at h
              subst c'
              simpa [lift, liftL_Hls, liftR, ListBlank.append_assoc'] using
                rule_P_DGn n (liftL l) (liftR r)
        | Cr =>
          rcases hu : unrxs r with (_ | r') <;> simp [simple_step, hu] at h
          subst c'
          have hr := unrxs_spec r r' hu
          simpa [lift, liftR, hr, ListBlank.append_assoc'] using
            rule_P_Cx (liftL l) (liftR r')
        | P =>
          simp [simple_step] at h
          subst c'
          simpa [lift, liftL_lxs, liftR, lpow_succ, lpow_zero,
            ListBlank.append_assoc'] using rule_P_P (liftL l) (liftR r)
        | Gs n => cases h
    | Gs n =>
      simp [simple_step] at h
      subst c'
      simpa [lift, liftR, liftL_Gls] using
        rule_Gn_right n (liftL l) (liftR r)

/-
Soundness of the `left`-facing cases of `simple_step`.
-/
lemma simple_step_spec_left (l : Ltape) (r : Rtape) (c' : Turing.Dir × Ltape × Rtape)
    (h : simple_step (.left, l, r) = some c') : lift (.left, l, r) -[M]->* lift c' := by
  rcases l with (_ | ⟨a, l⟩)
  · rcases r with (_ | ⟨a, r⟩)
    · simp [simple_step] at h
    · cases a <;> simp [simple_step] at h
      · rcases hu : unrxs r with (_ | r') <;> simp [hu] at h
        subst c'
        have hr := unrxs_spec r r' hu
        simpa [lift, liftL, liftR, hr, ListBlank.append_assoc'] using
          rule_L (liftR r')
  · cases a <;> simp [simple_step] at h
    · rename_i n
      subst c'
      simpa [lift, liftL, liftR_rxs] using
        rule_xn_left n (liftL l) (liftR r)
    · subst c'
      simpa [lift, liftL, liftR] using rule_D_left (liftL l) (liftR r)
    · subst c'
      simpa [lift, liftL, liftR] using rule_P_left (liftL l) (liftR r)
    · subst c'
      simpa [lift, liftL, lpow_succ, lpow_zero, ListBlank.append_assoc'] using
        rule_C01 (liftL l) (liftR r)
    · subst c'
      simpa [lift, liftL] using rule_C12 (liftL l) (liftR r)
    · subst c'
      simpa [lift, liftL, lpow_succ, lpow_zero, ListBlank.append_assoc'] using
        rule_C23 (liftL l) (liftR r)
    · subst c'
      simpa [lift, liftL, liftR] using rule_C_left (liftL l) (liftR r)
    · subst c'
      simpa [lift, liftL, lpow_succ, lpow_zero, ListBlank.append_assoc'] using
        rule_F0 (liftL l) (liftR r)
    · subst c'
      simpa [lift, liftL] using rule_F1 (liftL l) (liftR r)
    · subst c'
      simpa [lift, liftL, lpow_succ, lpow_zero, ListBlank.append_assoc'] using
        rule_F2 (liftL l) (liftR r)
    · rcases l with (_ | ⟨a, l⟩)
      · cases h
      · cases a with
        | xs n =>
          cases n with
          | zero => cases h
          | succ n =>
            simp at h
            subst c'
            simpa [lift, liftL, liftL_lxs, lpow_succ, ListBlank.append_assoc'] using
              rule_F3 (liftL (lxs n l)) (liftR r)
        | D => cases h
        | P => cases h
        | C0 => cases h
        | C1 => cases h
        | C2 => cases h
        | C3 => cases h
        | F0 => cases h
        | F1 => cases h
        | F2 => cases h
        | F3 => cases h
        | G0 => cases h
        | G1 => cases h
        | G2 => cases h
        | Fs n => cases h
        | Gs n => cases h
        | Hs n => cases h
    · subst c'
      simpa [lift, liftL, lpow_succ, lpow_zero, ListBlank.append_assoc'] using
        rule_G0 (liftL l) (liftR r)
    · subst c'
      simpa [lift, liftL] using rule_G1 (liftL l) (liftR r)
    · subst c'
      simpa [lift, liftL, lpow_succ, lpow_zero, ListBlank.append_assoc'] using
        rule_G2 (liftL l) (liftR r)
    · rename_i n
      subst c'
      simpa [lift, liftL, liftR_Grs] using
        rule_Gn_left n (liftL l) (liftR r)

/-- Soundness of `simple_step` (Coq `simple_step_spec`). -/
lemma simple_step_spec (c c' : Turing.Dir × Ltape × Rtape) (h : simple_step c = some c') :
    lift c -[M]->* lift c' := by
  obtain ⟨d, l, r⟩ := c
  cases d with
  | right => exact simple_step_spec_right l r c' h
  | left => exact simple_step_spec_left l r c' h

/-- The Coq `initial` symbolic configuration `(right, [l_C1], [r_P])`. -/
def initial : Turing.Dir × Ltape × Rtape := (.right, [Lsym.C1], [Rsym.P])

/-- Iterate the concrete machine step `M.step` `n` times. -/
def machRunN : ℕ → Config 4 1 → Option (Config 4 1)
  | 0, c => some c
  | n + 1, c => (M.step c).bind (machRunN n)

/-- Soundness of `machRunN`: a successful `n`-fold run is an `EvStep`.  (Recall
`A -[M]-> B` is definitionally `M.step A = some B`.) -/
lemma machRunN_evstep (n : ℕ) (c c' : Config 4 1) (h : machRunN n c = some c') :
    c -[M]->* c' := by
  induction n generalizing c with
  | zero =>
    simp only [machRunN, Option.some.injEq] at h; subst h; exact Machine.EvStep.refl
  | succ n ih =>
    simp only [machRunN] at h
    cases hs : M.step c with
    | none => rw [hs] at h; simp at h
    | some c'' =>
      rw [hs, Option.bind_some] at h
      exact Machine.EvStep.step hs (ih c'' h)

/-- From the blank tape, `M` reaches `lift initial` in exactly 19 steps
(Coq `init`/`init'`).  The 19-step run is checked by reflection. -/
lemma init_reach : (init : Config 4 1) -[M]->* lift initial := by
  have h : machRunN 19 (init : Config 4 1) = some (lift initial) := by native_decide
  exact machRunN_evstep 19 _ _ h

/-! ## Iterating `simple_step`. -/

/-- Iterate `simple_step` `n` times, threading through `Option`. -/
def simpleSteps : ℕ → (Turing.Dir × Ltape × Rtape) → Option (Turing.Dir × Ltape × Rtape)
  | 0, c => some c
  | n + 1, c =>
    match simple_step c with
    | some c' => simpleSteps n c'
    | none => none

/-- Soundness of iterated `simple_step`. -/
lemma simpleSteps_spec (n : ℕ) (c c' : Turing.Dir × Ltape × Rtape)
    (h : simpleSteps n c = some c') : lift c -[M]->* lift c' := by
  induction n generalizing c with
  | zero =>
    simp only [simpleSteps, Option.some.injEq] at h; subst h; exact Machine.EvStep.refl
  | succ n ih =>
    simp only [simpleSteps] at h
    cases hs : simple_step c with
    | none => rw [hs] at h; exact absurd h (by simp)
    | some c'' =>
      rw [hs] at h
      exact (simple_step_spec c c'' hs).trans (ih c'' h)

end Deciders.Skelet.Skelet1
