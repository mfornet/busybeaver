import Mathlib.Tactic
import Busybeaver.Deciders.BoundExplore
import Busybeaver.Deciders.FAR
import Busybeaver.Deciders.Loop1
import Busybeaver.Deciders.NGramCPS
import Busybeaver.Deciders.RepWL
import Busybeaver.Deciders.Sweep
import Busybeaver.Deciders.WFAR
import Busybeaver.Parse
import Busybeaver.TM.Table.ClosedSet
import Std.Data.HashMap
import Busybeaver.Deciders.Skelet.FixedBin
import Busybeaver.Deciders.Skelet.ShiftOverflow
import Busybeaver.Deciders.Skelet.ShiftOverflowBins
import Busybeaver.Deciders.Skelet.TapeCalc

/-!
Executable support for the BB(5) table-based layer.

The Coq BB5 proof uses a small generic pipeline followed by a lookup table for
machines requiring custom parameters, verifiers, or individual nonhalting
arguments.  This file defines the Lean-side shape of that table and the
algorithmic evaluator for the entries we already have executable support for.

The large Coq parameter lists are intentionally not copied here by hand.  They
are generated into `Entry` values by `scripts/generate_bb5_table.py`.
-/

/-!
## Skelet #26 (`sporadicMachine9`) development

Inlined from the former `Busybeaver/Deciders/Skelet/Skelet26.lean`.  This is a
Lean port of `Coq-BB5/BusyCoq/Skelet26.v` (sligocki's Skelet #26 analysis) up to
and including `step_reset0`.  It lives in its own `Deciders.Skelet.Skelet26`
namespace, kept inside a `section` so the local `open`s do not leak into the rest
of the table file.
-/
section Skelet26Inline
open Turing
open TM.Table
open Deciders.Skelet.ShiftOverflowBins
open Deciders.Skelet.ShiftOverflow
open Deciders.Skelet.FixedBin

namespace Deciders.Skelet.Skelet26

abbrev M : Machine 4 1 := mach["1RB1LD_1RC0RB_1LA1RC_1LE0LA_1LC---"]

local notation "𝟙" => (1 : Symbol 1)
local notation "𝟘" => (0 : Symbol 1)

-- Transitions (A=0, B=1, C=2, D=3, E=4).
lemma gA0 : M.get 0 0 = .next 1 .right 1 := by decide
lemma gA1 : M.get 0 1 = .next 1 .left 3 := by decide
lemma gB0 : M.get 1 0 = .next 1 .right 2 := by decide
lemma gB1 : M.get 1 1 = .next 0 .right 1 := by decide
lemma gC0 : M.get 2 0 = .next 1 .left 0 := by decide
lemma gC1 : M.get 2 1 = .next 1 .right 2 := by decide
lemma gD0 : M.get 3 0 = .next 1 .left 4 := by decide
lemma gD1 : M.get 3 1 = .next 0 .left 0 := by decide
lemma gE0 : M.get 4 0 = .next 1 .left 2 := by decide
-- blank-edge
lemma gA0d : M.get 0 default = .next 1 .right 1 := by decide
lemma gB0d : M.get 1 default = .next 1 .right 2 := by decide
lemma gC0d : M.get 2 default = .next 1 .left 0 := by decide
lemma gD0d : M.get 3 default = .next 1 .left 4 := by decide
lemma gE0d : M.get 4 default = .next 1 .left 2 := by decide

/-- Rightward directed configuration (Coq `l {{q}}> r`): head reads the top of
`R`, left side is `L`. -/
def headR (q : Label 4) (L R : ListBlank (Symbol 1)) : Config 4 1 := ⟨q, Tape.mk' L R⟩

open TM.Table (headL)

/-- The counter configuration `D n a m` (Coq `D`): `L n <{{D}} 1 0 1 a *> R m`. -/
def D (n : Num) (a : Symbol 1) (m : PosNum) : Config 4 1 :=
  headL 3 (L n) (ListBlank.cons 𝟙 (ListBlank.cons 𝟘 (ListBlank.cons 𝟙 (ListBlank.cons a (R m)))))

/-- Left counter increment sweep, base case `n = 0` (7 steps). -/
lemma L_inc_zero (r : ListBlank (Symbol 1)) :
    headL 3 (L 0) r -[M]->* headR 1 (L' .one) r := by
  rw [show (L 0) = (∅ : ListBlank (Symbol 1)) from rfl, TM.Table.headL_empty]
  simp only [L', headR]
  refine Machine.EvStep.step (step_left_edge gD0 r) ?_
  refine Machine.EvStep.step (step_left_edge gE0 _) ?_
  refine Machine.EvStep.step (step_left_edge gC0 _) ?_
  refine Machine.EvStep.step (step_right_mk' gA0 _ _) ?_
  refine Machine.EvStep.step (step_right_mk' gB1 _ _) ?_
  refine Machine.EvStep.step (step_right_mk' gB1 _ _) ?_
  exact Machine.EvStep.step (step_right_mk' gB1 _ _) Machine.EvStep.refl

/-
Left counter increment sweep on a positive counter (Coq `L_inc`, positive part).
Induction on `p`.
-/
lemma L'_inc (p : PosNum) (r : ListBlank (Symbol 1)) :
    headL 3 (L' p) r -[M]->* headR 1 (L' (PosNum.succ p)) r := by
  revert r;
  induction p using PosNum.recOn ; simp_all +decide [ L', headR, headL_cons, PosNum.succ ];
  · intro r
    constructor;
    exact step_left_mk' gD0 _ _;
    refine' Machine.EvStep.step ( step_left_mk' gE0 _ _ ) _;
    refine' Machine.EvStep.step ( step_left_mk' gC0 _ _ ) _;
    refine' Machine.EvStep.step ( step_left_edge gA1 _ ) _;
    convert L_inc_zero _ |> Machine.EvStep.trans <| _ using 1;
    refine' Machine.EvStep.step ( step_right_mk' gB1 _ _ ) _;
    refine' Machine.EvStep.step ( step_right_mk' gB1 _ _ ) _;
    refine' Machine.EvStep.step ( step_right_mk' gB1 _ _ ) _;
    refine' Machine.EvStep.step ( step_right_mk' gB1 _ _ ) _;
    constructor;
  · rename_i k ih; intro r; simp_all +decide [ L', headL_cons, headR, PosNum.succ ] ;
    convert Machine.EvStep.trans _ ( ih _ ) |> Machine.EvStep.trans <| _ using 1;
    convert Machine.EvStep.step ( step_left_mk' gD0 _ _ ) ( Machine.EvStep.step ( step_left_mk' gE0 _ _ ) ( Machine.EvStep.step ( step_left_mk' gC0 _ _ ) ( Machine.EvStep.step ( step_left_mk' gA1 _ _ ) Machine.EvStep.refl ) ) ) using 1;
    rotate_left;
    exact r;
    · convert Machine.EvStep.step ( step_right_mk' gB1 _ _ ) ( Machine.EvStep.step ( step_right_mk' gB1 _ _ ) ( Machine.EvStep.step ( step_right_mk' gB1 _ _ ) ( Machine.EvStep.step ( step_right_mk' gB1 _ _ ) Machine.EvStep.refl ) ) ) using 1;
    · cases k <;> aesop;
  · intro r; exact (by
    rename_i k ih
    simp [L', headR, headL_cons, PosNum.succ] at *;
    convert Machine.EvStep.step ( step_left_mk' gD0 _ _ ) ( Machine.EvStep.step ( step_left_mk' gE0 _ _ ) ( Machine.EvStep.step ( step_left_mk' gC0 _ _ ) ( Machine.EvStep.step ( step_right_mk' gA0 _ _ ) ( Machine.EvStep.step ( step_right_mk' gB1 _ _ ) ( Machine.EvStep.step ( step_right_mk' gB1 _ _ ) ( Machine.EvStep.step ( step_right_mk' gB1 _ _ ) ( Machine.EvStep.refl ) ) ) ) ) ) ) using 1);

/-- Left counter increment sweep (Coq `L_inc`). -/
lemma L_inc (n : Num) (r : ListBlank (Symbol 1)) :
    headL 3 (L n) r -[M]->* headR 1 (L (Num.succ n)) r := by
  cases n with
  | zero => exact L_inc_zero r
  | pos p => exact L'_inc p r

/-
Right counter increment with no overflow (Coq `R_inc_has0`).  Induction on `h`.
-/
lemma R_inc_has0 {n : PosNum} (h : Has0 n) (l : ListBlank (Symbol 1)) :
    headR 2 l (R n) -[M]->* headL 3 l (R n.succ) := by
  induction h generalizing l with
  | bit0 n =>
      show headR 2 l (ListBlank.cons 𝟙 (ListBlank.cons 𝟘 (R n)))
        -[M]->* headL 3 l (R (PosNum.succ (.bit0 n)))
      refine Machine.EvStep.step (step_right_mk' gC1 _ _) ?_
      refine Machine.EvStep.step (step_left_mk' gC0 _ _) ?_
      exact Machine.EvStep.step (step_left_head gA1 _ _) Machine.EvStep.refl
  | @bit1 n h ih =>
      show headR 2 l (ListBlank.cons 𝟙 (ListBlank.cons 𝟙 (R n)))
        -[M]->* headL 3 l (R (PosNum.succ (.bit1 n)))
      refine Machine.EvStep.step (step_right_mk' gC1 _ _) ?_
      refine Machine.EvStep.step (step_right_mk' gC1 _ _) ?_
      refine (ih (ListBlank.cons 𝟙 (ListBlank.cons 𝟙 l))).trans ?_
      rw [headL_cons]
      refine Machine.EvStep.step (step_left_mk' gD1 _ _) ?_
      exact Machine.EvStep.step (step_left_head gA1 _ _) Machine.EvStep.refl

/-- Right counter increment with overflow (Coq `R_inc_all1`).  Induction on `h`. -/
lemma R_inc_all1 {n : PosNum} (h : All1 n) (l : ListBlank (Symbol 1)) :
    headR 2 (ListBlank.cons 𝟙 l) (R n) -[M]->* headL 3 l (R n.succ) := by
  induction h generalizing l with
  | one =>
      show headR 2 (ListBlank.cons 𝟙 l) (ListBlank.cons 𝟙 (ListBlank.cons 𝟙 ∅))
        -[M]->* headL 3 l (R (PosNum.succ .one))
      refine Machine.EvStep.step (step_right_mk' gC1 _ _) ?_
      refine Machine.EvStep.step (step_right_mk' gC1 _ _) ?_
      refine Machine.EvStep.step (step_left_blank gC0 _) ?_
      refine Machine.EvStep.step (step_left_mk' gA1 _ _) ?_
      refine Machine.EvStep.step (step_left_mk' gD1 _ _) ?_
      exact Machine.EvStep.step (step_left_head gA1 _ _) Machine.EvStep.refl
  | @bit1 n h ih =>
      show headR 2 (ListBlank.cons 𝟙 l) (ListBlank.cons 𝟙 (ListBlank.cons 𝟙 (R n)))
        -[M]->* headL 3 l (R (PosNum.succ (.bit1 n)))
      refine Machine.EvStep.step (step_right_mk' gC1 _ _) ?_
      refine Machine.EvStep.step (step_right_mk' gC1 _ _) ?_
      refine (ih (ListBlank.cons 𝟙 (ListBlank.cons 𝟙 l))).trans ?_
      rw [headL_cons]
      refine Machine.EvStep.step (step_left_mk' gD1 _ _) ?_
      exact Machine.EvStep.step (step_left_head gA1 _ _) Machine.EvStep.refl

/-- `D_inc` for `a = 0`. -/
lemma D_inc_zero {n : Num} {m : PosNum} (h : Has0 m) :
    D n 0 m -[M]->* D (Num.succ n) 0 m.succ := by
  unfold D
  refine (L_inc n _).trans ?_
  refine Machine.EvStep.step (step_right_mk' gB1 _ _) ?_
  refine Machine.EvStep.step (step_right_mk' gB0 _ _) ?_
  refine Machine.EvStep.step (step_right_mk' gC1 _ _) ?_
  refine Machine.EvStep.step (step_left_mk' gC0 _ _) ?_
  refine Machine.EvStep.step (step_left_mk' gA1 _ _) ?_
  refine Machine.EvStep.step (step_left_mk' gD1 _ _) ?_
  refine Machine.EvStep.step (step_right_mk' gA0 _ _) ?_
  refine Machine.EvStep.step (step_right_mk' gB0 _ _) ?_
  refine Machine.EvStep.step (step_right_mk' gC1 _ _) ?_
  refine Machine.EvStep.step (step_right_mk' gC1 _ _) ?_
  refine (R_inc_has0 h _).trans ?_
  rw [headL_cons]
  refine Machine.EvStep.step (step_left_mk' gD1 _ _) ?_
  refine Machine.EvStep.step (step_left_mk' gA1 _ _) ?_
  refine Machine.EvStep.step (step_left_mk' gD1 _ _) ?_
  exact Machine.EvStep.step (step_left_head gA1 _ _) Machine.EvStep.refl

/-- `D_inc` for `a = 1`. -/
lemma D_inc_one {n : Num} {m : PosNum} (h : Has0 m) :
    D n 1 m -[M]->* D (Num.succ n) 1 m.succ := by
  unfold D
  refine (L_inc n _).trans ?_
  refine Machine.EvStep.step (step_right_mk' gB1 _ _) ?_
  refine Machine.EvStep.step (step_right_mk' gB0 _ _) ?_
  refine Machine.EvStep.step (step_right_mk' gC1 _ _) ?_
  refine Machine.EvStep.step (step_right_mk' gC1 _ _) ?_
  refine (R_inc_has0 h _).trans ?_
  rw [headL_cons]
  refine Machine.EvStep.step (step_left_mk' gD1 _ _) ?_
  refine Machine.EvStep.step (step_left_mk' gA1 _ _) ?_
  refine Machine.EvStep.step (step_left_mk' gD1 _ _) ?_
  refine Machine.EvStep.step (step_right_mk' gA0 _ _) ?_
  refine Machine.EvStep.step (step_right_mk' gB0 _ _) ?_
  refine Machine.EvStep.step (step_right_mk' gC1 _ _) ?_
  refine Machine.EvStep.step (step_left_mk' gC0 _ _) ?_
  refine Machine.EvStep.step (step_left_mk' gA1 _ _) ?_
  refine Machine.EvStep.step (step_left_mk' gD1 _ _) ?_
  exact Machine.EvStep.step (step_left_head gA1 _ _) Machine.EvStep.refl

/-- One counter increment (Coq `D_inc`). -/
lemma D_inc {n : Num} {a : Symbol 1} {m : PosNum} (h : Has0 m) :
    D n a m -[M]->* D (Num.succ n) a m.succ := by
  match a with
  | 0 => exact D_inc_zero h
  | 1 => exact D_inc_one h

/-- Iterated increment by `u ≤ b m` (Coq `D_run`).  Induction on `u`. -/
lemma D_run {n : Num} {a : Symbol 1} {m : PosNum} (u : ℕ) (hu : u ≤ b m) :
    D n a m -[M]->* D ((u : Num) + n) a (addN u m) := by
  induction u generalizing n m with
  | zero => simpa using Machine.EvStep.refl
  | succ u ih =>
      have hbm : 0 < b m := by omega
      refine (D_inc (bgt0_has0 hbm)).trans ?_
      have hbound : u ≤ b m.succ := by rw [b_succ hbm]; omega
      have key := ih (n := Num.succ n) (m := m.succ) hbound
      have hw : addN (u + 1) m = addN u m.succ := Function.iterate_succ_apply PosNum.succ u m
      have hc : ((u + 1 : ℕ) : Num) + n = (u : Num) + Num.succ n := by
        rw [Nat.cast_add_one, ← Num.add_one, add_assoc, add_comm (1 : Num) n]
      have htgt : D ((u : Num) + Num.succ n) a (addN u m.succ)
          = D (((u + 1 : ℕ) : Num) + n) a (addN (u + 1) m) := by
        rw [hc, hw]
      rw [← htgt]
      exact key

/-- Run to saturation (Coq `D_finish`). -/
lemma D_finish {n : Num} {a : Symbol 1} {m : PosNum} :
    D n a m -[M]->* D ((b m : Num) + n) a (addN (b m) m) :=
  D_run (b m) le_rfl

/-! ## The `J`/`K` representations and reset machinery -/

/-- Coq `J'`. -/
def J' : PosNum → side
  | .one => ListBlank.cons 𝟙 ∅
  | .bit0 n => ListBlank.cons 𝟘 (ListBlank.cons 𝟘 (ListBlank.cons 𝟘 (ListBlank.cons 𝟘 (J' n))))
  | .bit1 n => ListBlank.cons 𝟙 (ListBlank.cons 𝟘 (ListBlank.cons 𝟘 (ListBlank.cons 𝟘 (J' n))))

/-- Coq `J`. -/
def J : Num → side
  | .zero => ∅
  | .pos n => J' n

lemma L'_as_J' : ∀ p, L' p = ListBlank.cons 𝟘 (ListBlank.cons 𝟘 (ListBlank.cons 𝟘 (J' p)))
  | .one => rfl
  | .bit0 p => by simp only [L', J', L'_as_J' p]
  | .bit1 p => by simp only [L', J', L'_as_J' p]

lemma K'_as_J' : ∀ p, K' p = ListBlank.cons 𝟘 (ListBlank.cons 𝟘 (J' p))
  | .one => rfl
  | .bit0 p => by simp only [K', J', K'_as_J' p]
  | .bit1 p => by simp only [K', J', K'_as_J' p]

/-- Coq `L_as_J`. -/
lemma L_as_J (n : Num) : L n = ListBlank.cons 𝟘 (ListBlank.cons 𝟘 (ListBlank.cons 𝟘 (J n))) := by
  cases n with
  | zero => simp only [L, J, cons0_empty]
  | pos p => exact L'_as_J' p

/-- Coq `K_as_J`. -/
lemma K_as_J (n : Num) : K n = ListBlank.cons 𝟘 (ListBlank.cons 𝟘 (J n)) := by
  cases n with
  | zero => simp only [K, J, cons0_empty]
  | pos p => exact K'_as_J' p

/-- Counter configuration `E0` (Coq `E0`). -/
def E0 (n : Num) (a : Symbol 1) (m : PosNum) : Config 4 1 :=
  headL 3 (K n) (ListBlank.cons 𝟙 (ListBlank.cons 𝟘 (ListBlank.cons 𝟙 (ListBlank.cons a (R m)))))

/-- Counter configuration `E1` (Coq `E1`). -/
def E1 (n : Num) (a : Symbol 1) (m : PosNum) : Config 4 1 :=
  headL 3 (J n) (ListBlank.cons 𝟙 (ListBlank.cons 𝟘 (ListBlank.cons 𝟙 (ListBlank.cons a (R m)))))

/-- Coq `eat_LI`. -/
lemma eat_LI (l : side) (t : PosNum) :
    headL 3 (ListBlank.cons 𝟘 (ListBlank.cons 𝟘 (ListBlank.cons 𝟘 (ListBlank.cons 𝟙 l)))) (R t)
      -[M]->* headL 3 l (R t.bit1.bit1) := by
  rw [headL_cons]
  refine Machine.EvStep.step (step_left_mk' gD0 _ _) ?_
  refine Machine.EvStep.step (step_left_mk' gE0 _ _) ?_
  refine Machine.EvStep.step (step_left_mk' gC0 _ _) ?_
  exact Machine.EvStep.step (step_left_head gA1 _ _) Machine.EvStep.refl

/-- Coq `eat_KI`. -/
lemma eat_KI {t : PosNum} (h : Has0 t) (l : side) :
    headL 3 (ListBlank.cons 𝟘 (ListBlank.cons 𝟘 (ListBlank.cons 𝟙 (ListBlank.cons 𝟘 l)))) (R t)
      -[M]->* headL 3 l (R t.succ.bit1.bit0) := by
  rw [headL_cons]
  refine Machine.EvStep.step (step_left_mk' gD0 _ _) ?_
  refine Machine.EvStep.step (step_left_mk' gE0 _ _) ?_
  refine Machine.EvStep.step (step_right_mk' gC1 _ _) ?_
  refine Machine.EvStep.step (step_right_mk' gC1 _ _) ?_
  refine Machine.EvStep.step (step_right_mk' gC1 _ _) ?_
  refine (R_inc_has0 h _).trans ?_
  rw [headL_cons]
  refine Machine.EvStep.step (step_left_mk' gD1 _ _) ?_
  refine Machine.EvStep.step (step_left_mk' gA1 _ _) ?_
  refine Machine.EvStep.step (step_left_mk' gD1 _ _) ?_
  refine Machine.EvStep.step (step_right_mk' gA0 _ _) ?_
  refine Machine.EvStep.step (step_right_mk' gB0 _ _) ?_
  refine Machine.EvStep.step (step_right_mk' gC1 _ _) ?_
  refine Machine.EvStep.step (step_left_mk' gC0 _ _) ?_
  refine Machine.EvStep.step (step_left_mk' gA1 _ _) ?_
  refine Machine.EvStep.step (step_left_mk' gD1 _ _) ?_
  exact Machine.EvStep.step (step_left_head gA1 _ _) Machine.EvStep.refl

/-- Coq `eat_JI`. -/
lemma eat_JI {t : PosNum} (h : Has0 t) (l : side) :
    headL 3 (ListBlank.cons 𝟙 (ListBlank.cons 𝟘 l)) (R t)
      -[M]->* headL 3 l (R t.succ.bit0) := by
  rw [headL_cons]
  refine Machine.EvStep.step (step_left_mk' gD1 _ _) ?_
  refine Machine.EvStep.step (step_right_mk' gA0 _ _) ?_
  refine Machine.EvStep.step (step_right_mk' gB0 _ _) ?_
  refine (R_inc_has0 h _).trans ?_
  rw [headL_cons]
  refine Machine.EvStep.step (step_left_mk' gD1 _ _) ?_
  exact Machine.EvStep.step (step_left_head gA1 _ _) Machine.EvStep.refl

open Deciders.Skelet.FixedBin in
/-- Increment of a fixed-width `Lk` block (Coq `Lk_inc`).  Induction on the `Succ` proof. -/
lemma Lk_inc {k : ℕ} {n n' : Bin k} (hn : Succ n n') (l : side) (r : side) :
    headL 3 ((Lk n : List (Symbol 1)) ++ l) r -[M]->* headR 1 ((Lk n' : List (Symbol 1)) ++ l) r := by
  induction hn generalizing l r with
  | b0 n =>
      simp only [Lk, ListBlank.append_cons]
      rw [headL_cons]
      refine Machine.EvStep.step (step_left_mk' gD0 _ _) ?_
      refine Machine.EvStep.step (step_left_mk' gE0 _ _) ?_
      refine Machine.EvStep.step (step_left_mk' gC0 _ _) ?_
      refine Machine.EvStep.step (step_right_mk' gA0 _ _) ?_
      refine Machine.EvStep.step (step_right_mk' gB1 _ _) ?_
      refine Machine.EvStep.step (step_right_mk' gB1 _ _) ?_
      exact Machine.EvStep.step (step_right_mk' gB1 _ _) Machine.EvStep.refl
  | @b1 k' np ns hp ih =>
      simp only [Lk, ListBlank.append_cons]
      rw [headL_cons]
      refine Machine.EvStep.step (step_left_mk' gD0 _ _) ?_
      refine Machine.EvStep.step (step_left_mk' gE0 _ _) ?_
      refine Machine.EvStep.step (step_left_mk' gC0 _ _) ?_
      refine Machine.EvStep.step (step_left_head gA1 _ _) ?_
      refine (ih l (ListBlank.cons 𝟙 (ListBlank.cons 𝟙 (ListBlank.cons 𝟙 (ListBlank.cons 𝟙 r))))).trans ?_
      refine Machine.EvStep.step (step_right_mk' gB1 _ _) ?_
      refine Machine.EvStep.step (step_right_mk' gB1 _ _) ?_
      refine Machine.EvStep.step (step_right_mk' gB1 _ _) ?_
      exact Machine.EvStep.step (step_right_mk' gB1 _ _) Machine.EvStep.refl

open Deciders.Skelet.FixedBin in
/-- `LaR_inc` for `a = 0`. -/
lemma LaR_inc_zero {k : ℕ} {np ns : Bin k} (hn : Succ np ns) {m : PosNum} (hm : Has0 m) (l : side) :
    headL 3 ((Lk np : List (Symbol 1)) ++ l)
        (ListBlank.cons 𝟙 (ListBlank.cons 𝟘 (ListBlank.cons 𝟙 (ListBlank.cons 𝟘 (R m)))))
      -[M]->* headL 3 ((Lk ns : List (Symbol 1)) ++ l)
        (ListBlank.cons 𝟙 (ListBlank.cons 𝟘 (ListBlank.cons 𝟙 (ListBlank.cons 𝟘 (R m.succ))))) := by
  refine (Lk_inc hn l _).trans ?_
  refine Machine.EvStep.step (step_right_mk' gB1 _ _) ?_
  refine Machine.EvStep.step (step_right_mk' gB0 _ _) ?_
  refine Machine.EvStep.step (step_right_mk' gC1 _ _) ?_
  refine Machine.EvStep.step (step_left_mk' gC0 _ _) ?_
  refine Machine.EvStep.step (step_left_mk' gA1 _ _) ?_
  refine Machine.EvStep.step (step_left_mk' gD1 _ _) ?_
  refine Machine.EvStep.step (step_right_mk' gA0 _ _) ?_
  refine Machine.EvStep.step (step_right_mk' gB0 _ _) ?_
  refine Machine.EvStep.step (step_right_mk' gC1 _ _) ?_
  refine Machine.EvStep.step (step_right_mk' gC1 _ _) ?_
  refine (R_inc_has0 hm _).trans ?_
  rw [headL_cons]
  refine Machine.EvStep.step (step_left_mk' gD1 _ _) ?_
  refine Machine.EvStep.step (step_left_mk' gA1 _ _) ?_
  refine Machine.EvStep.step (step_left_mk' gD1 _ _) ?_
  exact Machine.EvStep.step (step_left_head gA1 _ _) Machine.EvStep.refl

open Deciders.Skelet.FixedBin in
/-- `LaR_inc` for `a = 1`. -/
lemma LaR_inc_one {k : ℕ} {np ns : Bin k} (hn : Succ np ns) {m : PosNum} (hm : Has0 m) (l : side) :
    headL 3 ((Lk np : List (Symbol 1)) ++ l)
        (ListBlank.cons 𝟙 (ListBlank.cons 𝟘 (ListBlank.cons 𝟙 (ListBlank.cons 𝟙 (R m)))))
      -[M]->* headL 3 ((Lk ns : List (Symbol 1)) ++ l)
        (ListBlank.cons 𝟙 (ListBlank.cons 𝟘 (ListBlank.cons 𝟙 (ListBlank.cons 𝟙 (R m.succ))))) := by
  refine (Lk_inc hn l _).trans ?_
  refine Machine.EvStep.step (step_right_mk' gB1 _ _) ?_
  refine Machine.EvStep.step (step_right_mk' gB0 _ _) ?_
  refine Machine.EvStep.step (step_right_mk' gC1 _ _) ?_
  refine Machine.EvStep.step (step_right_mk' gC1 _ _) ?_
  refine (R_inc_has0 hm _).trans ?_
  rw [headL_cons]
  refine Machine.EvStep.step (step_left_mk' gD1 _ _) ?_
  refine Machine.EvStep.step (step_left_mk' gA1 _ _) ?_
  refine Machine.EvStep.step (step_left_mk' gD1 _ _) ?_
  refine Machine.EvStep.step (step_right_mk' gA0 _ _) ?_
  refine Machine.EvStep.step (step_right_mk' gB0 _ _) ?_
  refine Machine.EvStep.step (step_right_mk' gC1 _ _) ?_
  refine Machine.EvStep.step (step_left_mk' gC0 _ _) ?_
  refine Machine.EvStep.step (step_left_mk' gA1 _ _) ?_
  refine Machine.EvStep.step (step_left_mk' gD1 _ _) ?_
  exact Machine.EvStep.step (step_left_head gA1 _ _) Machine.EvStep.refl

open Deciders.Skelet.FixedBin in
/-- Coq `LaR_inc`. -/
lemma LaR_inc {k : ℕ} (a : Symbol 1) {np ns : Bin k} (hn : Succ np ns) {m : PosNum} (hm : Has0 m)
    (l : side) :
    headL 3 ((Lk np : List (Symbol 1)) ++ l)
        (ListBlank.cons 𝟙 (ListBlank.cons 𝟘 (ListBlank.cons 𝟙 (ListBlank.cons a (R m)))))
      -[M]->* headL 3 ((Lk ns : List (Symbol 1)) ++ l)
        (ListBlank.cons 𝟙 (ListBlank.cons 𝟘 (ListBlank.cons 𝟙 (ListBlank.cons a (R m.succ))))) := by
  match a with
  | 0 => exact LaR_inc_zero hn hm l
  | 1 => exact LaR_inc_one hn hm l

open Deciders.Skelet.FixedBin in
/-- Coq `LaR_incs`.  Induction on the `Plus` proof. -/
lemma LaR_incs {k : ℕ} (a : Symbol 1) {u : ℕ} {np ns : Bin k} (hp : Plus u np ns) {m : PosNum}
    (hu : u ≤ b m) (l : side) :
    headL 3 ((Lk np : List (Symbol 1)) ++ l)
        (ListBlank.cons 𝟙 (ListBlank.cons 𝟘 (ListBlank.cons 𝟙 (ListBlank.cons a (R m)))))
      -[M]->* headL 3 ((Lk ns : List (Symbol 1)) ++ l)
        (ListBlank.cons 𝟙 (ListBlank.cons 𝟘 (ListBlank.cons 𝟙 (ListBlank.cons a (R (addN u m)))))) := by
  induction hp generalizing m with
  | zero n => simpa using Machine.EvStep.refl
  | @succ ucount bnp bmid bns s p ih =>
      have hbm : 0 < b m := by omega
      refine (LaR_inc a s (bgt0_has0 hbm) l).trans ?_
      have hbound : ucount ≤ b m.succ := by rw [b_succ hbm]; omega
      have key := ih (m := m.succ) hbound
      have hw : addN (ucount + 1) m = addN ucount m.succ :=
        Function.iterate_succ_apply PosNum.succ ucount m
      rw [hw]
      exact key

open Deciders.Skelet.FixedBin in
/-- Coq `LaR_max`. -/
lemma LaR_max {k : ℕ} (a : Symbol 1) {m : PosNum} (hm : 2 ^ k - 1 ≤ b m) (l : side) :
    headL 3 ((Lk (binMin k) : List (Symbol 1)) ++ l)
        (ListBlank.cons 𝟙 (ListBlank.cons 𝟘 (ListBlank.cons 𝟙 (ListBlank.cons a (R m)))))
      -[M]->* headL 3 ((Lk (binMax k) : List (Symbol 1)) ++ l)
        (ListBlank.cons 𝟙 (ListBlank.cons 𝟘 (ListBlank.cons 𝟙 (ListBlank.cons a (R (addN (2 ^ k - 1) m)))))) :=
  LaR_incs a (inc_to_max k) hm l

open Deciders.Skelet.FixedBin in
/-- Coq `eat_bin_max0`.  Induction on `k`. -/
lemma eat_bin_max0 (k : ℕ) {t : PosNum} (h : Has0 t) (l : side) :
    headL 3 ((Lk (binMax k) : List (Symbol 1)) ++
        ListBlank.cons 𝟘 (ListBlank.cons 𝟘 (ListBlank.cons 𝟙 (ListBlank.cons 𝟘 l)))) (R t)
      -[M]->* headL 3 l
        (ListBlank.cons 𝟙 (ListBlank.cons 𝟘 (ListBlank.cons 𝟙 (ListBlank.cons 𝟙 (R (pow4 k t.succ)))))) := by
  induction k generalizing t with
  | zero =>
      simp only [binMax, Lk, ListBlank.append_empty]
      exact eat_KI h l
  | succ k ih =>
      simp only [binMax, Lk, ListBlank.append_cons]
      refine (eat_LI _ t).trans ?_
      exact ih (Has0.bit1 (Has0.bit1 h))

open Deciders.Skelet.FixedBin in
/-- Coq `eat_bin_max1`.  Induction on `k`. -/
lemma eat_bin_max1 (k : ℕ) {t : PosNum} (h : Has0 t) (l : side) :
    headL 3 ((Lk (binMax k) : List (Symbol 1)) ++ ListBlank.cons 𝟙 (ListBlank.cons 𝟘 l)) (R t)
      -[M]->* headL 3 l (ListBlank.cons 𝟙 (ListBlank.cons 𝟘 (R (pow4 k t.succ)))) := by
  induction k generalizing t with
  | zero =>
      simp only [binMax, Lk, ListBlank.append_empty]
      exact eat_JI h l
  | succ k ih =>
      simp only [binMax, Lk, ListBlank.append_cons]
      refine (eat_LI _ t).trans ?_
      exact ih (Has0.bit1 (Has0.bit1 h))

/-- Coq `f`. -/
def f (m : PosNum) (a : Symbol 1) (k : ℕ) : PosNum :=
  if a = 0 then (addN (2 ^ k - 1) m).bit0.bit0 else (addN (2 ^ k - 1) m).bit1.bit0

/-- Coq `f1`. -/
def f1 (m : PosNum) (a : Symbol 1) (k : ℕ) : PosNum :=
  if a = 0 then (addN (2 ^ k - 1) m).bit0 else (addN (2 ^ k - 1) m).bit1

/-- Coq `f_as_f1`. -/
lemma f_as_f1 (m : PosNum) (a : Symbol 1) (k : ℕ) : f m a k = (f1 m a k).bit0 := by
  unfold f f1; split <;> rfl

/-- Coq `has0_f`. -/
lemma has0_f (m : PosNum) (a : Symbol 1) (k : ℕ) : Has0 (f m a k) := by
  unfold f; split <;> exact Has0.bit0 _

/-
Coq `f_lt`.
-/
lemma f_lt (m : PosNum) (a : Symbol 1) (k : ℕ) :
    ∃ x : PosNum, ((f m a k).succ : ℕ) = 4 * ((addN (2 ^ k - 1) m : PosNum) : ℕ) + (x : ℕ) ∧ (x : ℕ) ≤ 3 := by
  unfold f
  split
  · refine ⟨1, ?_, by decide⟩
    simp only [PosNum.cast_succ, PosNum.cast_bit0, PosNum.cast_one]
    omega
  · refine ⟨3, ?_, by decide⟩
    have h3 : ((3 : PosNum) : ℕ) = 3 := by decide
    simp only [PosNum.cast_succ, PosNum.cast_bit0, PosNum.cast_bit1, h3]
    omega

/-- Reinterpret the `1 0 1 a` prefix over `R (addN (2^k-1) m)` as `R (f m a k)`. -/
lemma R_f (m : PosNum) (a : Symbol 1) (k : ℕ) :
    ListBlank.cons 𝟙 (ListBlank.cons 𝟘 (ListBlank.cons 𝟙 (ListBlank.cons a (R (addN (2 ^ k - 1) m)))))
      = R (f m a k) := by
  match a with
  | 0 => rfl
  | 1 => rfl

open Deciders.Skelet.FixedBin in
/-- Coq `drop_KI`. -/
lemma drop_KI {k : ℕ} (a : Symbol 1) {m : PosNum} (hm : 2 ^ k - 1 ≤ b m) (l : side) :
    headL 3 ((Lk (binMin k) : List (Symbol 1)) ++
        ListBlank.cons 𝟘 (ListBlank.cons 𝟘 (ListBlank.cons 𝟙 (ListBlank.cons 𝟘 l))))
        (ListBlank.cons 𝟙 (ListBlank.cons 𝟘 (ListBlank.cons 𝟙 (ListBlank.cons a (R m)))))
      -[M]->* headL 3 l
        (ListBlank.cons 𝟙 (ListBlank.cons 𝟘 (ListBlank.cons 𝟙 (ListBlank.cons 𝟙 (R (pow4 k (f m a k).succ)))))) := by
  refine (LaR_max a hm _).trans ?_
  rw [R_f]
  exact eat_bin_max0 k (has0_f m a k) l

open Deciders.Skelet.FixedBin in
/-- Coq `drop_JI`. -/
lemma drop_JI {k : ℕ} (a : Symbol 1) {m : PosNum} (hm : 2 ^ k - 1 ≤ b m) (l : side) :
    headL 3 ((Lk (binMin k) : List (Symbol 1)) ++ ListBlank.cons 𝟙 (ListBlank.cons 𝟘 l))
        (ListBlank.cons 𝟙 (ListBlank.cons 𝟘 (ListBlank.cons 𝟙 (ListBlank.cons a (R m)))))
      -[M]->* headL 3 l (ListBlank.cons 𝟙 (ListBlank.cons 𝟘 (R (pow4 k (f m a k).succ)))) := by
  refine (LaR_max a hm _).trans ?_
  rw [R_f]
  exact eat_bin_max1 k (has0_f m a k) l

open Deciders.Skelet.FixedBin in
/-- Coq `prepare_K`. -/
lemma prepare_K (n : Num) (hn : 0 < (n : ℕ)) : ∃ (k : ℕ) (n' : Num),
    K n = (Lk (binMin k) : List (Symbol 1)) ++
        ListBlank.cons 𝟘 (ListBlank.cons 𝟘 (ListBlank.cons 𝟙 (ListBlank.cons 𝟘 (K n'))))
      ∧ (n : ℕ) = 2 ^ k + 2 ^ (k + 1) * (n' : ℕ) := by
  obtain ⟨p, rfl⟩ : ∃ p, n = Num.pos p := by
    cases n <;> aesop;
  induction p using PosNum.recOn <;> simp_all +decide [ pow_succ' ];
  · exists 0, 0;
  · rename_i p ih; use 0, Num.pos p; simp +decide [ *, pow_succ' ] ;
    exact ⟨ ListBlank.ext (congrFun rfl) , by ring ⟩;
  · rename_i p hp;
    obtain ⟨ k, n', hk, hn' ⟩ := hp; use k + 1, n'; simp_all +decide [ pow_succ', mul_assoc ] ;
    simp_all +decide [ K, K', binMin, Lk ] ; ring

open Deciders.Skelet.FixedBin in
/-- Coq `prepare_J`. -/
lemma prepare_J (k : ℕ) (n' : Num) :
    J (2 ^ k + 2 ^ (k + 1) * n') = (Lk (binMin k) : List (Symbol 1)) ++
        ListBlank.cons 𝟙 (ListBlank.cons 𝟘 (ListBlank.cons 𝟘 (ListBlank.cons 𝟘 (J n')))) := by
  induction' k with k ih generalizing n';
  · cases n' <;> simp +decide [ ListBlank.append ];
    rename_i p;
    -- By definition of `PosNum`, we know that `p.bit1` is equivalent to `1 + 2 * p`.
    have h_pos : p.bit1 = Num.succ (2 * Num.pos p) := by
      grind +suggestions;
    convert congr_arg ( fun x : Num => J x ) h_pos.symm using 1;
    simp +decide [ J, J' ];
    rw [ show ( Num.pos p + Num.pos p + 1 : Num ) = Num.pos ( p.bit1 ) from ?_ ];
    · cases p <;> rfl;
    · grind +suggestions;
  · -- By definition of $J$, we know that $J(2^{k+1} + 2^{k+2} n') = J(2(2^k + 2^{k+1} n'))$.
    have hJ_succ : J (2 ^ (k + 1) + 2 ^ (k + 2) * n') = J (2 * (2 ^ k + 2 ^ (k + 1) * n')) := by
      ring;
    rw [ hJ_succ, show J ( 2 * ( 2 ^ k + 2 ^ ( k + 1 ) * n' ) ) = ListBlank.cons 0 ( ListBlank.cons 0 ( ListBlank.cons 0 ( ListBlank.cons 0 ( J ( 2 ^ k + 2 ^ ( k + 1 ) * n' ) ) ) ) ) from ?_ ];
    · rw [ ih ];
      exact ListBlank.ext (congrFun rfl);
    · have hJ_def : ∀ p : PosNum, J (Num.pos p.bit0) = ListBlank.cons 0 (ListBlank.cons 0 (ListBlank.cons 0 (ListBlank.cons 0 (J (Num.pos p))))) := by
        intros p
        simp [J, J'];
      cases h : 2 ^ k + 2 ^ ( k + 1 ) * n' <;> simp_all +decide [ two_mul ];
      convert hJ_def _ using 2 ; ring!;
      exact Num.to_nat_inj.mp rfl

/-- Coq `reset_invariant`. -/
def reset_invariant (m : PosNum) : Prop :=
  2 ≤ (m : ℕ) ∧ ∃ (k : ℕ) (n' : ℕ), b m + 1 = 2 ^ k + 2 ^ (k + 1) * n' ∧ 2 ≤ n'

/-
Coq `step_reset0`.
-/
lemma step_reset0 (n : Num) (m : PosNum) (a : Symbol 1) (hinv : (n : ℕ) ≤ b m) (hpos : 0 < (n : ℕ)) :
    ∃ (n' : Num) (m' : PosNum),
      (E0 n a m -[M]->* E0 n' 1 m') ∧ (n' : ℕ) < (n : ℕ) ∧ (n' : ℕ) ≤ b m' ∧ reset_invariant m' := by
  obtain ⟨ k, n', hK, hn ⟩ := prepare_K n hpos;
  refine' ⟨ n', pow4 k ( f m a k |> PosNum.succ ), _, _, _, _ ⟩;
  · unfold E0; rw [ hK ] ; exact drop_KI a ( by omega ) ( K n' ) ;
  · nlinarith [ Nat.one_le_pow k 2 zero_lt_two, Nat.one_le_pow ( k + 1 ) 2 zero_lt_two ];
  · have hbt : b (addN (2^k - 1) m) = b m - (2^k - 1) := by
      apply b_add;
      grind;
    have hbf1 : b (f1 m a k) ≥ 2 * b (addN (2^k - 1) m) := by
      unfold f1; split_ifs <;> simp_all +decide [ b ] ;
    have hbm' : b (pow4 k (f m a k).succ) ≥ 2 * b (f1 m a k) := by
      rw [ b_pow4 ];
      rw [ show b ( f m a k |> PosNum.succ ) = b ( f1 m a k ) * 2 from ?_ ];
      · exact Nat.le_sub_one_of_lt ( by nlinarith only [ Nat.one_le_pow ( 2 * k ) 2 zero_lt_two, Nat.zero_le ( b ( f1 m a k ) ) ] );
      · rw [ show f m a k = ( f1 m a k ).bit0 from ?_, b_succ ];
        · exact Nat.sub_eq_of_eq_add <| by rw [ show b ( f1 m a k |> PosNum.bit0 ) = 2 * b ( f1 m a k ) + 1 from rfl ] ; ring;
        · exact Nat.succ_pos _;
        · exact f_as_f1 m a k;
    nlinarith [ Nat.sub_add_cancel ( show 1 ≤ 2 ^ k from Nat.one_le_pow _ _ ( by decide ) ), Nat.sub_add_cancel ( show 2 ^ k - 1 ≤ b m from by omega ), pow_pos ( show 0 < 2 by decide ) k, pow_succ' 2 k ];
  · refine' ⟨ _, 2 * k, b ( f1 m a k ), _, _ ⟩ <;> norm_num [ b_pow4 ];
    · have h_pow4_ge_two : ∀ k : ℕ, ∀ y : PosNum, 2 ≤ (y : ℕ) → 2 ≤ (pow4 k y : ℕ) := by
        intro k y hy; induction' k with k ih <;> simp_all +decide [ pow_succ', pow4 ] ;
        grind +suggestions;
      exact h_pow4_ge_two k _ ( by
        cases a ; simp +decide [ f ] );
    · rw [ b_succ ];
      · rw [ f_as_f1, b ] ;
        zify ; norm_num ; ring;
      · cases a ; simp +decide [ f ];
        split_ifs <;> simp +decide [ b ];
    · -- By definition of $f1$, we know that $b (f1 m a k) \geq 2 * b t$.
      have hbf1 : b (f1 m a k) ≥ 2 * b (addN (2^k - 1) m) := by
        unfold f1; split_ifs <;> simp_all +decide [ b ] ;
      grind +suggestions

end Deciders.Skelet.Skelet26
end Skelet26Inline

open TM.Table

namespace Deciders.BB5Table

inductive EntryDecider where
  | nGram : (history : ℕ) → (len : ℕ) → (bound : ℕ) → EntryDecider
  | nGramLRU : (len : ℕ) → (bound : ℕ) → EntryDecider
  | repWL : (len : ℕ) → (threshold : ℕ) → (maxT : ℕ) → (bound : ℕ) → EntryDecider
  | halt : (bound : ℕ) → EntryDecider
  | loop1 : (bound : ℕ) → EntryDecider
  | far : (states : ℕ) → (dfa : List (ℕ × ℕ)) → EntryDecider
  | wfar :
      (maxD : ℕ) →
      (leftStates : ℕ) → (left : List ((ℕ × Int) × (ℕ × Int))) →
      (rightStates : ℕ) → (right : List ((ℕ × Int) × (ℕ × Int))) →
      (bound : ℕ) → EntryDecider
  | sporadic : EntryDecider
  | unsupported : String → EntryDecider
deriving DecidableEq, Repr

abbrev Entry := String × EntryDecider
abbrev Table := Std.HashMap String EntryDecider

/-!
## Sporadic holdout machines

The Coq BB5 proof closes a handful of machines that no algorithmic decider in
the pipeline can handle — the "sporadic" holdouts — each with its own hand-built
non-halting argument.  We mirror that structure: every holdout is a concrete
machine paired with its own `…_nonHalting` theorem.

These theorems carry the real mathematical content and are still `sorry`.  But
unlike a single `∀ M, ¬M.halts` placeholder (which is *false* as stated, since
halting BB(5) machines exist), each is a *true* statement about one specific
machine — so discharging them is ordinary proof work, not a redesign.
-/

def sporadicMachine0 : Machine 4 1 := mach["1RB0LE_1RC1RB_1RD1LC_0LE0RB_---1LA"]

/-!
### Non-halting proof for `sporadicMachine0`

`1RB0LE_1RC1RB_1RD1LC_0LE0RB_---1LA` is a quadratic-growth counter.  It bounces
between a left edge (state `C` reading the leftmost blank) and a right edge,
adding one `1` to a left block and one `10` to a right `(10)^r` tail per visit.

We close it with a two-parameter family `F m r` (state `C`, left `1^m`, right
`1^(2m+r+4) 0 (10)^r`) that is closed under single "bounces": `F m (r+1)` reaches
`F (m+1) r`, and the carry `F m 0` reaches `F 0 (m+1)`.  Both are a *constant*
number of block sweeps, so the `ClosedSet` machinery supplies all the induction.
-/
namespace SM0
open Turing

abbrev M : Machine 4 1 := sporadicMachine0

-- Transition lemmas (A=0, B=1, C=2, D=3, E=4).
lemma gA0 : M.get 0 0 = .next 1 .right 1 := by decide
lemma gA1 : M.get 0 1 = .next 0 .left 4 := by decide
lemma gB0 : M.get 1 0 = .next 1 .right 2 := by decide
lemma gB1 : M.get 1 1 = .next 1 .right 1 := by decide
lemma gC0 : M.get 2 0 = .next 1 .right 3 := by decide
lemma gC1 : M.get 2 1 = .next 1 .left 2 := by decide
lemma gD1 : M.get 3 1 = .next 0 .right 1 := by decide
lemma gE1 : M.get 4 1 = .next 1 .left 0 := by decide
-- Blank-edge transitions (head reading the blank `default`).
lemma gA0d : M.get 0 default = .next 1 .right 1 := by decide
lemma gB0d : M.get 1 default = .next 1 .right 2 := by decide
lemma gC0d : M.get 2 default = .next 1 .right 3 := by decide
lemma gD0d : M.get 3 default = .next 0 .left 4 := by decide

/-- The `(10)^r` right-tail of the counter configuration (as a `ListBlank`). -/
def tp : ℕ → ListBlank (Symbol 1)
  | 0 => ∅
  | r + 1 => ListBlank.cons 1 (ListBlank.cons 0 (tp r))

/-- The counter family `F m r`: state C, left `1^m`, right `1^(2m+r+4) 0 (10)^r`. -/
def F (m r : ℕ) : Config 4 1 :=
  ⟨2, Tape.mk' (List.replicate m (1 : Symbol 1) ++ (∅ : ListBlank (Symbol 1)))
      (ListBlank.cons 0 (List.replicate (2 * m + r + 4) (1 : Symbol 1) ++ ListBlank.cons 0 (tp r)))⟩

/-- Abbreviation: `1^n` prepended to a `ListBlank`. -/
abbrev Bl (n : ℕ) (L : ListBlank (Symbol 1)) : ListBlank (Symbol 1) :=
  List.replicate n (1 : Symbol 1) ++ L

local notation "𝟙" => (1 : Symbol 1)
local notation "𝟘" => (0 : Symbol 1)

lemma cons_zero_empty : ListBlank.cons (0 : Symbol 1) ∅ = ∅ :=
  ListBlank.cons_default_empty

/-- The zigzag accumulator (with writes `1`, `0`) collapses to the `0 :: (10)^k` tail. -/
lemma zztp (k : ℕ) : zigzagAcc (1 : Symbol 1) 0 k ∅ = ListBlank.cons 0 (tp k) := by
  induction k with
  | zero => simp [zigzagAcc, tp, cons_zero_empty]
  | succ k ih => simp [zigzagAcc, tp, ih]

/-- One bounce: `F m (r+1)` reaches `F (m+1) r` (left edge → left edge). -/
lemma bounce (m r : ℕ) : F m (r + 1) -[M]->+ F (m + 1) r := by
  set N1 := 2 * m + r + 4 with hN1
  -- (a) C reads 0 → D
  have ha := step_right_mk' gC0 (Bl m ∅) (Bl (N1 + 1) (ListBlank.cons 𝟘 (tp (r + 1))))
  -- (b) D reads 1 → B
  have hb := step_right_mk' gD1 (ListBlank.cons 𝟙 (Bl m ∅)) (Bl N1 (ListBlank.cons 𝟘 (tp (r + 1))))
  -- (c) B sweeps right over 1^N1
  have hc := right_run gB1 N1 (ListBlank.cons 𝟘 (ListBlank.cons 𝟙 (Bl m ∅)))
      (ListBlank.cons 𝟘 (tp (r + 1)))
  -- (d) B reads 0 → C
  have hd := step_right_mk' gB0 (Bl N1 (ListBlank.cons 𝟘 (ListBlank.cons 𝟙 (Bl m ∅)))) (tp (r + 1))
  -- (e) C sweeps left over 1^(N1+1)
  have he := left_run gC1 (N1 + 1) (ListBlank.cons 𝟘 (ListBlank.cons 𝟙 (Bl m ∅)))
      (ListBlank.cons 𝟘 (tp r))
  -- (f) C reads 1 → C, lands on the new leftmost 0
  have hf := step_left_mk' (l₀ := 𝟘) gC1 (ListBlank.cons 𝟙 (Bl m ∅))
      (Bl (N1 + 1) (ListBlank.cons 𝟘 (tp r)))
  have chain :
      (⟨2, Tape.mk' (Bl m ∅)
          (ListBlank.cons 𝟘 (Bl (N1 + 1) (ListBlank.cons 𝟘 (tp (r + 1)))))⟩ : Config 4 1)
        -[M]{1 + 1 + N1 + 1 + (N1 + 1) + 1}->
      ⟨2, Tape.mk' (ListBlank.cons 𝟙 (Bl m ∅))
          (ListBlank.cons 𝟘 (ListBlank.cons 𝟙 (Bl (N1 + 1) (ListBlank.cons 𝟘 (tp r)))))⟩ :=
    (((((Machine.Multistep.single ha).trans (Machine.Multistep.single hb)).trans hc).trans
      (Machine.Multistep.single hd)).trans he).trans (Machine.Multistep.single hf)
  have hsrc : F m (r + 1) = (⟨2, Tape.mk' (Bl m ∅)
      (ListBlank.cons 𝟘 (Bl (N1 + 1) (ListBlank.cons 𝟘 (tp (r + 1)))))⟩ : Config 4 1) := by
    unfold F; rw [show 2 * m + (r + 1) + 4 = N1 + 1 by omega]
  have htgt : F (m + 1) r = (⟨2, Tape.mk' (ListBlank.cons 𝟙 (Bl m ∅))
      (ListBlank.cons 𝟘 (ListBlank.cons 𝟙 (Bl (N1 + 1) (ListBlank.cons 𝟘 (tp r)))))⟩
      : Config 4 1) := by
    unfold F; rw [show 2 * (m + 1) + r + 4 = N1 + 1 + 1 by omega]; rfl
  rw [hsrc, htgt]
  exact Machine.Progress.from_multistep' (by omega) chain

/-- The carry: `F m 0` reaches `F 0 (m+1)` (left edge → right edge → left edge). -/
lemma reset (m : ℕ) : F m 0 -[M]->+ F 0 (m + 1) := by
  -- (a) C reads 0 → D
  have ha := step_right_mk' gC0 (Bl m ∅) (Bl (2 * m + 4) (ListBlank.cons 𝟘 (tp 0)))
  -- (b) D reads 1 → B
  have hb := step_right_mk' gD1 (ListBlank.cons 𝟙 (Bl m ∅)) (Bl (2 * m + 3) (ListBlank.cons 𝟘 (tp 0)))
  -- (c) B sweeps right over 1^(2m+3) to the right edge
  have hc := right_run gB1 (2 * m + 3) (ListBlank.cons 𝟘 (ListBlank.cons 𝟙 (Bl m ∅)))
      (ListBlank.cons 𝟘 (tp 0))
  -- (d) B reads 0 (last separator) → C
  have hd := step_right_mk' gB0 (Bl (2 * m + 3) (ListBlank.cons 𝟘 (ListBlank.cons 𝟙 (Bl m ∅)))) (tp 0)
  -- (e) C reads blank → D
  have he := step_right_blank gC0d
      (ListBlank.cons 𝟙 (Bl (2 * m + 3) (ListBlank.cons 𝟘 (ListBlank.cons 𝟙 (Bl m ∅)))))
  -- (f) D reads blank → E, turning left
  have hf := step_left_blank (l₀ := 𝟙) gD0d
      (ListBlank.cons 𝟙 (Bl (2 * m + 3) (ListBlank.cons 𝟘 (ListBlank.cons 𝟙 (Bl m ∅)))))
  rw [cons_zero_empty] at hf
  -- (g) E/A zigzag left over 1^(2m+5), building (10) pattern; ends in A reading separator 0
  have hg := zigzag gE1 gA1 (m + 2) (0 : Symbol 1) (ListBlank.cons 𝟙 (Bl m ∅))
      (∅ : ListBlank (Symbol 1))
  -- (h) A reads 0 → B (turn around)
  have hh := step_right_mk' gA0 (ListBlank.cons 𝟙 (Bl m ∅))
      (ListBlank.cons 𝟙 (zigzagAcc 1 0 (m + 2) ∅))
  -- (i) B reads 1
  have hi := step_right_mk' gB1 (ListBlank.cons 𝟙 (ListBlank.cons 𝟙 (Bl m ∅)))
      (zigzagAcc 1 0 (m + 2) ∅)
  -- (j) B reads 0 → C
  have hj := step_right_mk' gB0 (ListBlank.cons 𝟙 (ListBlank.cons 𝟙 (ListBlank.cons 𝟙 (Bl m ∅))))
      (ListBlank.cons 𝟙 (zigzagAcc 1 0 (m + 1) ∅))
  -- (k) C sweeps left over 1^(m+4) to the far left
  have hk := left_run gC1 (m + 4) (∅ : ListBlank (Symbol 1)) (zigzagAcc 1 0 (m + 1) ∅)
  -- (l) C reads 1 → C, lands on the new leftmost 0
  have hl := step_left_edge gC1 (Bl (m + 4) (zigzagAcc 1 0 (m + 1) ∅))
  have chain := ((((((((((Machine.Multistep.single ha).trans
      (Machine.Multistep.single hb)).trans hc).trans (Machine.Multistep.single hd)).trans
      (Machine.Multistep.single he)).trans (Machine.Multistep.single hf)).trans hg).trans
      (Machine.Multistep.single hh)).trans (Machine.Multistep.single hi)).trans
      (Machine.Multistep.single hj)).trans hk |>.trans (Machine.Multistep.single hl)
  have htgt : (⟨2, Tape.mk' ∅
      (ListBlank.cons 𝟘 (ListBlank.cons 𝟙 (Bl (m + 4) (zigzagAcc 1 0 (m + 1) ∅))))⟩ : Config 4 1)
      = F 0 (m + 1) := by
    unfold F; rw [show 2 * 0 + (m + 1) + 4 = m + 5 by omega, ← zztp]; rfl
  rw [← htgt]
  exact Machine.Progress.from_multistep' (by omega) chain

/-- The initial configuration reaches the base case `F 0 0` of the counter family.
Fourteen explicit steps from the all-blank tape. -/
lemma enters : init -[M]->* F 0 0 := by
  have s0 := step_right_blank gA0d (∅ : ListBlank (Symbol 1))
  have s1 := step_right_blank gB0d (ListBlank.cons 𝟙 ∅)
  have s2 := step_right_blank gC0d (ListBlank.cons 𝟙 (ListBlank.cons 𝟙 ∅))
  have s3 := step_left_blank (l₀ := 𝟙) gD0d (ListBlank.cons 𝟙 (ListBlank.cons 𝟙 ∅))
  rw [cons_zero_empty] at s3
  have s4 := step_left_mk' (l₀ := 𝟙) gE1 (ListBlank.cons 𝟙 ∅) (∅ : ListBlank (Symbol 1))
  have s5 := step_left_mk' (l₀ := 𝟙) gA1 (∅ : ListBlank (Symbol 1)) (ListBlank.cons 𝟙 ∅)
  have s6 := step_left_edge gE1 (ListBlank.cons 𝟘 (ListBlank.cons 𝟙 ∅))
  have s7 := step_right_mk' gA0 (∅ : ListBlank (Symbol 1))
      (ListBlank.cons 𝟙 (ListBlank.cons 𝟘 (ListBlank.cons 𝟙 ∅)))
  have s8 := step_right_mk' gB1 (ListBlank.cons 𝟙 ∅) (ListBlank.cons 𝟘 (ListBlank.cons 𝟙 ∅))
  have s9 := step_right_mk' gB0 (ListBlank.cons 𝟙 (ListBlank.cons 𝟙 ∅)) (ListBlank.cons 𝟙 ∅)
  have s10 := step_left_mk' (l₀ := 𝟙) gC1 (ListBlank.cons 𝟙 (ListBlank.cons 𝟙 ∅))
      (∅ : ListBlank (Symbol 1))
  have s11 := step_left_mk' (l₀ := 𝟙) gC1 (ListBlank.cons 𝟙 ∅) (ListBlank.cons 𝟙 ∅)
  have s12 := step_left_mk' (l₀ := 𝟙) gC1 (∅ : ListBlank (Symbol 1))
      (ListBlank.cons 𝟙 (ListBlank.cons 𝟙 ∅))
  have s13 := step_left_edge gC1 (ListBlank.cons 𝟙 (ListBlank.cons 𝟙 (ListBlank.cons 𝟙 ∅)))
  have chain := ((((((((((((Machine.Multistep.single s0).trans
      (Machine.Multistep.single s1)).trans (Machine.Multistep.single s2)).trans
      (Machine.Multistep.single s3)).trans (Machine.Multistep.single s4)).trans
      (Machine.Multistep.single s5)).trans (Machine.Multistep.single s6)).trans
      (Machine.Multistep.single s7)).trans (Machine.Multistep.single s8)).trans
      (Machine.Multistep.single s9)).trans (Machine.Multistep.single s10)).trans
      (Machine.Multistep.single s11)).trans (Machine.Multistep.single s12) |>.trans
      (Machine.Multistep.single s13)
  have htgt : F 0 0 = (⟨2, Tape.mk' ∅ (ListBlank.cons 𝟘 (Bl 4 ∅))⟩ : Config 4 1) := by
    unfold F; simp only [tp, cons_zero_empty]; rfl
  have key : (⟨0, Tape.mk' ∅ ∅⟩ : Config 4 1) -[M]{14}-> F 0 0 := by
    rw [htgt]; exact chain
  exact Machine.Multistep.to_evstep key

theorem nonHalting : ¬ M.halts init := by
  have cs : ClosedSet M (fun C => ∃ m r, C = F m r) init := by
    refine ⟨?_, ?_⟩
    · rintro ⟨C, m, r, rfl⟩
      cases r with
      | zero => exact ⟨⟨F 0 (m + 1), 0, m + 1, rfl⟩, reset m⟩
      | succ r => exact ⟨⟨F (m + 1) r, m + 1, r, rfl⟩, bounce m r⟩
    · exact ⟨⟨F 0 0, 0, 0, rfl⟩, enters⟩
  exact cs.nonHalting

end SM0

theorem sporadicMachine0_nonHalting : ¬ sporadicMachine0.halts init := SM0.nonHalting

def sporadicMachine1 : Machine 4 1 := mach["1RB1RA_1RC1LB_0LD0RA_1RA1LE_---0LD"]

/-!
### Non-halting proof for `sporadicMachine1`

`1RB1RA_1RC1LB_0LD0RA_1RA1LE_---0LD` is another quadratic-growth counter.  It
maintains a configuration `F a r` (state `B`, left `1^a`, right
`0 1^(2a+r+3) (01)^r`) closed under two kinds of "bounces":

* a *subbounce* `F a (r+1) → F (a+1) r` consumes one `(01)` pair from the right
  tail and grows the central `1`-block by one, and
* a *finish* `F a 0 → F 0 (a+1)` runs the head to the right edge, plants two new
  cells, then zig-zags left rebuilding the `(01)`-tail.

Both are a *constant* number of block sweeps, so `ClosedSet` supplies the
induction.  (Structurally this mirrors `SM0`: subbounce ≈ bounce, finish ≈
reset.)
-/
namespace SM1
open Turing

abbrev M : Machine 4 1 := sporadicMachine1

-- Transition lemmas (A=0, B=1, C=2, D=3, E=4).
lemma gA0 : M.get 0 0 = .next 1 .right 1 := by decide
lemma gA1 : M.get 0 1 = .next 1 .right 0 := by decide
lemma gB0 : M.get 1 0 = .next 1 .right 2 := by decide
lemma gB1 : M.get 1 1 = .next 1 .left 1 := by decide
lemma gC1 : M.get 2 1 = .next 0 .right 0 := by decide
lemma gD0 : M.get 3 0 = .next 1 .right 0 := by decide
lemma gD1 : M.get 3 1 = .next 1 .left 4 := by decide
lemma gE1 : M.get 4 1 = .next 0 .left 3 := by decide
-- Blank-edge transitions (head reading the blank `default`).
lemma gA0d : M.get 0 default = .next 1 .right 1 := by decide
lemma gB0d : M.get 1 default = .next 1 .right 2 := by decide
lemma gC0d : M.get 2 default = .next 0 .left 3 := by decide

local notation "𝟙" => (1 : Symbol 1)
local notation "𝟘" => (0 : Symbol 1)

/-- The `(01)^r` right-tail of the counter configuration (as a `ListBlank`). -/
def tl : ℕ → ListBlank (Symbol 1)
  | 0 => ∅
  | r + 1 => ListBlank.cons 0 (ListBlank.cons 1 (tl r))

/-- Abbreviation: `1^n` prepended to a `ListBlank`. -/
abbrev Bl (n : ℕ) (L : ListBlank (Symbol 1)) : ListBlank (Symbol 1) :=
  List.replicate n (1 : Symbol 1) ++ L

/-- The counter family `F a r`: state B, left `1^a`, right `0 1^(2a+r+3) (01)^r`. -/
def F (a r : ℕ) : Config 4 1 :=
  ⟨1, Tape.mk' (Bl a ∅)
      (ListBlank.cons 0 (Bl (2 * a + r + 3) (tl r)))⟩

lemma cons_zero_empty : ListBlank.cons (0 : Symbol 1) ∅ = ∅ :=
  ListBlank.cons_default_empty

/-- The zigzag accumulator (with writes `0`, `1`) collapses to the `0 :: (01)^k` tail. -/
lemma ztl (k : ℕ) :
    ListBlank.cons (0 : Symbol 1) (zigzagAcc (0 : Symbol 1) 1 k (ListBlank.cons 1 ∅)) = tl (k + 1) := by
  induction k with
  | zero => simp [zigzagAcc, tl]
  | succ k ih => simp [zigzagAcc, tl, ih]

/-- One subbounce: `F a (r+1)` reaches `F (a+1) r` (consume one `(01)` pair). -/
lemma subbounce (a r : ℕ) : F a (r + 1) -[M]->+ F (a + 1) r := by
  set N := 2 * a + r + 3 with hN
  -- (a) B reads 0 → C
  have ha := step_right_mk' gB0 (Bl a ∅) (Bl (N + 1) (ListBlank.cons 𝟘 (ListBlank.cons 𝟙 (tl r))))
  -- (b) C reads 1 → A, planting a 0 in the block
  have hb := step_right_mk' gC1 (ListBlank.cons 𝟙 (Bl a ∅)) (Bl N (ListBlank.cons 𝟘 (ListBlank.cons 𝟙 (tl r))))
  -- (c) A sweeps right over the rest of the block
  have hc := right_run gA1 N (ListBlank.cons 𝟘 (ListBlank.cons 𝟙 (Bl a ∅))) (ListBlank.cons 𝟘 (ListBlank.cons 𝟙 (tl r)))
  -- (d) A reads the separator 0 → B
  have hd := step_right_mk' gA0 (Bl N (ListBlank.cons 𝟘 (ListBlank.cons 𝟙 (Bl a ∅)))) (ListBlank.cons 𝟙 (tl r))
  -- (e) B sweeps left back over the block
  have he := left_run gB1 (N + 1) (ListBlank.cons 𝟘 (ListBlank.cons 𝟙 (Bl a ∅))) (tl r)
  -- (f) B reads 1 → B, landing on the planted 0
  have hf := step_left_mk' (l₀ := 𝟘) gB1 (ListBlank.cons 𝟙 (Bl a ∅)) (Bl (N + 1) (tl r))
  have chain :
      (⟨1, Tape.mk' (Bl a ∅)
          (ListBlank.cons 𝟘 (Bl (N + 1) (ListBlank.cons 𝟘 (ListBlank.cons 𝟙 (tl r)))))⟩ : Config 4 1)
        -[M]{1 + 1 + N + 1 + (N + 1) + 1}->
      ⟨1, Tape.mk' (ListBlank.cons 𝟙 (Bl a ∅))
          (ListBlank.cons 𝟘 (ListBlank.cons 𝟙 (Bl (N + 1) (tl r))))⟩ :=
    (((((Machine.Multistep.single ha).trans (Machine.Multistep.single hb)).trans hc).trans
      (Machine.Multistep.single hd)).trans he).trans (Machine.Multistep.single hf)
  have hsrc : F a (r + 1) = (⟨1, Tape.mk' (Bl a ∅)
      (ListBlank.cons 𝟘 (Bl (N + 1) (ListBlank.cons 𝟘 (ListBlank.cons 𝟙 (tl r)))))⟩ : Config 4 1) := by
    unfold F; rw [show 2 * a + (r + 1) + 3 = N + 1 by omega]; rfl
  have htgt : F (a + 1) r = (⟨1, Tape.mk' (ListBlank.cons 𝟙 (Bl a ∅))
      (ListBlank.cons 𝟘 (ListBlank.cons 𝟙 (Bl (N + 1) (tl r))))⟩ : Config 4 1) := by
    unfold F; rw [show 2 * (a + 1) + r + 3 = N + 2 by omega]; rfl
  rw [hsrc, htgt]
  exact Machine.Progress.from_multistep' (by omega) chain

/-- The finish: `F a 0` reaches `F 0 (a+1)` (right edge → zigzag back to left edge). -/
lemma finish (a : ℕ) : F a 0 -[M]->+ F 0 (a + 1) := by
  -- (a) B reads 0 → C
  have ha := step_right_mk' gB0 (Bl a ∅) (Bl (2 * a + 3) (∅ : ListBlank (Symbol 1)))
  -- (b) C reads 1 → A, planting a 0
  have hb := step_right_mk' gC1 (ListBlank.cons 𝟙 (Bl a ∅)) (Bl (2 * a + 2) (∅ : ListBlank (Symbol 1)))
  -- (c) A sweeps right over the rest of the block to the right edge
  have hc := right_run gA1 (2 * a + 2) (ListBlank.cons 𝟘 (ListBlank.cons 𝟙 (Bl a ∅)))
      (∅ : ListBlank (Symbol 1))
  -- (d) A reads blank → B
  have hd := step_right_blank gA0d (Bl (2 * a + 2) (ListBlank.cons 𝟘 (ListBlank.cons 𝟙 (Bl a ∅))))
  -- (e) B reads blank → C
  have he := step_right_blank gB0d
      (ListBlank.cons 𝟙 (Bl (2 * a + 2) (ListBlank.cons 𝟘 (ListBlank.cons 𝟙 (Bl a ∅)))))
  -- (f) C reads blank → D, turning left
  have hf := step_left_blank (l₀ := 𝟙) gC0d
      (ListBlank.cons 𝟙 (Bl (2 * a + 2) (ListBlank.cons 𝟘 (ListBlank.cons 𝟙 (Bl a ∅)))))
  rw [cons_zero_empty] at hf
  -- (g) D reads 1 → E (first zigzag step, peeled off to make the block odd)
  have hg := step_left_mk' (l₀ := 𝟙) gD1 (Bl (2 * a + 2) (ListBlank.cons 𝟘 (ListBlank.cons 𝟙 (Bl a ∅))))
      (∅ : ListBlank (Symbol 1))
  -- (h) E/D zigzag left over 1^(2a+3), building the (01) pattern; ends in D reading the planted 0
  have hh := zigzag gE1 gD1 (a + 1) 𝟘 (ListBlank.cons 𝟙 (Bl a ∅)) (ListBlank.cons 𝟙 ∅)
  -- (i) D reads the planted 0 → A
  have hi := step_right_mk' gD0 (ListBlank.cons 𝟙 (Bl a ∅))
      (ListBlank.cons 𝟘 (zigzagAcc 𝟘 1 (a + 1) (ListBlank.cons 𝟙 ∅)))
  -- (j) A reads 0 → B
  have hj := step_right_mk' gA0 (ListBlank.cons 𝟙 (ListBlank.cons 𝟙 (Bl a ∅)))
      (zigzagAcc 𝟘 1 (a + 1) (ListBlank.cons 𝟙 ∅))
  -- (k) B sweeps left over the new 1-block
  have hk := left_run gB1 (a + 3) (∅ : ListBlank (Symbol 1))
      (ListBlank.cons 𝟘 (zigzagAcc 𝟘 1 a (ListBlank.cons 𝟙 ∅)))
  -- (l) B reads 1 → B, landing on the new leftmost 0
  have hl := step_left_edge gB1 (Bl (a + 3) (ListBlank.cons 𝟘 (zigzagAcc 𝟘 1 a (ListBlank.cons 𝟙 ∅))))
  have chain := ((((((((((Machine.Multistep.single ha).trans
      (Machine.Multistep.single hb)).trans hc).trans (Machine.Multistep.single hd)).trans
      (Machine.Multistep.single he)).trans (Machine.Multistep.single hf)).trans
      (Machine.Multistep.single hg)).trans hh).trans (Machine.Multistep.single hi)).trans
      (Machine.Multistep.single hj)).trans hk |>.trans (Machine.Multistep.single hl)
  have htgt : (⟨1, Tape.mk' (∅ : ListBlank (Symbol 1))
      (ListBlank.cons 𝟘 (ListBlank.cons 𝟙 (Bl (a + 3) (ListBlank.cons 𝟘 (zigzagAcc 𝟘 1 a (ListBlank.cons 𝟙 ∅))))))⟩
      : Config 4 1) = F 0 (a + 1) := by
    unfold F; rw [show 2 * 0 + (a + 1) + 3 = a + 4 by omega, ← ztl a]; rfl
  rw [← htgt]
  exact Machine.Progress.from_multistep' (by omega) chain

/-- The initial configuration reaches the base case `F 0 0` of the counter family.
Ten explicit steps from the all-blank tape. -/
lemma enters : init -[M]->* F 0 0 := by
  have s0 := step_right_blank gA0d (∅ : ListBlank (Symbol 1))
  have s1 := step_right_blank gB0d (ListBlank.cons 𝟙 ∅)
  have s2 := step_left_blank (l₀ := 𝟙) gC0d (ListBlank.cons 𝟙 ∅)
  rw [cons_zero_empty] at s2
  have s3 := step_left_mk' (l₀ := 𝟙) gD1 (∅ : ListBlank (Symbol 1)) (∅ : ListBlank (Symbol 1))
  have s4 := step_left_edge gE1 (ListBlank.cons 𝟙 ∅)
  have s5 := step_right_mk' gD0 (∅ : ListBlank (Symbol 1)) (ListBlank.cons 𝟘 (ListBlank.cons 𝟙 ∅))
  have s6 := step_right_mk' gA0 (ListBlank.cons 𝟙 ∅) (ListBlank.cons 𝟙 ∅)
  have s7 := step_left_mk' (l₀ := 𝟙) gB1 (ListBlank.cons 𝟙 ∅) (∅ : ListBlank (Symbol 1))
  have s8 := step_left_mk' (l₀ := 𝟙) gB1 (∅ : ListBlank (Symbol 1)) (ListBlank.cons 𝟙 ∅)
  have s9 := step_left_edge gB1 (ListBlank.cons 𝟙 (ListBlank.cons 𝟙 ∅))
  have chain :=
    ((((((((Machine.Multistep.single s0).trans (Machine.Multistep.single s1)).trans
      (Machine.Multistep.single s2)).trans (Machine.Multistep.single s3)).trans
      (Machine.Multistep.single s4)).trans (Machine.Multistep.single s5)).trans
      (Machine.Multistep.single s6)).trans (Machine.Multistep.single s7)).trans
      (Machine.Multistep.single s8) |>.trans (Machine.Multistep.single s9)
  have htgt : F 0 0 = (⟨1, Tape.mk' (∅ : ListBlank (Symbol 1))
      (ListBlank.cons 𝟘 (ListBlank.cons 𝟙 (ListBlank.cons 𝟙 (ListBlank.cons 𝟙 ∅))))⟩ : Config 4 1) := by
    unfold F; simp only [tl]; rfl
  have key : (⟨0, Tape.mk' ∅ ∅⟩ : Config 4 1) -[M]{10}-> F 0 0 := by
    rw [htgt]; exact chain
  exact Machine.Multistep.to_evstep key

theorem nonHalting : ¬ M.halts init := by
  have cs : ClosedSet M (fun C => ∃ a r, C = F a r) init := by
    refine ⟨?_, ?_⟩
    · rintro ⟨C, a, r, rfl⟩
      cases r with
      | zero => exact ⟨⟨F 0 (a + 1), 0, a + 1, rfl⟩, finish a⟩
      | succ r => exact ⟨⟨F (a + 1) r, a + 1, r, rfl⟩, subbounce a r⟩
    · exact ⟨⟨F 0 0, 0, 0, rfl⟩, enters⟩
  exact cs.nonHalting

end SM1

theorem sporadicMachine1_nonHalting : ¬ sporadicMachine1.halts init := SM1.nonHalting

def sporadicMachine2 : Machine 4 1 := mach["1RB1RE_1LC1RB_0RA0LD_1LB1LD_---0RA"]

/-!
### Non-halting proof for `sporadicMachine2`

`1RB1RE_1LC1RB_0RA0LD_1LB1LD_---0RA` is a quadratic counter whose left side
carries a *comb* of `(01)` pairs.  We track the family `K q j` (state B reading a
`0`, left `1^(2q+j+1) (01)^j`, right `1^q`) closed under:

* a *subbounce* `K q (j+1) → K (q+1) j` that dives left, absorbs the first comb
  pair into the central block, and bounces back (only `left_run`/`right_run`), and
* a *reset* `K q 0 → K 0 (q+1)` that runs to the left edge and rebuilds a fresh
  comb of `q+1` pairs on the way back right (an A/E zig-zag).
-/
namespace SM2
open Turing

abbrev M : Machine 4 1 := sporadicMachine2

-- Transition lemmas (A=0, B=1, C=2, D=3, E=4).
lemma gA0 : M.get 0 0 = .next 1 .right 1 := by decide
lemma gA1 : M.get 0 1 = .next 1 .right 4 := by decide
lemma gB0 : M.get 1 0 = .next 1 .left 2 := by decide
lemma gB1 : M.get 1 1 = .next 1 .right 1 := by decide
lemma gC0 : M.get 2 0 = .next 0 .right 0 := by decide
lemma gC1 : M.get 2 1 = .next 0 .left 3 := by decide
lemma gD0 : M.get 3 0 = .next 1 .left 1 := by decide
lemma gD1 : M.get 3 1 = .next 1 .left 3 := by decide
lemma gE1 : M.get 4 1 = .next 0 .right 0 := by decide
-- Blank-edge transitions (head reading the blank `default`).
lemma gA0d : M.get 0 default = .next 1 .right 1 := by decide
lemma gB0d : M.get 1 default = .next 1 .left 2 := by decide

local notation "𝟙" => (1 : Symbol 1)
local notation "𝟘" => (0 : Symbol 1)

/-- Abbreviation: `1^n` prepended to a `ListBlank`. -/
abbrev Bl (n : ℕ) (L : ListBlank (Symbol 1)) : ListBlank (Symbol 1) :=
  List.replicate n (1 : Symbol 1) ++ L

/-- The `(01)^j` comb carried on the left of the counter (adjacent-to-head first). -/
def comb : ℕ → ListBlank (Symbol 1)
  | 0 => ∅
  | j + 1 => ListBlank.cons 0 (ListBlank.cons 1 (comb j))

/-- The counter family `K q j`: state B reading `0`, left `1^(2q+j+1) (01)^j`, right `1^q`. -/
def K (q j : ℕ) : Config 4 1 :=
  ⟨1, Tape.mk' (Bl (2 * q + j + 1) (comb j)) (ListBlank.cons 0 (Bl q ∅))⟩

lemma cons_zero_empty : ListBlank.cons (0 : Symbol 1) ∅ = ∅ :=
  ListBlank.cons_default_empty

/-- One subbounce: `K q (j+1)` reaches `K (q+1) j` (absorb one comb pair). -/
lemma subbounce (q j : ℕ) : K q (j + 1) -[M]->+ K (q + 1) j := by
  -- (a) B reads 0 → C, diving left into the block
  have ha := step_left_mk' (l₀ := 𝟙) gB0 (Bl (2 * q + j + 1) (comb (j + 1))) (Bl q ∅)
  -- (b) C reads 1 → D, planting a 0
  have hb := step_left_mk' (l₀ := 𝟙) gC1 (Bl (2 * q + j) (comb (j + 1))) (ListBlank.cons 𝟙 (Bl q ∅))
  -- (c) D sweeps left over the block interior
  have hc := left_run gD1 (2 * q + j) (comb (j + 1))
      (ListBlank.cons 𝟘 (ListBlank.cons 𝟙 (Bl q ∅)))
  -- (d) D reads 1 → D, stepping onto the first comb 0
  have hd := step_left_mk' (l₀ := 𝟘) gD1 (ListBlank.cons 𝟙 (comb j))
      (Bl (2 * q + j) (ListBlank.cons 𝟘 (ListBlank.cons 𝟙 (Bl q ∅))))
  -- (e) D reads 0 → B, planting a 1 (merging the comb pair into the block)
  have he := step_left_mk' (l₀ := 𝟙) gD0 (comb j)
      (ListBlank.cons 𝟙 (Bl (2 * q + j) (ListBlank.cons 𝟘 (ListBlank.cons 𝟙 (Bl q ∅)))))
  -- (f) B sweeps right back to the planted 0
  have hf := right_run gB1 (2 * q + j + 3) (comb j) (ListBlank.cons 𝟘 (ListBlank.cons 𝟙 (Bl q ∅)))
  have chain :
      (⟨1, Tape.mk' (Bl (2 * q + j + 2) (comb (j + 1))) (ListBlank.cons 𝟘 (Bl q ∅))⟩ : Config 4 1)
        -[M]{1 + 1 + (2 * q + j) + 1 + 1 + (2 * q + j + 3)}->
      ⟨1, Tape.mk' (Bl (2 * q + j + 3) (comb j)) (ListBlank.cons 𝟘 (ListBlank.cons 𝟙 (Bl q ∅)))⟩ :=
    (((((Machine.Multistep.single ha).trans (Machine.Multistep.single hb)).trans hc).trans
      (Machine.Multistep.single hd)).trans (Machine.Multistep.single he)).trans hf
  have hsrc : K q (j + 1) = (⟨1, Tape.mk' (Bl (2 * q + j + 2) (comb (j + 1)))
      (ListBlank.cons 𝟘 (Bl q ∅))⟩ : Config 4 1) := by
    unfold K; rw [show 2 * q + (j + 1) + 1 = 2 * q + j + 2 by omega]
  have htgt : K (q + 1) j = (⟨1, Tape.mk' (Bl (2 * q + j + 3) (comb j))
      (ListBlank.cons 𝟘 (ListBlank.cons 𝟙 (Bl q ∅)))⟩ : Config 4 1) := by
    unfold K; rw [show 2 * (q + 1) + j + 1 = 2 * q + j + 3 by omega]; rfl
  rw [hsrc, htgt]
  exact Machine.Progress.from_multistep' (by omega) chain

/-- The rightward zig-zag accumulator collapses to the `(01)^n` comb. -/
lemma combeq (n : ℕ) : zigzagAcc (1 : Symbol 1) 0 n ∅ = comb n := by
  induction n with
  | zero => rfl
  | succ n ih => simp only [zigzagAcc, comb, ih]

lemma Bl_zero (L : ListBlank (Symbol 1)) : Bl 0 L = L := rfl

lemma Bl_cons (n : ℕ) (L : ListBlank (Symbol 1)) :
    Bl n (ListBlank.cons 1 L) = Bl (n + 1) L := (replicate_succ_append 1 n L).symm

/-- The reset: `K (m+1) 0` reaches `K 0 (m+2)` (run to the left edge, then rebuild
a fresh comb on the way back right). -/
lemma reset (m : ℕ) : K (m + 1) 0 -[M]->+ K 0 (m + 2) := by
  -- (a) B reads 0 → C, diving left
  have ha := step_left_mk' (l₀ := 𝟙) gB0 (Bl (2 * m + 2) (∅ : ListBlank (Symbol 1))) (Bl (m + 1) ∅)
  -- (b) C reads 1 → D, planting a 0
  have hb := step_left_mk' (l₀ := 𝟙) gC1 (Bl (2 * m + 1) (∅ : ListBlank (Symbol 1)))
      (ListBlank.cons 𝟙 (Bl (m + 1) ∅))
  -- (c) D sweeps left over the block interior
  have hc := left_run gD1 (2 * m + 1) (∅ : ListBlank (Symbol 1))
      (ListBlank.cons 𝟘 (ListBlank.cons 𝟙 (Bl (m + 1) ∅)))
  -- (d) D reads the last 1 at the left edge → fresh blank
  have hd := step_left_edge gD1 (Bl (2 * m + 1) (ListBlank.cons 𝟘 (ListBlank.cons 𝟙 (Bl (m + 1) ∅))))
  -- (e) D reads blank → B, planting a 1
  have he := step_left_edge gD0
      (ListBlank.cons 𝟙 (Bl (2 * m + 1) (ListBlank.cons 𝟘 (ListBlank.cons 𝟙 (Bl (m + 1) ∅)))))
  -- (f) B reads blank → C
  have hf := step_left_edge gB0
      (ListBlank.cons 𝟙 (ListBlank.cons 𝟙 (Bl (2 * m + 1) (ListBlank.cons 𝟘 (ListBlank.cons 𝟙 (Bl (m + 1) ∅))))))
  -- (g) C reads blank → A
  have hg := step_right_mk' gC0 (∅ : ListBlank (Symbol 1))
      (ListBlank.cons 𝟙 (ListBlank.cons 𝟙 (ListBlank.cons 𝟙 (Bl (2 * m + 1) (ListBlank.cons 𝟘 (ListBlank.cons 𝟙 (Bl (m + 1) ∅)))))))
  -- (h) A/E zig-zag right over the even block, building the new comb on the left
  have hi := zigzag_pairs_right gA1 gE1 (m + 2) (ListBlank.cons 𝟘 ∅)
      (ListBlank.cons 𝟘 (ListBlank.cons 𝟙 (Bl (m + 1) ∅)))
  -- (i) A reads the separator 0 → B
  have hj := step_right_mk' gA0 (zigzagAcc 𝟙 0 (m + 2) (ListBlank.cons 𝟘 ∅)) (ListBlank.cons 𝟙 (Bl (m + 1) ∅))
  -- (j) B sweeps right over the second block to the right edge
  have hk := right_run gB1 (m + 2) (ListBlank.cons 𝟙 (zigzagAcc 𝟙 0 (m + 2) (ListBlank.cons 𝟘 ∅)))
      (∅ : ListBlank (Symbol 1))
  have chain := ((((((((Machine.Multistep.single ha).trans
      (Machine.Multistep.single hb)).trans hc).trans (Machine.Multistep.single hd)).trans
      (Machine.Multistep.single he)).trans (Machine.Multistep.single hf)).trans
      (Machine.Multistep.single hg)).trans hi).trans (Machine.Multistep.single hj) |>.trans hk
  have htgt : (⟨1, Tape.mk' (Bl (m + 2) (ListBlank.cons 𝟙 (zigzagAcc 𝟙 0 (m + 2) (ListBlank.cons 𝟘 ∅))))
      (∅ : ListBlank (Symbol 1))⟩ : Config 4 1) = K 0 (m + 2) := by
    unfold K
    simp only [cons_zero_empty, combeq, Bl_cons, Bl_zero,
      show 2 * 0 + (m + 2) + 1 = m + 3 by omega]
  rw [← htgt]
  exact Machine.Progress.from_multistep' (by omega) chain

/-- The initial configuration reaches the base case `K 0 1` of the counter family.
Ten explicit steps from the all-blank tape. -/
lemma enters : init -[M]->* K 0 1 := by
  have s0 := step_right_blank gA0d (∅ : ListBlank (Symbol 1))
  have s1 := step_left_blank (l₀ := 𝟙) gB0d (∅ : ListBlank (Symbol 1))
  have s2 := step_left_edge gC1 (ListBlank.cons 𝟙 ∅)
  have s3 := step_left_edge gD0 (ListBlank.cons 𝟘 (ListBlank.cons 𝟙 ∅))
  have s4 := step_left_edge gB0 (ListBlank.cons 𝟙 (ListBlank.cons 𝟘 (ListBlank.cons 𝟙 ∅)))
  have s5 := step_right_mk' gC0 (∅ : ListBlank (Symbol 1))
      (ListBlank.cons 𝟙 (ListBlank.cons 𝟙 (ListBlank.cons 𝟘 (ListBlank.cons 𝟙 ∅))))
  have s6 := step_right_mk' gA1 (ListBlank.cons 𝟘 ∅) (ListBlank.cons 𝟙 (ListBlank.cons 𝟘 (ListBlank.cons 𝟙 ∅)))
  have s7 := step_right_mk' gE1 (ListBlank.cons 𝟙 (ListBlank.cons 𝟘 ∅)) (ListBlank.cons 𝟘 (ListBlank.cons 𝟙 ∅))
  have s8 := step_right_mk' gA0 (ListBlank.cons 𝟘 (ListBlank.cons 𝟙 (ListBlank.cons 𝟘 ∅))) (ListBlank.cons 𝟙 ∅)
  have s9 := step_right_mk' gB1 (ListBlank.cons 𝟙 (ListBlank.cons 𝟘 (ListBlank.cons 𝟙 (ListBlank.cons 𝟘 ∅))))
      (∅ : ListBlank (Symbol 1))
  have chain := ((((((((Machine.Multistep.single s0).trans
      (Machine.Multistep.single s1)).trans (Machine.Multistep.single s2)).trans
      (Machine.Multistep.single s3)).trans (Machine.Multistep.single s4)).trans
      (Machine.Multistep.single s5)).trans (Machine.Multistep.single s6)).trans
      (Machine.Multistep.single s7)).trans (Machine.Multistep.single s8) |>.trans
      (Machine.Multistep.single s9)
  have htgt : K 0 1 = (⟨1, Tape.mk' (ListBlank.cons 𝟙 (ListBlank.cons 𝟙 (ListBlank.cons 𝟘
      (ListBlank.cons 𝟙 (ListBlank.cons 𝟘 ∅))))) (∅ : ListBlank (Symbol 1))⟩ : Config 4 1) := by
    unfold K; simp only [comb, cons_zero_empty, Bl_zero]; rfl
  rw [htgt]
  exact Machine.Multistep.to_evstep chain

theorem nonHalting : ¬ M.halts init := by
  have cs : ClosedSet M (fun C => ∃ q j, q + j ≥ 1 ∧ C = K q j) init := by
    refine ⟨?_, ?_⟩
    · rintro ⟨C, q, j, hqj, rfl⟩
      cases j with
      | zero =>
        obtain ⟨q', rfl⟩ : ∃ q', q = q' + 1 := ⟨q - 1, by omega⟩
        exact ⟨⟨K 0 (q' + 2), 0, q' + 2, by omega, rfl⟩, reset q'⟩
      | succ j => exact ⟨⟨K (q + 1) j, q + 1, j, by omega, rfl⟩, subbounce q j⟩
    · exact ⟨⟨K 0 1, 0, 1, by omega, rfl⟩, enters⟩
  exact cs.nonHalting

end SM2

theorem sporadicMachine2_nonHalting : ¬ sporadicMachine2.halts init := SM2.nonHalting

def sporadicMachine3 : Machine 4 1 := mach["1RB1LA_0LC0RE_---1LD_1RA0LC_1RA1RE"]

/-!
### Non-halting proof for `sporadicMachine3`

`1RB1LA_0LC0RE_---1LD_1RA0LC_1RA1RE` is a quadratic counter with the same
two-parameter shape as `SM1`, but anchored on state `A` reading a `0`.  Family
`F a r` = state A reading 0, left `1^a`, right `0 1^(2a+r+2) (01)^r`, closed under
a `subbounce` `F a (r+1) → F (a+1) r` and a `finish` `F a 0 → F 0 (a+1)`.  The
finish zig-zag here is odd-length, so the `zigzag` lemma applies directly.
-/
namespace SM3
open Turing

abbrev M : Machine 4 1 := sporadicMachine3

-- Transition lemmas (A=0, B=1, C=2, D=3, E=4).
lemma gA0 : M.get 0 0 = .next 1 .right 1 := by decide
lemma gA1 : M.get 0 1 = .next 1 .left 0 := by decide
lemma gB1 : M.get 1 1 = .next 0 .right 4 := by decide
lemma gC1 : M.get 2 1 = .next 1 .left 3 := by decide
lemma gD0 : M.get 3 0 = .next 1 .right 0 := by decide
lemma gD1 : M.get 3 1 = .next 0 .left 2 := by decide
lemma gE0 : M.get 4 0 = .next 1 .right 0 := by decide
lemma gE1 : M.get 4 1 = .next 1 .right 4 := by decide
-- Blank-edge transitions (head reading the blank `default`).
lemma gA0d : M.get 0 default = .next 1 .right 1 := by decide
lemma gB0d : M.get 1 default = .next 0 .left 2 := by decide
lemma gE0d : M.get 4 default = .next 1 .right 0 := by decide

local notation "𝟙" => (1 : Symbol 1)
local notation "𝟘" => (0 : Symbol 1)

/-- Abbreviation: `1^n` prepended to a `ListBlank`. -/
abbrev Bl (n : ℕ) (L : ListBlank (Symbol 1)) : ListBlank (Symbol 1) :=
  List.replicate n (1 : Symbol 1) ++ L

/-- The `(01)^r` comb (adjacent-to-head first). -/
def tl : ℕ → ListBlank (Symbol 1)
  | 0 => ∅
  | r + 1 => ListBlank.cons 0 (ListBlank.cons 1 (tl r))

/-- The counter family `F a r`: state A reading 0, left `1^a`, right `0 1^(2a+r+2) (01)^r`. -/
def F (a r : ℕ) : Config 4 1 :=
  ⟨0, Tape.mk' (Bl a ∅) (ListBlank.cons 0 (Bl (2 * a + r + 2) (tl r)))⟩

lemma cons_zero_empty : ListBlank.cons (0 : Symbol 1) ∅ = ∅ :=
  ListBlank.cons_default_empty

/-- The zig-zag accumulator collapses to the `(01)^n` comb. -/
lemma ztl (n : ℕ) : zigzagAcc (1 : Symbol 1) 0 n ∅ = tl n := by
  induction n with
  | zero => rfl
  | succ n ih => simp only [zigzagAcc, tl, ih]

/-- One subbounce: `F a (r+1)` reaches `F (a+1) r`. -/
lemma subbounce (a r : ℕ) : F a (r + 1) -[M]->+ F (a + 1) r := by
  set N := 2 * a + r + 2 with hN
  have ha := step_right_mk' gA0 (Bl a ∅) (Bl (N + 1) (ListBlank.cons 𝟘 (ListBlank.cons 𝟙 (tl r))))
  have hb := step_right_mk' gB1 (ListBlank.cons 𝟙 (Bl a ∅)) (Bl N (ListBlank.cons 𝟘 (ListBlank.cons 𝟙 (tl r))))
  have hc := right_run gE1 N (ListBlank.cons 𝟘 (ListBlank.cons 𝟙 (Bl a ∅))) (ListBlank.cons 𝟘 (ListBlank.cons 𝟙 (tl r)))
  have hd := step_right_mk' gE0 (Bl N (ListBlank.cons 𝟘 (ListBlank.cons 𝟙 (Bl a ∅)))) (ListBlank.cons 𝟙 (tl r))
  have he := left_run gA1 (N + 1) (ListBlank.cons 𝟘 (ListBlank.cons 𝟙 (Bl a ∅))) (tl r)
  have hf := step_left_mk' (l₀ := 𝟘) gA1 (ListBlank.cons 𝟙 (Bl a ∅)) (Bl (N + 1) (tl r))
  have chain :
      (⟨0, Tape.mk' (Bl a ∅)
          (ListBlank.cons 𝟘 (Bl (N + 1) (ListBlank.cons 𝟘 (ListBlank.cons 𝟙 (tl r)))))⟩ : Config 4 1)
        -[M]{1 + 1 + N + 1 + (N + 1) + 1}->
      ⟨0, Tape.mk' (ListBlank.cons 𝟙 (Bl a ∅))
          (ListBlank.cons 𝟘 (ListBlank.cons 𝟙 (Bl (N + 1) (tl r))))⟩ :=
    (((((Machine.Multistep.single ha).trans (Machine.Multistep.single hb)).trans hc).trans
      (Machine.Multistep.single hd)).trans he).trans (Machine.Multistep.single hf)
  have hsrc : F a (r + 1) = (⟨0, Tape.mk' (Bl a ∅)
      (ListBlank.cons 𝟘 (Bl (N + 1) (ListBlank.cons 𝟘 (ListBlank.cons 𝟙 (tl r)))))⟩ : Config 4 1) := by
    unfold F; rw [show 2 * a + (r + 1) + 2 = N + 1 by omega]; rfl
  have htgt : F (a + 1) r = (⟨0, Tape.mk' (ListBlank.cons 𝟙 (Bl a ∅))
      (ListBlank.cons 𝟘 (ListBlank.cons 𝟙 (Bl (N + 1) (tl r))))⟩ : Config 4 1) := by
    unfold F; rw [show 2 * (a + 1) + r + 2 = N + 2 by omega]; rfl
  rw [hsrc, htgt]
  exact Machine.Progress.from_multistep' (by omega) chain

/-- The finish: `F a 0` reaches `F 0 (a+1)`. -/
lemma finish (a : ℕ) : F a 0 -[M]->+ F 0 (a + 1) := by
  have ha := step_right_mk' gA0 (Bl a ∅) (Bl (2 * a + 2) (∅ : ListBlank (Symbol 1)))
  have hb := step_right_mk' gB1 (ListBlank.cons 𝟙 (Bl a ∅)) (Bl (2 * a + 1) (∅ : ListBlank (Symbol 1)))
  have hc := right_run gE1 (2 * a + 1) (ListBlank.cons 𝟘 (ListBlank.cons 𝟙 (Bl a ∅))) (∅ : ListBlank (Symbol 1))
  have hd := step_right_blank gE0d (Bl (2 * a + 1) (ListBlank.cons 𝟘 (ListBlank.cons 𝟙 (Bl a ∅))))
  have he := step_right_blank gA0d
      (ListBlank.cons 𝟙 (Bl (2 * a + 1) (ListBlank.cons 𝟘 (ListBlank.cons 𝟙 (Bl a ∅)))))
  have hf := step_left_blank (l₀ := 𝟙) gB0d
      (ListBlank.cons 𝟙 (Bl (2 * a + 1) (ListBlank.cons 𝟘 (ListBlank.cons 𝟙 (Bl a ∅)))))
  rw [cons_zero_empty] at hf
  have hg := zigzag gC1 gD1 (a + 1) 𝟘 (ListBlank.cons 𝟙 (Bl a ∅)) (∅ : ListBlank (Symbol 1))
  have hh := step_right_mk' gD0 (ListBlank.cons 𝟙 (Bl a ∅)) (ListBlank.cons 𝟙 (zigzagAcc 𝟙 0 (a + 1) ∅))
  have hi := left_run gA1 (a + 2) (∅ : ListBlank (Symbol 1)) (ListBlank.cons 𝟘 (ListBlank.cons 𝟙 (zigzagAcc 𝟙 0 a ∅)))
  have hj := step_left_edge gA1 (Bl (a + 2) (ListBlank.cons 𝟘 (ListBlank.cons 𝟙 (zigzagAcc 𝟙 0 a ∅))))
  have chain := ((((((((Machine.Multistep.single ha).trans
      (Machine.Multistep.single hb)).trans hc).trans (Machine.Multistep.single hd)).trans
      (Machine.Multistep.single he)).trans (Machine.Multistep.single hf)).trans hg).trans
      (Machine.Multistep.single hh)).trans hi |>.trans (Machine.Multistep.single hj)
  have htgt : (⟨0, Tape.mk' (∅ : ListBlank (Symbol 1))
      (ListBlank.cons 𝟘 (ListBlank.cons 𝟙 (Bl (a + 2) (ListBlank.cons 𝟘 (ListBlank.cons 𝟙 (zigzagAcc 𝟙 0 a ∅))))))⟩
      : Config 4 1) = F 0 (a + 1) := by
    unfold F; rw [show 2 * 0 + (a + 1) + 2 = a + 3 by omega, ztl a]; rfl
  rw [← htgt]
  exact Machine.Progress.from_multistep' (by omega) chain

/-- The initial configuration reaches the base case `F 0 0`. Six explicit steps. -/
lemma enters : init -[M]->* F 0 0 := by
  have s0 := step_right_blank gA0d (∅ : ListBlank (Symbol 1))
  have s1 := step_left_blank (l₀ := 𝟙) gB0d (∅ : ListBlank (Symbol 1))
  have s2 := step_left_edge gC1 (ListBlank.cons 𝟘 ∅)
  have s3 := step_right_mk' gD0 (∅ : ListBlank (Symbol 1)) (ListBlank.cons 𝟙 (ListBlank.cons 𝟘 ∅))
  have s4 := step_left_mk' (l₀ := 𝟙) gA1 (∅ : ListBlank (Symbol 1)) (ListBlank.cons 𝟘 ∅)
  have s5 := step_left_edge gA1 (ListBlank.cons 𝟙 (ListBlank.cons 𝟘 ∅))
  have chain := (((((Machine.Multistep.single s0).trans (Machine.Multistep.single s1)).trans
      (Machine.Multistep.single s2)).trans (Machine.Multistep.single s3)).trans
      (Machine.Multistep.single s4)) |>.trans (Machine.Multistep.single s5)
  have htgt : F 0 0 = (⟨0, Tape.mk' (∅ : ListBlank (Symbol 1))
      (ListBlank.cons 𝟘 (ListBlank.cons 𝟙 (ListBlank.cons 𝟙 (ListBlank.cons 𝟘 ∅))))⟩ : Config 4 1) := by
    unfold F; simp only [tl, cons_zero_empty]; rfl
  rw [htgt]
  exact Machine.Multistep.to_evstep chain

theorem nonHalting : ¬ M.halts init := by
  have cs : ClosedSet M (fun C => ∃ a r, C = F a r) init := by
    refine ⟨?_, ?_⟩
    · rintro ⟨C, a, r, rfl⟩
      cases r with
      | zero => exact ⟨⟨F 0 (a + 1), 0, a + 1, rfl⟩, finish a⟩
      | succ r => exact ⟨⟨F (a + 1) r, a + 1, r, rfl⟩, subbounce a r⟩
    · exact ⟨⟨F 0 0, 0, 0, rfl⟩, enters⟩
  exact cs.nonHalting

end SM3

theorem sporadicMachine3_nonHalting : ¬ sporadicMachine3.halts init := SM3.nonHalting

def sporadicMachine4 : Machine 4 1 := mach["1RB1LA_0LC0RE_---1LD_1LA0LC_1RA1RE"]

/-!
### Non-halting proof for `sporadicMachine4`

Identical to `SM3` except `D` reading `0` moves *left* (`1LA`) instead of right.
Same family `F a r` = state A reading 0, left `1^a`, right `0 1^(2a+r+2) (01)^r`; the
`subbounce` is literally the same, and the `finish` differs only in the post-zig-zag
turn (one left step instead of a right step + longer sweep).
-/
namespace SM4
open Turing

abbrev M : Machine 4 1 := sporadicMachine4

lemma gA0 : M.get 0 0 = .next 1 .right 1 := by decide
lemma gA1 : M.get 0 1 = .next 1 .left 0 := by decide
lemma gB1 : M.get 1 1 = .next 0 .right 4 := by decide
lemma gC1 : M.get 2 1 = .next 1 .left 3 := by decide
lemma gD0 : M.get 3 0 = .next 1 .left 0 := by decide
lemma gD1 : M.get 3 1 = .next 0 .left 2 := by decide
lemma gE0 : M.get 4 0 = .next 1 .right 0 := by decide
lemma gE1 : M.get 4 1 = .next 1 .right 4 := by decide
lemma gA0d : M.get 0 default = .next 1 .right 1 := by decide
lemma gB0d : M.get 1 default = .next 0 .left 2 := by decide
lemma gE0d : M.get 4 default = .next 1 .right 0 := by decide

local notation "𝟙" => (1 : Symbol 1)
local notation "𝟘" => (0 : Symbol 1)

abbrev Bl (n : ℕ) (L : ListBlank (Symbol 1)) : ListBlank (Symbol 1) :=
  List.replicate n (1 : Symbol 1) ++ L

def tl : ℕ → ListBlank (Symbol 1)
  | 0 => ∅
  | r + 1 => ListBlank.cons 0 (ListBlank.cons 1 (tl r))

def F (a r : ℕ) : Config 4 1 :=
  ⟨0, Tape.mk' (Bl a ∅) (ListBlank.cons 0 (Bl (2 * a + r + 2) (tl r)))⟩

lemma cons_zero_empty : ListBlank.cons (0 : Symbol 1) ∅ = ∅ :=
  ListBlank.cons_default_empty

lemma ztl (n : ℕ) : zigzagAcc (1 : Symbol 1) 0 n ∅ = tl n := by
  induction n with
  | zero => rfl
  | succ n ih => simp only [zigzagAcc, tl, ih]

lemma Bl_cons (n : ℕ) (L : ListBlank (Symbol 1)) :
    Bl n (ListBlank.cons 1 L) = Bl (n + 1) L := (replicate_succ_append 1 n L).symm

/-- One subbounce: `F a (r+1)` reaches `F (a+1) r` (same as SM3). -/
lemma subbounce (a r : ℕ) : F a (r + 1) -[M]->+ F (a + 1) r := by
  set N := 2 * a + r + 2 with hN
  have ha := step_right_mk' gA0 (Bl a ∅) (Bl (N + 1) (ListBlank.cons 𝟘 (ListBlank.cons 𝟙 (tl r))))
  have hb := step_right_mk' gB1 (ListBlank.cons 𝟙 (Bl a ∅)) (Bl N (ListBlank.cons 𝟘 (ListBlank.cons 𝟙 (tl r))))
  have hc := right_run gE1 N (ListBlank.cons 𝟘 (ListBlank.cons 𝟙 (Bl a ∅))) (ListBlank.cons 𝟘 (ListBlank.cons 𝟙 (tl r)))
  have hd := step_right_mk' gE0 (Bl N (ListBlank.cons 𝟘 (ListBlank.cons 𝟙 (Bl a ∅)))) (ListBlank.cons 𝟙 (tl r))
  have he := left_run gA1 (N + 1) (ListBlank.cons 𝟘 (ListBlank.cons 𝟙 (Bl a ∅))) (tl r)
  have hf := step_left_mk' (l₀ := 𝟘) gA1 (ListBlank.cons 𝟙 (Bl a ∅)) (Bl (N + 1) (tl r))
  have chain :
      (⟨0, Tape.mk' (Bl a ∅)
          (ListBlank.cons 𝟘 (Bl (N + 1) (ListBlank.cons 𝟘 (ListBlank.cons 𝟙 (tl r)))))⟩ : Config 4 1)
        -[M]{1 + 1 + N + 1 + (N + 1) + 1}->
      ⟨0, Tape.mk' (ListBlank.cons 𝟙 (Bl a ∅))
          (ListBlank.cons 𝟘 (ListBlank.cons 𝟙 (Bl (N + 1) (tl r))))⟩ :=
    (((((Machine.Multistep.single ha).trans (Machine.Multistep.single hb)).trans hc).trans
      (Machine.Multistep.single hd)).trans he).trans (Machine.Multistep.single hf)
  have hsrc : F a (r + 1) = (⟨0, Tape.mk' (Bl a ∅)
      (ListBlank.cons 𝟘 (Bl (N + 1) (ListBlank.cons 𝟘 (ListBlank.cons 𝟙 (tl r)))))⟩ : Config 4 1) := by
    unfold F; rw [show 2 * a + (r + 1) + 2 = N + 1 by omega]; rfl
  have htgt : F (a + 1) r = (⟨0, Tape.mk' (ListBlank.cons 𝟙 (Bl a ∅))
      (ListBlank.cons 𝟘 (ListBlank.cons 𝟙 (Bl (N + 1) (tl r))))⟩ : Config 4 1) := by
    unfold F; rw [show 2 * (a + 1) + r + 2 = N + 2 by omega]; rfl
  rw [hsrc, htgt]
  exact Machine.Progress.from_multistep' (by omega) chain

/-- The finish: `F a 0` reaches `F 0 (a+1)`. -/
lemma finish (a : ℕ) : F a 0 -[M]->+ F 0 (a + 1) := by
  have ha := step_right_mk' gA0 (Bl a ∅) (Bl (2 * a + 2) (∅ : ListBlank (Symbol 1)))
  have hb := step_right_mk' gB1 (ListBlank.cons 𝟙 (Bl a ∅)) (Bl (2 * a + 1) (∅ : ListBlank (Symbol 1)))
  have hc := right_run gE1 (2 * a + 1) (ListBlank.cons 𝟘 (ListBlank.cons 𝟙 (Bl a ∅))) (∅ : ListBlank (Symbol 1))
  have hd := step_right_blank gE0d (Bl (2 * a + 1) (ListBlank.cons 𝟘 (ListBlank.cons 𝟙 (Bl a ∅))))
  have he := step_right_blank gA0d
      (ListBlank.cons 𝟙 (Bl (2 * a + 1) (ListBlank.cons 𝟘 (ListBlank.cons 𝟙 (Bl a ∅)))))
  have hf := step_left_blank (l₀ := 𝟙) gB0d
      (ListBlank.cons 𝟙 (Bl (2 * a + 1) (ListBlank.cons 𝟘 (ListBlank.cons 𝟙 (Bl a ∅)))))
  rw [cons_zero_empty] at hf
  have hg := zigzag gC1 gD1 (a + 1) 𝟘 (ListBlank.cons 𝟙 (Bl a ∅)) (∅ : ListBlank (Symbol 1))
  have hh := step_left_mk' (l₀ := 𝟙) gD0 (Bl a ∅) (ListBlank.cons 𝟙 (zigzagAcc 𝟙 0 (a + 1) ∅))
  have hi := left_run gA1 a (∅ : ListBlank (Symbol 1)) (ListBlank.cons 𝟙 (ListBlank.cons 𝟙 (zigzagAcc 𝟙 0 (a + 1) ∅)))
  have hj := step_left_edge gA1 (Bl a (ListBlank.cons 𝟙 (ListBlank.cons 𝟙 (zigzagAcc 𝟙 0 (a + 1) ∅))))
  have chain := ((((((((Machine.Multistep.single ha).trans
      (Machine.Multistep.single hb)).trans hc).trans (Machine.Multistep.single hd)).trans
      (Machine.Multistep.single he)).trans (Machine.Multistep.single hf)).trans hg).trans
      (Machine.Multistep.single hh)).trans hi |>.trans (Machine.Multistep.single hj)
  have htgt : (⟨0, Tape.mk' (∅ : ListBlank (Symbol 1))
      (ListBlank.cons 𝟘 (ListBlank.cons 𝟙 (Bl a (ListBlank.cons 𝟙 (ListBlank.cons 𝟙 (zigzagAcc 𝟙 0 (a + 1) ∅))))))⟩
      : Config 4 1) = F 0 (a + 1) := by
    unfold F; rw [show 2 * 0 + (a + 1) + 2 = a + 3 by omega, ztl (a + 1), Bl_cons, Bl_cons]; rfl
  rw [← htgt]
  exact Machine.Progress.from_multistep' (by omega) chain

/-- The initial configuration reaches `F 0 0`. Four explicit steps. -/
lemma enters : init -[M]->* F 0 0 := by
  have s0 := step_right_blank gA0d (∅ : ListBlank (Symbol 1))
  have s1 := step_left_blank (l₀ := 𝟙) gB0d (∅ : ListBlank (Symbol 1))
  have s2 := step_left_edge gC1 (ListBlank.cons 𝟘 ∅)
  have s3 := step_left_edge gD0 (ListBlank.cons 𝟙 (ListBlank.cons 𝟘 ∅))
  have chain := (((Machine.Multistep.single s0).trans (Machine.Multistep.single s1)).trans
      (Machine.Multistep.single s2)) |>.trans (Machine.Multistep.single s3)
  have htgt : F 0 0 = (⟨0, Tape.mk' (∅ : ListBlank (Symbol 1))
      (ListBlank.cons 𝟘 (ListBlank.cons 𝟙 (ListBlank.cons 𝟙 (ListBlank.cons 𝟘 ∅))))⟩ : Config 4 1) := by
    unfold F; simp only [tl, cons_zero_empty]; rfl
  rw [htgt]
  exact Machine.Multistep.to_evstep chain

theorem nonHalting : ¬ M.halts init := by
  have cs : ClosedSet M (fun C => ∃ a r, C = F a r) init := by
    refine ⟨?_, ?_⟩
    · rintro ⟨C, a, r, rfl⟩
      cases r with
      | zero => exact ⟨⟨F 0 (a + 1), 0, a + 1, rfl⟩, finish a⟩
      | succ r => exact ⟨⟨F (a + 1) r, a + 1, r, rfl⟩, subbounce a r⟩
    · exact ⟨⟨F 0 0, 0, 0, rfl⟩, enters⟩
  exact cs.nonHalting

end SM4

theorem sporadicMachine4_nonHalting : ¬ sporadicMachine4.halts init := SM4.nonHalting

def sporadicMachine5 : Machine 4 1 := mach["1RB1RD_1LC0RC_1RA1LD_0RE0LB_---1RC"]
theorem sporadicMachine5_nonHalting : ¬ sporadicMachine5.halts init := by
  sorry

def sporadicMachine6 : Machine 4 1 := mach["1RB0RA_0LC1RA_1RE1LD_1LC0LD_---0RB"]
/-!
### Non-halting proof for `sporadicMachine6` (Skelet #10 — fully proven)

`1RB0RA_0LC1RA_1RE1LD_1LC0LD_---0RB` is a Fibonacci-rate *multi-digit counter* (a
genuine BB(5) sporadic holdout that no pipeline decider handles).  This is a
faithful Lean port of the Coq `BusyCoq/Skelet10.v` proof (sligocki's analysis):
the counter value lives in a *Zeckendorf digit string* `Dorf`, the configuration
`Dcfg n` advances by exactly one increment per macro-step
(`incr_D : Dcfg n -[M]->+ Dcfg (incr n)`), and the family `{Dcfg n}` is closed
under progress and reached from `init`, so `ClosedSet` closes the machine.  The
two block sweeps `incr_left`/`incr_right` and `incr_D`'s five-way case split
(mirroring the Coq `destruct`) are all discharged — no `sorry`.
-/
namespace SM6
open Turing

abbrev M : Machine 4 1 := sporadicMachine6

-- Transitions (A=0,B=1,C=2,D=3,E=4)
lemma gA0 : M.get 0 0 = .next 1 .right 1 := by decide
lemma gA1 : M.get 0 1 = .next 0 .right 0 := by decide
lemma gB0 : M.get 1 0 = .next 0 .left 2 := by decide
lemma gB1 : M.get 1 1 = .next 1 .right 0 := by decide
lemma gC0 : M.get 2 0 = .next 1 .right 4 := by decide
lemma gC1 : M.get 2 1 = .next 1 .left 3 := by decide
lemma gD0 : M.get 3 0 = .next 1 .left 2 := by decide
lemma gD1 : M.get 3 1 = .next 0 .left 3 := by decide
lemma gE1 : M.get 4 1 = .next 0 .right 1 := by decide
-- blank-edge
lemma gA0d : M.get 0 default = .next 1 .right 1 := by decide
lemma gB0d : M.get 1 default = .next 0 .left 2 := by decide

local notation "𝟙" => (1 : Symbol 1)
local notation "𝟘" => (0 : Symbol 1)

@[simp] lemma cons_zero_empty : ListBlank.cons (0 : Symbol 1) ∅ = ∅ := ListBlank.cons_default_empty

/-!
### Non-halting proof for `sporadicMachine6` via a Zeckendorf counter

Port of the Coq `BusyCoq/Skelet10.v` argument (sligocki's Skelet #10 analysis).
`1RB0RA_0LC1RA_1RE1LD_1LC0LD_---0RB` is a Fibonacci-rate counter whose value is
carried in a *Zeckendorf digit string* `Dorf`.  The configuration `Dcfg n`
advances by one counter increment per macro-step,
`Dcfg n -[M]->+ Dcfg (incr n)`, and the family `{Dcfg n}` is closed under
progress and reached from `init` — so `ClosedSet` closes the machine.
-/

/-- Zeckendorf digit string (Coq `dorf`): `zO` = digit `0`, `zIO` = digit `10`. -/
inductive Dorf where
  | zend : Dorf
  | zO : Dorf → Dorf
  | zIO : Dorf → Dorf

open Dorf

/-- The Fibonacci "prepend a leading 1" carry rewrite `zI` (Coq `zI`). -/
def zI : Dorf → Dorf
  | zend => zIO zend
  | zO n => zIO n
  | zIO n => zO (zO (zI n))

/-- Increment of the Zeckendorf counter (Coq `incr`). -/
def incr : Dorf → Dorf
  | zend => zIO zend
  | zO n => zI n
  | zIO n => zO (zI n)

/-- Right-side counter tape `Z` (head-nearest first). -/
def Zs : Dorf → ListBlank (Symbol 1)
  | zend => ∅
  | zO n => ListBlank.cons 𝟘 (Zs n)
  | zIO n => ListBlank.cons 𝟙 (ListBlank.cons 𝟘 (Zs n))

/-- Left-side accumulator `T` (head-nearest first); the Coq `<[…]` literal
reverses, so `zO ↦ 0 0` and `zIO ↦ 0 1 0 1`. -/
def Ts : Dorf → ListBlank (Symbol 1)
  | zend => ∅
  | zO n => ListBlank.cons 𝟘 (ListBlank.cons 𝟘 (Ts n))
  | zIO n => ListBlank.cons 𝟘 (ListBlank.cons 𝟙 (ListBlank.cons 𝟘 (ListBlank.cons 𝟙 (Ts n))))

/-- Left-side counter `L` (Coq `L`); `zIO` carries an extra `0 1` over `T`. -/
def Ls : Dorf → ListBlank (Symbol 1)
  | zend => ∅
  | zO n => Ts n
  | zIO n => ListBlank.cons 𝟘 (ListBlank.cons 𝟙 (Ts n))

/-- Head-on-left directed configuration (Coq `l <{{q}} r`): the head reads the
top of `L`, so the underlying tape is `mk' L.tail (L.head :: R)`. -/
def headL (q : Label 4) (L R : ListBlank (Symbol 1)) : Config 4 1 :=
  ⟨q, Tape.mk' L.tail (ListBlank.cons L.head R)⟩

@[simp] lemma headL_cons (q : Label 4) (a : Symbol 1) (L R : ListBlank (Symbol 1)) :
    headL q (ListBlank.cons a L) R = ⟨q, Tape.mk' L (ListBlank.cons a R)⟩ := by
  simp [headL]

lemma headL_empty (q : Label 4) (R : ListBlank (Symbol 1)) :
    headL q ∅ R = ⟨q, Tape.mk' ∅ (ListBlank.cons 𝟘 R)⟩ := rfl

/-- A leftward step with the left side abstract, landing in `headL` form
(the general form of `step_left_mk'`). -/
lemma step_left_head {q q' : Label 4} {a b : Symbol 1}
    (h : M.get q a = .next b .left q') (L R : ListBlank (Symbol 1)) :
    (⟨q, Tape.mk' L (ListBlank.cons a R)⟩ : Config 4 1) -[M]-> headL q' L (ListBlank.cons b R) := by
  refine Machine.step.some' h ?_ ?_
  · simp
  · simp [Tape.write_mk', Tape.move_left_mk']

/-- The complete-behaviour configuration `D n` (Coq Skelet10 `D`). -/
def Dcfg (n : Dorf) : Config 4 1 := headL 3 (Ls n) (Zs (incr n))

/-- Right-counter increment sweep (Coq `incr_right`): with the head entering the
right counter from the left in state `B`, the Zeckendorf carry `zI` is applied
and the head returns to the left of the block in state `D`. -/
lemma incr_right : ∀ (n : Dorf) (l : ListBlank (Symbol 1)),
    (⟨1, Tape.mk' (ListBlank.cons 𝟙 l) (Zs n)⟩ : Config 4 1) -[M]->* headL 3 l (Zs (zI n))
  | zend, l => by
      have sB := step_left_blank (l₀ := 𝟙) gB0d l
      have sC := step_left_head gC1 l (∅ : ListBlank (Symbol 1))
      simp only [cons_zero_empty] at sB
      simp only [Zs, zI, cons_zero_empty]
      exact Machine.EvStep.step sB (Machine.EvStep.step sC Machine.EvStep.refl)
  | zO n, l => by
      have sB := step_left_mk' (l₀ := 𝟙) gB0 l (Zs n)
      have sC := step_left_head gC1 l (ListBlank.cons 𝟘 (Zs n))
      simp only [Zs, zI]
      exact Machine.EvStep.step sB (Machine.EvStep.step sC Machine.EvStep.refl)
  | zIO n, l => by
      have sB := step_right_mk' gB1 (ListBlank.cons 𝟙 l) (ListBlank.cons 𝟘 (Zs n))
      have sA := step_right_mk' gA0 (ListBlank.cons 𝟙 (ListBlank.cons 𝟙 l)) (Zs n)
      have ih := incr_right n (ListBlank.cons 𝟙 (ListBlank.cons 𝟙 l))
      have sD1 := step_left_mk' (l₀ := 𝟙) gD1 l (Zs (zI n))
      have sD2 := step_left_head gD1 l (ListBlank.cons 𝟘 (Zs (zI n)))
      simp only [headL_cons] at ih
      simp only [Zs, zI]
      exact Machine.EvStep.step sB (Machine.EvStep.step sA
        (ih.trans (Machine.EvStep.step sD1 (Machine.EvStep.step sD2 Machine.EvStep.refl))))

/-- Left-counter increment sweep (Coq `incr_left`): the head, entering the left
accumulator in state `D`, applies the Zeckendorf carry `zI` to it and returns to
the right boundary in state `A`.  Forward `refine` steps; Lean infers the tapes. -/
lemma incr_left : ∀ (n : Dorf) (r : ListBlank (Symbol 1)),
    headL 3 (Ts n) (ListBlank.cons 𝟙 (ListBlank.cons 𝟙 r))
      -[M]->* (⟨0, Tape.mk' (Ts (zI n)) r⟩ : Config 4 1)
  | zend, r => by
      simp only [Ts, zI, headL_empty]
      refine Machine.EvStep.step (step_left_edge gD0 _) ?_
      refine Machine.EvStep.step (step_right_mk' gC0 _ _) ?_
      refine Machine.EvStep.step (step_right_mk' gE1 _ _) ?_
      refine Machine.EvStep.step (step_right_mk' gB1 _ _) ?_
      exact Machine.EvStep.step (step_right_mk' gA1 _ _) Machine.EvStep.refl
  | zO n, r => by
      simp only [Ts, zI, headL_cons]
      refine Machine.EvStep.step (step_left_mk' (l₀ := 𝟘) gD0 _ _) ?_
      refine Machine.EvStep.step (step_right_mk' gC0 _ _) ?_
      refine Machine.EvStep.step (step_right_mk' gE1 _ _) ?_
      refine Machine.EvStep.step (step_right_mk' gB1 _ _) ?_
      exact Machine.EvStep.step (step_right_mk' gA1 _ _) Machine.EvStep.refl
  | zIO n, r => by
      simp only [Ts, zI, headL_cons]
      refine Machine.EvStep.step (step_left_mk' (l₀ := 𝟙) gD0 _ _) ?_
      refine Machine.EvStep.step (step_left_mk' (l₀ := 𝟘) gC1 _ _) ?_
      refine Machine.EvStep.step (step_left_mk' (l₀ := 𝟙) gD0 _ _) ?_
      refine Machine.EvStep.step (step_left_head gC1 _ _) ?_
      refine (incr_left n _).trans ?_
      refine Machine.EvStep.step (step_right_mk' gA1 _ _) ?_
      refine Machine.EvStep.step (step_right_mk' gA1 _ _) ?_
      refine Machine.EvStep.step (step_right_mk' gA1 _ _) ?_
      exact Machine.EvStep.step (step_right_mk' gA1 _ _) Machine.EvStep.refl

/-- One macro-step: the counter increments (Coq `incr_D`). -/
lemma incr_D (n : Dorf) : Dcfg n -[M]->+ Dcfg (incr n) := by
  cases n with
  | zend =>
      simp only [Dcfg, incr, zI, Ls, Zs, Ts, headL_empty, headL_cons, cons_zero_empty]
      refine Trans.trans (Machine.Progress.single (step_left_edge gD0 _))
        (?_ : _ -[M]->* _)
      refine Machine.EvStep.step (step_right_mk' gC0 _ _) ?_
      refine Machine.EvStep.step (step_right_mk' gE1 _ _) ?_
      refine Machine.EvStep.step (step_right_mk' gB1 _ _) ?_
      refine Machine.EvStep.step (step_right_blank gA0d _) ?_
      refine Machine.EvStep.step (step_left_blank (l₀ := 𝟙) gB0d _) ?_
      refine Machine.EvStep.step (step_left_mk' gC1 _ _) ?_
      refine Machine.EvStep.step (step_left_mk' gD1 _ _) ?_
      simp only [cons_zero_empty]
      exact Machine.EvStep.refl
  | zO n =>
      cases n with
      | zend =>
          simp only [Dcfg, incr, zI, Ls, Zs, Ts, headL_empty, headL_cons, cons_zero_empty]
          refine Trans.trans (Machine.Progress.single (step_left_edge gD0 _))
            (?_ : _ -[M]->* _)
          refine Machine.EvStep.step (step_right_mk' gC0 _ _) ?_
          refine Machine.EvStep.step (step_right_mk' gE1 _ _) ?_
          refine Machine.EvStep.step (step_right_mk' gB1 _ _) ?_
          refine Machine.EvStep.step (step_right_blank gA0d _) ?_
          refine Machine.EvStep.step (step_left_blank (l₀ := 𝟙) gB0d _) ?_
          refine Machine.EvStep.step (step_left_mk' gC1 _ _) ?_
          refine Machine.EvStep.step (step_left_mk' gD1 _ _) ?_
          simp only [cons_zero_empty]
          exact Machine.EvStep.refl
      | zO n =>
          simp only [Dcfg, incr, zI, Ls, Zs, Ts, headL_cons]
          refine Trans.trans (Machine.Progress.single (step_left_mk' gD0 _ _))
            (?_ : _ -[M]->* _)
          refine Machine.EvStep.step (step_right_mk' gC0 _ _) ?_
          refine Machine.EvStep.step (step_right_mk' gE1 _ _) ?_
          refine Machine.EvStep.step (step_right_mk' gB1 _ _) ?_
          refine Machine.EvStep.step (step_right_mk' gA0 _ _) ?_
          refine (incr_right n _).trans ?_
          simp only [headL_cons]
          refine Machine.EvStep.step (step_left_mk' gD1 _ _) ?_
          exact Machine.EvStep.refl
      | zIO n =>
          simp only [Dcfg, incr, zI, Ls, Zs, Ts, headL_cons]
          refine Trans.trans (Machine.Progress.single (step_left_mk' gD0 _ _))
            (?_ : _ -[M]->* _)
          refine Machine.EvStep.step (step_left_mk' gC1 _ _) ?_
          refine Machine.EvStep.step (step_left_mk' gD0 _ _) ?_
          refine Machine.EvStep.step (step_left_head gC1 _ _) ?_
          refine (incr_left n _).trans ?_
          refine Machine.EvStep.step (step_right_mk' gA1 _ _) ?_
          refine Machine.EvStep.step (step_right_mk' gA1 _ _) ?_
          refine Machine.EvStep.step (step_right_mk' gA0 _ _) ?_
          refine Machine.EvStep.step (step_left_mk' gB0 _ _) ?_
          refine Machine.EvStep.step (step_left_mk' gC1 _ _) ?_
          exact Machine.EvStep.refl
  | zIO n =>
      simp only [Dcfg, incr, Ls, Zs, headL_cons]
      refine Trans.trans (Machine.Progress.single (step_left_mk' gD0 _ _))
        (?_ : _ -[M]->* _)
      refine Machine.EvStep.step (step_left_head gC1 _ _) ?_
      refine (incr_left n _).trans ?_
      refine Machine.EvStep.step (step_right_mk' gA0 _ _) ?_
      exact incr_right (zI n) _

/-- `init` reaches `Dcfg zend` in three steps. -/
lemma enters : init -[M]->* Dcfg zend := by
  have s0 := step_right_blank gA0d (∅ : ListBlank (Symbol 1))
  have s1 := step_left_blank (l₀ := 𝟙) gB0d (∅ : ListBlank (Symbol 1))
  have s2 := step_left_edge gC1 (∅ : ListBlank (Symbol 1))
  simp only [cons_zero_empty] at s1
  have hd0 : Dcfg zend = (⟨3, Tape.mk' (∅ : ListBlank (Symbol 1))
      (ListBlank.cons 𝟘 (ListBlank.cons 𝟙 ∅))⟩ : Config 4 1) := by
    simp only [Dcfg, incr, Zs, Ls, headL_empty, cons_zero_empty]
  rw [hd0]
  exact Machine.EvStep.step s0 (Machine.EvStep.step s1
    (Machine.EvStep.step s2 Machine.EvStep.refl))

/-- `SM6` does not halt: the Zeckendorf family `{Dcfg n}` is closed and reachable. -/
theorem nonHalting : ¬ M.halts init := by
  have cs : ClosedSet M (fun C => ∃ n, C = Dcfg n) init := by
    refine ⟨?_, ?_⟩
    · rintro ⟨C, n, rfl⟩
      exact ⟨⟨Dcfg (incr n), incr n, rfl⟩, incr_D n⟩
    · exact ⟨⟨Dcfg zend, zend, rfl⟩, enters⟩
  exact cs.nonHalting

end SM6

theorem sporadicMachine6_nonHalting : ¬ sporadicMachine6.halts init := SM6.nonHalting

def sporadicMachine7 : Machine 4 1 := mach["1RB---_1RC1LB_1LD1RE_1LB0LD_1RA0RC"]
theorem sporadicMachine7_nonHalting : ¬ sporadicMachine7.halts init := by
  sorry

def sporadicMachine8 : Machine 4 1 := mach["1RB---_0LC1RE_0LD1LC_1RA1LB_0RB0RA"]
theorem sporadicMachine8_nonHalting : ¬ sporadicMachine8.halts init := by
  sorry

def sporadicMachine9 : Machine 4 1 := mach["1RB1LD_1RC0RB_1LA1RC_1LE0LA_1LC---"]
theorem sporadicMachine9_nonHalting : ¬ sporadicMachine9.halts init := by
  sorry

def sporadicMachine10 : Machine 4 1 := mach["1RB1LC_0RC0RB_1LD0LA_1LE---_1LA1RE"]
theorem sporadicMachine10_nonHalting : ¬ sporadicMachine10.halts init := by
  sorry

def sporadicMachine11 : Machine 4 1 := mach["1RB1LC_0RC0RB_1LD0LA_1LE---_1LA1RA"]
theorem sporadicMachine11_nonHalting : ¬ sporadicMachine11.halts init := by
  sorry

def sporadicMachine12 : Machine 4 1 := mach["1RB1LC_0RC0RB_1LD0LA_1LE---_1LA0LA"]
theorem sporadicMachine12_nonHalting : ¬ sporadicMachine12.halts init := by
  sorry

/-- A sporadic holdout machine bundled with a proof that it never halts. -/
structure SporadicCert where
  machine : Machine 4 1
  nonHalting : ¬ machine.halts init

/-- The certified sporadic holdouts.  Adding or removing a holdout means editing
this list alongside its `…_nonHalting` theorem. -/
def sporadicCerts : List SporadicCert :=
  [ ⟨sporadicMachine0, sporadicMachine0_nonHalting⟩,
    ⟨sporadicMachine1, sporadicMachine1_nonHalting⟩,
    ⟨sporadicMachine2, sporadicMachine2_nonHalting⟩,
    ⟨sporadicMachine3, sporadicMachine3_nonHalting⟩,
    ⟨sporadicMachine4, sporadicMachine4_nonHalting⟩,
    ⟨sporadicMachine5, sporadicMachine5_nonHalting⟩,
    ⟨sporadicMachine6, sporadicMachine6_nonHalting⟩,
    ⟨sporadicMachine7, sporadicMachine7_nonHalting⟩,
    ⟨sporadicMachine8, sporadicMachine8_nonHalting⟩,
    ⟨sporadicMachine9, sporadicMachine9_nonHalting⟩,
    ⟨sporadicMachine10, sporadicMachine10_nonHalting⟩,
    ⟨sporadicMachine11, sporadicMachine11_nonHalting⟩,
    ⟨sporadicMachine12, sporadicMachine12_nonHalting⟩ ]

/-- Sound dispatch for the `.sporadic` table entry.  We are handed an arbitrary
`M`, so we recover its identity by matching it against the certified holdouts and
return that machine's non-halting proof; if `M` is none of them we stay
`.unknown` rather than fabricate a certificate.  In practice the table lookup
only routes the 13 holdouts here, but the match keeps the proof honest. -/
def sporadicResult : List SporadicCert → (M : Machine 4 1) → HaltM M Unit
  | [], _ => .unknown ()
  | c :: rest, M =>
      if h : c.machine = M then .loops_prf (h ▸ c.nonHalting)
      else sporadicResult rest M

def haltDecider (bound : ℕ) (M : Machine l s) : HaltM M Unit := do
  let _ ← TM.Table.boundedExplore bound M
  .unknown ()

def EntryDecider.run (d : EntryDecider) (M : Machine 4 1) : HaltM M Unit :=
  match d with
  | .nGram 0 len bound =>
      nGramCPSDecider { n := len, bound } M
  | .nGram history len bound =>
      nGramCPSHistoryDecider { history, left := len, right := len, bound } M
  | .nGramLRU len bound =>
      nGramCPSLRUDecider { left := len, right := len, bound } M
  | .repWL len threshold maxT bound =>
      Deciders.RepWL.decider { len, threshold, maxT, bound } M
  | .halt bound =>
      haltDecider bound M
  | .loop1 bound =>
      Deciders.Loop1.decider bound M
  | .far states dfa =>
      Deciders.FAR.decider 5000001 { states, dfa := dfa.toArray } M
  | .wfar maxD leftStates left rightStates right bound =>
      Deciders.WFAR.decider {
        maxD
        left := { states := leftStates, trans := left.toArray }
        right := { states := rightStates, trans := right.toArray }
        bound
      } M
  | .sporadic =>
      sporadicResult sporadicCerts M
  | .unsupported _ =>
      .unknown ()

def machineCode (M : Machine 4 1) : String :=
  toString (repr M)

def findEntry? (entries : List Entry) (M : Machine 4 1) : Option EntryDecider :=
  let code := machineCode M
  entries.findSome? fun entry =>
    if entry.fst = code then
      some entry.snd
    else
      none

def tableOfEntries (entries : List Entry) : Table :=
  Std.HashMap.ofList entries

def findInTable? (table : Table) (M : Machine 4 1) : Option EntryDecider :=
  table.get? (machineCode M)

def decider (entries : List Entry) (M : Machine 4 1) : HaltM M Unit :=
  match findEntry? entries M with
  | none => .unknown ()
  | some d => d.run M

def tableDecider (table : Table) (M : Machine 4 1) : HaltM M Unit :=
  match findInTable? table M with
  | none => .unknown ()
  | some d => d.run M

def emptyEntries : List Entry := []

def sporadicEntries : List Entry :=
  sporadicCerts.map fun c => (machineCode c.machine, .sporadic)

def initialEntries : List Entry :=
  sporadicEntries

def initialTable : Table :=
  tableOfEntries initialEntries

end Deciders.BB5Table
