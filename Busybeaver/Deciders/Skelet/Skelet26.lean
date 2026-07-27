import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Cases
import Busybeaver.Deciders.Skelet.EvStepTactics
import Busybeaver.TM.Table.Parse
import Busybeaver.TM.Table.ClosedSet
import Busybeaver.Deciders.Skelet.ShiftOverflowBins
import Busybeaver.Deciders.Skelet.TapeCalc

/-!
## Skelet #26 (`sporadicMachine9`) development

A Lean port of `Coq-BB5/BusyCoq/Skelet26.v` (sligocki's Skelet #26 analysis)
up to and including `step_reset0`.  The development is isolated in the
`Deciders.Skelet.Skelet26` namespace.
-/
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
  evsteps step_left_edge gD0 r, step_left_edge gE0 _, step_left_edge gC0 _, step_right_mk' gA0 _ _, step_right_mk' gB1 _ _, step_right_mk' gB1 _ _, step_right_mk' gB1 _ _

/-
Left counter increment sweep on a positive counter (Coq `L_inc`, positive part).
Induction on `p`.
-/
/-- `headL` over a positive left-counter body `L' k`, in explicit `Tape.mk'` form
(uses `L'_as_K'`). -/
lemma headL_L' (k : PosNum) (R : ListBlank (Symbol 1)) :
    headL 3 (L' k) R
      = (⟨3, Tape.mk' (K' k) (ListBlank.cons (0 : Symbol 1) R)⟩ : Config 4 1) := by
  rw [L'_as_K']; simp [headL_cons]

lemma L'_inc (p : PosNum) (r : ListBlank (Symbol 1)) :
    headL 3 (L' p) r -[M]->* headR 1 (L' (PosNum.succ p)) r := by
  induction p using PosNum.recOn generalizing r with
  | one =>
      simp only [L', headR, headL_cons, PosNum.succ]
      evchain step_left_mk' gD0 _ _, step_left_mk' gE0 _ _, step_left_mk' gC0 _ _, step_left_edge gA1 _
      refine Machine.EvStep.trans (L_inc_zero _) ?_
      simp only [L', headR]
      evsteps step_right_mk' gB1 _ _, step_right_mk' gB1 _ _, step_right_mk' gB1 _ _, step_right_mk' gB1 _ _
  | bit1 k ih =>
      simp only [L', headR, headL_cons, PosNum.succ]
      evchain step_left_mk' gD0 _ _, step_left_mk' gE0 _ _, step_left_mk' gC0 _ _
      rw [L'_as_K']
      evchain step_left_mk' gA1 _ _
      have key := ih (ListBlank.cons 1 (ListBlank.cons 1 (ListBlank.cons 1 (ListBlank.cons 1 r))))
      rw [headL_L'] at key
      refine Machine.EvStep.trans key ?_
      simp only [headR]
      evsteps step_right_mk' gB1 _ _, step_right_mk' gB1 _ _, step_right_mk' gB1 _ _, step_right_mk' gB1 _ _
  | bit0 k ih =>
      simp only [L', headR, headL_cons, PosNum.succ]
      evsteps step_left_mk' gD0 _ _, step_left_mk' gE0 _ _, step_left_mk' gC0 _ _, step_right_mk' gA0 _ _, step_right_mk' gB1 _ _, step_right_mk' gB1 _ _, step_right_mk' gB1 _ _

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
      evsteps step_right_mk' gC1 _ _, step_left_mk' gC0 _ _, step_left_head gA1 _ _
  | @bit1 n h ih =>
      show headR 2 l (ListBlank.cons 𝟙 (ListBlank.cons 𝟙 (R n)))
        -[M]->* headL 3 l (R (PosNum.succ (.bit1 n)))
      evchain step_right_mk' gC1 _ _, step_right_mk' gC1 _ _
      refine (ih (ListBlank.cons 𝟙 (ListBlank.cons 𝟙 l))).trans ?_
      rw [headL_cons]
      evsteps step_left_mk' gD1 _ _, step_left_head gA1 _ _

/-- Right counter increment with overflow (Coq `R_inc_all1`).  Induction on `h`. -/
lemma R_inc_all1 {n : PosNum} (h : All1 n) (l : ListBlank (Symbol 1)) :
    headR 2 (ListBlank.cons 𝟙 l) (R n) -[M]->* headL 3 l (R n.succ) := by
  induction h generalizing l with
  | one =>
      show headR 2 (ListBlank.cons 𝟙 l) (ListBlank.cons 𝟙 (ListBlank.cons 𝟙 ∅))
        -[M]->* headL 3 l (R (PosNum.succ .one))
      evsteps step_right_mk' gC1 _ _, step_right_mk' gC1 _ _, step_left_blank gC0 _, step_left_mk' gA1 _ _, step_left_mk' gD1 _ _, step_left_head gA1 _ _
  | @bit1 n h ih =>
      show headR 2 (ListBlank.cons 𝟙 l) (ListBlank.cons 𝟙 (ListBlank.cons 𝟙 (R n)))
        -[M]->* headL 3 l (R (PosNum.succ (.bit1 n)))
      evchain step_right_mk' gC1 _ _, step_right_mk' gC1 _ _
      refine (ih (ListBlank.cons 𝟙 (ListBlank.cons 𝟙 l))).trans ?_
      rw [headL_cons]
      evsteps step_left_mk' gD1 _ _, step_left_head gA1 _ _

/-- `D_inc` for `a = 0`. -/
lemma D_inc_zero {n : Num} {m : PosNum} (h : Has0 m) :
    D n 0 m -[M]->* D (Num.succ n) 0 m.succ := by
  unfold D
  refine (L_inc n _).trans ?_
  evchain step_right_mk' gB1 _ _, step_right_mk' gB0 _ _, step_right_mk' gC1 _ _, step_left_mk' gC0 _ _, step_left_mk' gA1 _ _, step_left_mk' gD1 _ _, step_right_mk' gA0 _ _, step_right_mk' gB0 _ _, step_right_mk' gC1 _ _, step_right_mk' gC1 _ _
  refine (R_inc_has0 h _).trans ?_
  rw [headL_cons]
  evsteps step_left_mk' gD1 _ _, step_left_mk' gA1 _ _, step_left_mk' gD1 _ _, step_left_head gA1 _ _

/-- `D_inc` for `a = 1`. -/
lemma D_inc_one {n : Num} {m : PosNum} (h : Has0 m) :
    D n 1 m -[M]->* D (Num.succ n) 1 m.succ := by
  unfold D
  refine (L_inc n _).trans ?_
  evchain step_right_mk' gB1 _ _, step_right_mk' gB0 _ _, step_right_mk' gC1 _ _, step_right_mk' gC1 _ _
  refine (R_inc_has0 h _).trans ?_
  rw [headL_cons]
  evsteps step_left_mk' gD1 _ _, step_left_mk' gA1 _ _, step_left_mk' gD1 _ _, step_right_mk' gA0 _ _, step_right_mk' gB0 _ _, step_right_mk' gC1 _ _, step_left_mk' gC0 _ _, step_left_mk' gA1 _ _, step_left_mk' gD1 _ _, step_left_head gA1 _ _

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
  evsteps step_left_mk' gD0 _ _, step_left_mk' gE0 _ _, step_left_mk' gC0 _ _, step_left_head gA1 _ _

/-- Coq `eat_KI`. -/
lemma eat_KI {t : PosNum} (h : Has0 t) (l : side) :
    headL 3 (ListBlank.cons 𝟘 (ListBlank.cons 𝟘 (ListBlank.cons 𝟙 (ListBlank.cons 𝟘 l)))) (R t)
      -[M]->* headL 3 l (R t.succ.bit1.bit0) := by
  rw [headL_cons]
  evchain step_left_mk' gD0 _ _, step_left_mk' gE0 _ _, step_right_mk' gC1 _ _, step_right_mk' gC1 _ _, step_right_mk' gC1 _ _
  refine (R_inc_has0 h _).trans ?_
  rw [headL_cons]
  evsteps step_left_mk' gD1 _ _, step_left_mk' gA1 _ _, step_left_mk' gD1 _ _, step_right_mk' gA0 _ _, step_right_mk' gB0 _ _, step_right_mk' gC1 _ _, step_left_mk' gC0 _ _, step_left_mk' gA1 _ _, step_left_mk' gD1 _ _, step_left_head gA1 _ _

/-- Coq `eat_JI`. -/
lemma eat_JI {t : PosNum} (h : Has0 t) (l : side) :
    headL 3 (ListBlank.cons 𝟙 (ListBlank.cons 𝟘 l)) (R t)
      -[M]->* headL 3 l (R t.succ.bit0) := by
  rw [headL_cons]
  evchain step_left_mk' gD1 _ _, step_right_mk' gA0 _ _, step_right_mk' gB0 _ _
  refine (R_inc_has0 h _).trans ?_
  rw [headL_cons]
  evsteps step_left_mk' gD1 _ _, step_left_head gA1 _ _

open Deciders.Skelet.FixedBin in
/-- Increment of a fixed-width `Lk` block (Coq `Lk_inc`).  Induction on the `Succ` proof. -/
lemma Lk_inc {k : ℕ} {n n' : Bin k} (hn : Succ n n') (l : side) (r : side) :
    headL 3 ((Lk n : List (Symbol 1)) ++ l) r -[M]->* headR 1 ((Lk n' : List (Symbol 1)) ++ l) r := by
  induction hn generalizing l r with
  | b0 n =>
      simp only [Lk, ListBlank.append_cons]
      rw [headL_cons]
      evsteps step_left_mk' gD0 _ _, step_left_mk' gE0 _ _, step_left_mk' gC0 _ _, step_right_mk' gA0 _ _, step_right_mk' gB1 _ _, step_right_mk' gB1 _ _, step_right_mk' gB1 _ _
  | @b1 k' np ns hp ih =>
      simp only [Lk, ListBlank.append_cons]
      rw [headL_cons]
      evchain step_left_mk' gD0 _ _, step_left_mk' gE0 _ _, step_left_mk' gC0 _ _, step_left_head gA1 _ _
      refine (ih l (ListBlank.cons 𝟙 (ListBlank.cons 𝟙 (ListBlank.cons 𝟙 (ListBlank.cons 𝟙 r))))).trans ?_
      evsteps step_right_mk' gB1 _ _, step_right_mk' gB1 _ _, step_right_mk' gB1 _ _, step_right_mk' gB1 _ _

open Deciders.Skelet.FixedBin in
/-- `LaR_inc` for `a = 0`. -/
lemma LaR_inc_zero {k : ℕ} {np ns : Bin k} (hn : Succ np ns) {m : PosNum} (hm : Has0 m) (l : side) :
    headL 3 ((Lk np : List (Symbol 1)) ++ l)
        (ListBlank.cons 𝟙 (ListBlank.cons 𝟘 (ListBlank.cons 𝟙 (ListBlank.cons 𝟘 (R m)))))
      -[M]->* headL 3 ((Lk ns : List (Symbol 1)) ++ l)
        (ListBlank.cons 𝟙 (ListBlank.cons 𝟘 (ListBlank.cons 𝟙 (ListBlank.cons 𝟘 (R m.succ))))) := by
  refine (Lk_inc hn l _).trans ?_
  evchain step_right_mk' gB1 _ _, step_right_mk' gB0 _ _, step_right_mk' gC1 _ _, step_left_mk' gC0 _ _, step_left_mk' gA1 _ _, step_left_mk' gD1 _ _, step_right_mk' gA0 _ _, step_right_mk' gB0 _ _, step_right_mk' gC1 _ _, step_right_mk' gC1 _ _
  refine (R_inc_has0 hm _).trans ?_
  rw [headL_cons]
  evsteps step_left_mk' gD1 _ _, step_left_mk' gA1 _ _, step_left_mk' gD1 _ _, step_left_head gA1 _ _

open Deciders.Skelet.FixedBin in
/-- `LaR_inc` for `a = 1`. -/
lemma LaR_inc_one {k : ℕ} {np ns : Bin k} (hn : Succ np ns) {m : PosNum} (hm : Has0 m) (l : side) :
    headL 3 ((Lk np : List (Symbol 1)) ++ l)
        (ListBlank.cons 𝟙 (ListBlank.cons 𝟘 (ListBlank.cons 𝟙 (ListBlank.cons 𝟙 (R m)))))
      -[M]->* headL 3 ((Lk ns : List (Symbol 1)) ++ l)
        (ListBlank.cons 𝟙 (ListBlank.cons 𝟘 (ListBlank.cons 𝟙 (ListBlank.cons 𝟙 (R m.succ))))) := by
  refine (Lk_inc hn l _).trans ?_
  evchain step_right_mk' gB1 _ _, step_right_mk' gB0 _ _, step_right_mk' gC1 _ _, step_right_mk' gC1 _ _
  refine (R_inc_has0 hm _).trans ?_
  rw [headL_cons]
  evsteps step_left_mk' gD1 _ _, step_left_mk' gA1 _ _, step_left_mk' gD1 _ _, step_right_mk' gA0 _ _, step_right_mk' gB0 _ _, step_right_mk' gC1 _ _, step_left_mk' gC0 _ _, step_left_mk' gA1 _ _, step_left_mk' gD1 _ _, step_left_head gA1 _ _

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
  · rename_i p ih; use 0, Num.pos p; simp +decide [*] ;
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
  · -- k = 0: normalise the powers so the `Num` argument is `1 + 2 * n'`.
    simp only [pow_zero, pow_one, zero_add]
    cases n' with
    | zero => simp +decide
    | pos p =>
      -- The argument equals `Num.pos p.bit1`; we prove the `Num` identity via the
      -- cast to `ℕ`, which avoids depending on the exact `simp`-normal form.
      have hnum : (1 + 2 * Num.pos p : Num) = Num.pos p.bit1 := by
        apply Num.to_nat_inj.mp
        simp only [Num.cast_add, Num.cast_mul, Num.cast_one, Num.cast_pos, PosNum.cast_bit1,
          show ((2 : Num) : ℕ) = 2 from rfl]
        ring
      rw [hnum]
      simp +decide [J, J', binMin, Lk]
  · -- By definition of $J$, we know that $J(2^{k+1} + 2^{k+2} n') = J(2(2^k + 2^{k+1} n'))$.
    have hJ_succ : J (2 ^ (k + 1) + 2 ^ (k + 2) * n') = J (2 * (2 ^ k + 2 ^ (k + 1) * n')) := by
      ring_nf;
    rw [ hJ_succ, show J ( 2 * ( 2 ^ k + 2 ^ ( k + 1 ) * n' ) ) = ListBlank.cons 0 ( ListBlank.cons 0 ( ListBlank.cons 0 ( ListBlank.cons 0 ( J ( 2 ^ k + 2 ^ ( k + 1 ) * n' ) ) ) ) ) from ?_ ];
    · rw [ ih ];
      exact ListBlank.ext (congrFun rfl);
    · have hJ_def : ∀ p : PosNum, J (Num.pos p.bit0) = ListBlank.cons 0 (ListBlank.cons 0 (ListBlank.cons 0 (ListBlank.cons 0 (J (Num.pos p))))) := by
        intros p
        simp [J, J'];
      cases h : 2 ^ k + 2 ^ ( k + 1 ) * n' <;> simp_all +decide [ two_mul ];
      convert hJ_def _ using 2 ; ring_nf!;
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

/-! ## Reset cycle and non-halting (Coq `start_reset0` … `nonhalt`) -/

/-- Coq `start_reset0`. -/
lemma start_reset0 (n : Num) {m : PosNum} (h : All1 m) :
    D n 0 m -[M]->+ E0 (Num.succ n) 1 m.succ := by
  unfold D
  refine Trans.trans (L_inc n _) (?_ : _ -[M]->+ _)
  rw [L_as_K]
  refine Trans.trans (Machine.Progress.single (step_right_mk' gB1 _ _)) (?_ : _ -[M]->* _)
  evchain step_right_mk' gB0 _ _, step_right_mk' gC1 _ _, step_left_mk' gC0 _ _, step_left_mk' gA1 _ _, step_left_mk' gD1 _ _, step_right_mk' gA0 _ _, step_right_mk' gB0 _ _, step_right_mk' gC1 _ _, step_right_mk' gC1 _ _
  refine (R_inc_all1 h _).trans ?_
  rw [headL_cons]
  evsteps step_left_mk' gD1 _ _, step_left_mk' gA1 _ _, step_left_mk' gD1 _ _, step_right_mk' gA0 _ _, step_right_mk' gB0 _ _, step_right_mk' gC1 _ _, step_left_mk' gC0 _ _, step_left_mk' gA1 _ _, step_left_mk' gD1 _ _, step_left_head gA1 _ _

/-
`J (2*(n+1))` peels off four leading zeros.
-/
lemma J_double (n : Num) :
    J (2 * (n + 1))
      = ListBlank.cons 𝟘 (ListBlank.cons 𝟘 (ListBlank.cons 𝟘 (ListBlank.cons 𝟘 (J (n + 1))))) := by
  cases n <;> simp +decide [two_mul];
  rename_i n;
  rw [ show ( Num.pos n + 1 + ( Num.pos n + 1 ) : Num ) = Num.pos ( n + 1 |> PosNum.bit0 ) by
        -- By definition of `Num.add`, we can rewrite the left-hand side as `Num.pos (n + 1 + (n + 1))`.
        have h_add : Num.pos n + 1 + (Num.pos n + 1) = Num.pos (n + 1 + (n + 1)) := by
          rfl;
        convert h_add using 2;
        exact Eq.symm (PosNum.bit0_of_bit0 (n + 1)) ];
  exact ListBlank.ext (congrFun rfl)

/-- Base case of `start_reset1` (`m = 1`). -/
lemma start_reset1_base (n : Num) :
    D n 1 1 -[M]->+ E1 (2 * (n + 1)) 0 1 := by
  have hJ : J (2 * (n + 1))
      = ListBlank.cons 𝟘 (ListBlank.cons 𝟘 (ListBlank.cons 𝟘 (ListBlank.cons 𝟘 (J (Num.succ n))))) := by
    rw [← Num.add_one n]; exact J_double n
  unfold D E1
  refine Trans.trans (L_inc n _) (?_ : _ -[M]->+ _)
  rw [L_as_J]
  refine Trans.trans (Machine.Progress.single (step_right_mk' gB1 _ _)) (?_ : _ -[M]->* _)
  evchain step_right_mk' gB0 _ _, step_right_mk' gC1 _ _, step_right_mk' gC1 _ _, step_right_mk' gC1 _ _, step_right_mk' gC1 _ _, step_left_blank gC0d _, step_left_mk' gA1 _ _, step_left_mk' gD1 _ _, step_left_mk' gA1 _ _, step_left_mk' gD1 _ _
  rw [hJ]
  evsteps step_left_head gA1 _ _

/-- Inductive case of `start_reset1` (`m = bit1 m0`). -/
lemma start_reset1_step (n : Num) (m0 : PosNum) (h0 : All1 m0) (m'' : PosNum)
    (hm'' : m''.bit0 = m0.succ) :
    D n 1 m0.bit1 -[M]->+ E1 (2 * (n + 1)) 0 m''.bit0 := by
  have hR : R (m0.bit1).succ
      = ListBlank.cons 𝟙 (ListBlank.cons 𝟘 (ListBlank.cons 𝟙 (ListBlank.cons 𝟘 (R m'')))) := by
    have h1 : (m0.bit1).succ = (m''.bit0).bit0 := by rw [show (m0.bit1).succ = (m0.succ).bit0 from rfl, ← hm'']
    rw [h1]; simp only [R]
  have hJ : J (2 * (n + 1))
      = ListBlank.cons 𝟘 (ListBlank.cons 𝟘 (ListBlank.cons 𝟘 (ListBlank.cons 𝟘 (J (Num.succ n))))) := by
    rw [← Num.add_one n]; exact J_double n
  unfold D E1
  refine Trans.trans (L_inc n _) (?_ : _ -[M]->+ _)
  rw [L_as_J]
  refine Trans.trans (Machine.Progress.single (step_right_mk' gB1 _ _)) (?_ : _ -[M]->* _)
  evchain step_right_mk' gB0 _ _, step_right_mk' gC1 _ _, step_right_mk' gC1 _ _
  refine (R_inc_all1 (All1.bit1 h0)
    (ListBlank.cons 𝟙 (ListBlank.cons 𝟙 (ListBlank.cons 𝟘 (ListBlank.cons 𝟘 (ListBlank.cons 𝟘 (ListBlank.cons 𝟘 (J (Num.succ n))))))))).trans ?_
  rw [hR, headL_cons]
  evchain step_left_mk' gD1 _ _
  rw [hJ]
  evsteps step_left_head gA1 _ _

/-- Coq `start_reset1`. -/
lemma start_reset1 (n : Num) {m : PosNum} (h : All1 m) :
    ∃ m' : PosNum, m'.bit0 = m.succ ∧ D n 1 m -[M]->+ E1 (2 * (n + 1)) 0 m' := by
  induction h with
  | one => exact ⟨1, rfl, start_reset1_base n⟩
  | @bit1 m0 h0 ih =>
      obtain ⟨m'', hm'', _⟩ := ih
      exact ⟨m''.bit0, by rw [show (PosNum.bit1 m0).succ = (m0.succ).bit0 from rfl, hm''],
        start_reset1_step n m0 h0 m'' hm''⟩

/-
Coq `do_reset0`.
-/
lemma do_reset0 (n : Num) (m : PosNum) (a : Symbol 1)
    (hinv : (n : ℕ) ≤ b m) (hpos : 0 < (n : ℕ)) :
    ∃ m' : PosNum, (E0 n a m -[M]->* E0 0 1 m') ∧ reset_invariant m' := by
  revert n m a hinv hpos;
  -- We'll use strong induction on `n`.
  have h_ind : ∀ n : ℕ, ∀ (n' : Num) (m : PosNum) (a : Symbol 1), (n' : ℕ) = n → (n' : ℕ) ≤ b m → 0 < (n' : ℕ) → ∃ m' : PosNum, (E0 n' a m -[M]->* E0 0 1 m') ∧ reset_invariant m' := by
    intro n
    induction' n using Nat.strong_induction_on with n ih;
    intro n' m a hn' hinv hpos;
    obtain ⟨ n'', m'', h₁, h₂, h₃, h₄ ⟩ := step_reset0 n' m a hinv hpos;
    by_cases h₅ : 0 < (n'' : ℕ);
    · obtain ⟨ m''', h₆, h₇ ⟩ := ih ( n'' : ℕ ) ( by linarith ) n'' m'' 1 rfl h₃ h₅; exact ⟨ m''', h₁.trans h₆, h₇ ⟩ ;
    · cases n'' <;> aesop;
  exact fun n m a h₁ h₂ => h_ind _ _ _ _ rfl h₁ h₂

/-
Coq `pow4_shift1`.
-/
lemma pow4_shift1 (k : ℕ) (n : PosNum) : pow4 k n.bit0 = (pow4 k n).bit0 := by
  induction' k with k ih generalizing n <;> simp_all +decide [ pow4 ]

/-- Reachability step of `step_reset1` (the `drop_JI` sweep). -/
lemma step_reset1_run (k : ℕ) (n' : Num) (m : PosNum) (a : Symbol 1)
    (hb : 2 ^ (k + 1) - 1 ≤ b m) :
    E1 (2 ^ (k + 1) + 2 ^ (k + 1 + 1) * n') a m
      -[M]->* E0 n' 0 ((pow4 k (f m a (k + 1)).succ).bit0) := by
  unfold E1 E0
  rw [prepare_J (k + 1) n', K_as_J]
  refine (drop_JI a hb (ListBlank.cons 𝟘 (ListBlank.cons 𝟘 (J n')))).trans ?_
  have hp : pow4 (k + 1) (f m a (k + 1)).succ
      = ((pow4 k (f m a (k + 1)).succ).bit0).bit0 := by
    rw [pow4, pow4_shift]
  rw [hp]
  exact Machine.EvStep.refl

/-- `b ((f m a (k+1)).succ) = 2 * b (f1 m a (k+1))`. -/
lemma b_f_succ (m : PosNum) (a : Symbol 1) (k : ℕ) :
    b (f m a (k + 1)).succ = 2 * b (f1 m a (k + 1)) := by
  rw [f_as_f1]
  show b (PosNum.bit1 (f1 m a (k + 1))) = _
  simp only [b]

/-
Strict decrease of `step_reset1`.
-/
lemma step_reset1_dec (k : ℕ) (n n' : Num) (hn_eq : n = 2 ^ (k + 1) + 2 ^ (k + 2) * n') :
    (n' : ℕ) < (n : ℕ) := by
  rw [ hn_eq ];
  -- Since $2^{k+2} \geq 1$, we have $n' < 2^{k+1} + 2^{k+2} * n'$.
  have h_ineq : (n' : ℕ) < 2^(k+1) + 2^(k+2) * (n' : ℕ) := by
    nlinarith [ pow_pos ( by decide : 0 < 2 ) ( k + 1 ), pow_pos ( by decide : 0 < 2 ) ( k + 2 ), show ( n' : ℕ ) ≥ 0 by exact Nat.zero_le _ ];
  convert h_ineq using 1;
  norm_num [ Num.add, Num.mul ];
  congr;
  · induction k + 1 <;> simp_all +decide [ pow_succ' ];
  · induction k + 2 <;> simp_all +decide [ pow_succ' ]

/-
`b`-distance bound of `step_reset1`.
-/
lemma step_reset1_bbound (k : ℕ) (n n' : Num) (m : PosNum) (a : Symbol 1)
    (hle : (n : ℕ) ≤ 4 * b m) (hn_eq : n = 2 ^ (k + 1) + 2 ^ (k + 2) * n')
    (hbound : 2 ^ (k + 1) ≤ b m) :
    (n' : ℕ) ≤ b (pow4 k (f m a (k + 1)).succ).bit0 := by
  -- From `hn_eq`, we have `2^(k+2) * n' ≤ 4 * b m`.
  have h_le : 2 ^ (k + 2) * (n' : ℕ) ≤ 4 * (b m : ℕ) := by
    convert Nat.le_trans _ hle using 1;
    convert Nat.le_add_left _ _;
    convert congr_arg ( fun x : Num => ( x : ℕ ) ) hn_eq using 1;
    swap;
    exact 2 ^ ( k + 1 );
    norm_num [ Num.add, Num.mul ];
    congr;
    · induction k + 1 <;> simp_all +decide [ pow_succ' ];
    · induction k + 2 <;> simp_all +decide [ pow_succ' ];
  -- By definition of $f1$, we know that $b (f1 m a (k + 1)) \geq b m - (2 ^ (k + 1) - 1)$.
  have h_f1_ge : b (f1 m a (k + 1)) ≥ b m - (2 ^ (k + 1) - 1) := by
    have h_f1_ge : b (addN (2 ^ (k + 1) - 1) m) = b m - (2 ^ (k + 1) - 1) := by
      apply b_add; exact Nat.sub_le_of_le_add (by linarith);
    unfold f1; split_ifs <;> simp_all +decide [ b ] ;
    · omega;
    · omega;
  have h_pow4_ge : b (pow4 k (f m a (k + 1)).succ) ≥ 2 ^ (2 * k) * (2 * (b m - (2 ^ (k + 1) - 1)) + 1) - 1 := by
    have h_pow4_ge : b (pow4 k (f m a (k + 1)).succ) = 2 ^ (2 * k) * (b (f m a (k + 1)).succ + 1) - 1 := by
      convert b_pow4 k ( f m a ( k + 1 ) ).succ using 1;
    have h_f_ge : b (f m a (k + 1)).succ = 2 * b (f1 m a (k + 1)) := by
      exact b_f_succ m a k;
    exact h_pow4_ge.symm ▸ Nat.sub_le_sub_right ( Nat.mul_le_mul_left _ ( by linarith ) ) _;
  simp_all +decide [ pow_succ', pow_mul' ];
  rw [ show b ( pow4 k ( f m a ( k + 1 ) ).succ ).bit0 = 2 * b ( pow4 k ( f m a ( k + 1 ) ).succ ) + 1 from ?_ ];
  · zify at *;
    rw [ Nat.cast_sub ] at * <;> push_cast at *;
    · erw [ Nat.cast_sub ] at * <;> push_cast at * <;> repeat nlinarith only [ h_le, h_pow4_ge, hbound, pow_pos ( zero_lt_two' ℕ ) k ] ;
      nlinarith [ pow_pos ( zero_lt_two' ℤ ) k, pow_two ( 2 ^ k - 1 : ℤ ) ];
    · exact Nat.one_le_iff_ne_zero.mpr ( by positivity );
    · exact Nat.sub_le_of_le_add <| by linarith;
  · exact Eq.symm (Nat.add_succ (2 * b (pow4 k (f m a (k + 1)).succ)) 0)

/-- `reset_invariant` part of `step_reset1`. -/
lemma step_reset1_inv (k : ℕ) (m : PosNum) (a : Symbol 1) (hbound : 2 ^ (k + 1) ≤ b m) :
    reset_invariant (pow4 k (f m a (k + 1)).succ).bit0 := by
  have hbz : b (f m a (k + 1)).succ = 2 * b (f1 m a (k + 1)) := b_f_succ m a k
  have hbp : b (pow4 k (f m a (k + 1)).succ)
      = 2 ^ (2 * k) * (b (f m a (k + 1)).succ + 1) - 1 := b_pow4 k _
  have hbit : b (pow4 k (f m a (k + 1)).succ).bit0
      = 2 * b (pow4 k (f m a (k + 1)).succ) + 1 := by
    show b (PosNum.bit0 _) = _; simp only [b]
  have hpk : 1 ≤ 2 ^ (k + 1) := Nat.one_le_two_pow
  have hD : b (addN (2 ^ (k + 1) - 1) m) = b m - (2 ^ (k + 1) - 1) := b_add _ (by omega)
  have hf1ge : 2 ≤ b (f1 m a (k + 1)) := by
    unfold f1; split_ifs <;> simp only [b] <;> omega
  refine ⟨?_, 2 * k + 1, b (f1 m a (k + 1)), ?_, hf1ge⟩
  · have h1 : (1 : ℕ) ≤ (pow4 k (f m a (k + 1)).succ : ℕ) :=
      (pow4 k (f m a (k + 1)).succ).one_le_cast
    have he : ((pow4 k (f m a (k + 1)).succ).bit0 : ℕ)
        = 2 * (pow4 k (f m a (k + 1)).succ : ℕ) := by
      simp [PosNum.cast_bit0, two_mul]
    omega
  · have hXge : 1 ≤ 2 ^ (2 * k) * (b (f m a (k + 1)).succ + 1) :=
      Nat.one_le_iff_ne_zero.mpr (by positivity)
    have hp1 : b (pow4 k (f m a (k + 1)).succ) + 1
        = 2 ^ (2 * k) * (b (f m a (k + 1)).succ + 1) := by rw [hbp]; omega
    have e1 : 2 ^ (2 * k + 1) = 2 * 2 ^ (2 * k) := by rw [pow_succ]; ring
    have e2 : 2 ^ (2 * k + 2) = 4 * 2 ^ (2 * k) := by rw [pow_add]; ring
    rw [hbit, show 2 * b (pow4 k (f m a (k + 1)).succ) + 1 + 1
        = 2 * (b (pow4 k (f m a (k + 1)).succ) + 1) from by ring, hp1, hbz, e1, e2]
    ring

/-- Coq `step_reset1`. -/
lemma step_reset1 (n : Num) (m : PosNum) (a : Symbol 1)
    (hle : (n : ℕ) ≤ 4 * b m)
    (hex : ∃ (k : ℕ) (n' : Num), n = 2 ^ (k + 1) + 2 ^ (k + 2) * n' ∧ 2 ^ (k + 1) ≤ b m) :
    ∃ (n' : Num) (m' : PosNum),
      (E1 n a m -[M]->* E0 n' 0 m') ∧ (n' : ℕ) < (n : ℕ) ∧ (n' : ℕ) ≤ b m' ∧ reset_invariant m' := by
  obtain ⟨k, n', hn_eq, hbound⟩ := hex
  refine ⟨n', (pow4 k (f m a (k + 1)).succ).bit0, ?_, ?_, ?_, ?_⟩
  · rw [hn_eq]
    exact step_reset1_run k n' m a (by omega)
  · exact step_reset1_dec k n n' hn_eq
  · exact step_reset1_bbound k n n' m a hle hn_eq hbound
  · exact step_reset1_inv k m a hbound

/-
Coq `do_reset1`.
-/
lemma do_reset1 (n : Num) (m : PosNum) (a : Symbol 1)
    (hle : (n : ℕ) ≤ 4 * b m)
    (hex : ∃ (k : ℕ) (n' : Num), n = 2 ^ (k + 1) + 2 ^ (k + 2) * n' ∧ 2 ^ (k + 1) ≤ b m) :
    ∃ (m' : PosNum) (a' : Symbol 1), (E1 n a m -[M]->* E0 0 a' m') ∧ reset_invariant m' := by
  -- Use `step_reset1` to obtain `n', m'` with `E1 n a m -[M]->* E0 n' 0 m'`, `(n':ℕ) < (n:ℕ)`, `(n':ℕ) ≤ b m'`, `reset_invariant m'`.
  obtain ⟨n', m', Hsteps, Hless, Hinv⟩ := step_reset1 n m a hle hex;
  by_cases hn' : 0 < (n' : ℕ);
  · obtain ⟨ m'', Hsteps', Hinv' ⟩ := do_reset0 n' m' 0 Hinv.1 hn';
    exact ⟨ m'', 1, Hsteps.trans Hsteps', Hinv' ⟩;
  · cases n' <;> aesop

/-- Coq `D0_next`. -/
lemma D0_next (m : PosNum) :
    ∃ m' : PosNum, (D 0 0 m -[M]->+ D 0 1 m') ∧ reset_invariant m' := by
  have hall : All1 (addN (b m) m) := b0_all1 (b_add_self m)
  have hsucc : b (addN (b m) m).succ = (addN (b m) m : ℕ) := b0_succ (b_add_self m)
  have hle : ((Num.succ (b m : Num) : Num) : ℕ) ≤ b (addN (b m) m).succ := by
    rw [hsucc, Num.cast_succ, Num.to_of_nat, addN_cast]
    have : (1 : ℕ) ≤ (m : ℕ) := m.one_le_cast; omega
  have hpos : 0 < ((Num.succ (b m : Num) : Num) : ℕ) := by
    rw [Num.cast_succ]; omega
  obtain ⟨m', hsteps, hinv⟩ :=
    do_reset0 (Num.succ (b m : Num)) (addN (b m) m).succ 1 hle hpos
  refine ⟨m', ?_, hinv⟩
  have c1 : D 0 0 m -[M]->* D (b m : Num) 0 (addN (b m) m) := by
    have h := @D_finish 0 0 m; simpa using h
  have c2 : D (b m : Num) 0 (addN (b m) m)
      -[M]->+ E0 (Num.succ (b m : Num)) 1 (addN (b m) m).succ := start_reset0 (b m : Num) hall
  exact Trans.trans (Trans.trans c1 c2) hsteps

/-
Coq `D1_next`.
-/
lemma D1_next (m : PosNum) (hinv : reset_invariant m) :
    ∃ (m' : PosNum) (a' : Symbol 1), (D 0 1 m -[M]->+ D 0 a' m') ∧ reset_invariant m' := by
  obtain ⟨hm2, k, n', heq, hn'2⟩ := hinv;
  -- Let `m0 := addN (b m) m`; `All1 m0` by `b0_all1 (b_add_self m)`.
  set m0 := addN (b m) m with hm0
  have hm0_all1 : All1 m0 := b0_all1 (b_add_self m);
  -- Apply `start_reset1 (b m : Num) (this All1)` to get `m'`, `hm' : m'.bit0 = m0.succ`, and `H1 : D (b m : Num) 1 m0 -[M]->+ E1 (2*((b m:Num)+1)) 0 m'`.
  obtain ⟨m', hm', H1⟩ := start_reset1 (b m : Num) hm0_all1;
  -- Now apply `do_reset1 (2*((b m:Num)+1)) m' 0` providing:
  -- - `hle : ((2*((b m:Num)+1):Num):ℕ) ≤ 4 * b m'`: the LHS casts to `2*(b m + 1)` (push the Num→ℕ cast with `Num.to_of_nat`); from `hbm'` (so `2*b m' = b m + (m:ℕ) - 1 ≥ b m + 1` since `(m:ℕ) ≥ 2`) conclude by `omega`.
  have hle : ((2 * ((b m : Num) + 1) : Num) : ℕ) ≤ 4 * b m' := by
    have hbm' : 2 * b m' + 1 = b m + (m : ℕ) := by
      have h1 : b m'.bit0 = b m0.succ := congr_arg b hm'
      simp only [b] at h1
      rw [hm0, b0_succ (b_add_self m), addN_cast] at h1
      exact h1
    norm_num +zetaDelta at *;
    exact show 2 * ( b m + 1 ) ≤ 4 * b m' from by show ( 2 : ℕ ) * ( b m + 1 ) ≤ 4 * b m'; linarith! [ show ( m : ℕ ) ≥ 2 by assumption ] ;
  obtain ⟨m'', a'', H2, hreset⟩ := do_reset1 (2 * ((b m : Num) + 1)) m' 0 hle ⟨k, n', by
    norm_cast;
    grind, by
    have hkey : 2 * b m' + 2 = 2 ^ k + 2 ^ (k + 1) * n' + (m : ℕ) := by
      have hkey : 2 * b m' + 1 = b m + (m : ℕ) := by
        have h1 : b m'.bit0 = b m0.succ := congr_arg b hm'
        simp only [b] at h1
        rw [hm0, b0_succ (b_add_self m), addN_cast] at h1
        exact h1
      linarith;
    nlinarith [ Nat.pow_le_pow_right two_pos ( show k + 1 ≥ 1 by linarith ), Nat.pow_le_pow_right two_pos ( show k ≥ 0 by linarith ) ]⟩
  generalize_proofs at *;
  refine' ⟨ m'', a'', _, hreset ⟩;
  have h_trans : D 0 1 m -[M]->* D (b m : Num) 1 m0 := by
    convert D_finish using 1;
    norm_num +zetaDelta at *;
  exact Trans.trans ( Trans.trans h_trans H1 ) H2

/-
Coq `D_next`.
-/
lemma D_next (m : PosNum) (a : Symbol 1) (hinv : reset_invariant m) :
    ∃ (m' : PosNum) (a' : Symbol 1), (D 0 a m -[M]->+ D 0 a' m') ∧ reset_invariant m' := by
  rcases a with ( _ | _ | a );
  · exact Exists.elim ( D0_next m ) fun m' hm' => ⟨ m', 1, hm'.1, hm'.2 ⟩;
  · exact D1_next m hinv
  · contradiction

/-- `n`-fold application of the machine step (computable). -/
private def stepN : ℕ → Config 4 1 → Option (Config 4 1)
  | 0, c => some c
  | n + 1, c => (Machine.step M c).bind (stepN n)

/-- A successful `stepN` run yields an `EvStep` reachability. -/
private lemma stepN_evstep : ∀ (n : ℕ) {c d : Config 4 1}, stepN n c = some d → c -[M]->* d
  | 0, c, d, h => by
      simp only [stepN, Option.some.injEq] at h; subst h; exact Machine.EvStep.refl
  | n + 1, c, d, h => by
      rw [stepN] at h
      cases hc : Machine.step M c with
      | none => rw [hc] at h; simp at h
      | some c1 =>
          rw [hc] at h
          exact Machine.EvStep.step hc (stepN_evstep n h)

/-- `init` reaches `D 0 0 11` (Coq `c0 -->* D 0 0 11`). -/
lemma enters : init -[M]->* D 0 0 11 := by
  refine stepN_evstep 85 ?_
  decide

/-- Skelet #26 (`sporadicMachine9`) does not halt (Coq `nonhalt`). -/
theorem nonHalting : ¬ M.halts init := by
  have cs : ClosedSet M
      (fun C => ∃ (m : PosNum) (a : Symbol 1), reset_invariant m ∧ C = D 0 a m) init := by
    refine ⟨?_, ?_⟩
    · rintro ⟨C, m, a, hinv, rfl⟩
      obtain ⟨m', a', hstep, hinv'⟩ := D_next m a hinv
      exact ⟨⟨D 0 a' m', m', a', hinv', rfl⟩, hstep⟩
    · obtain ⟨m', hstep, hinv'⟩ := D0_next 11
      exact ⟨⟨D 0 1 m', m', 1, hinv', rfl⟩, enters.trans hstep.to_evstep⟩
  exact cs.nonHalting

/-- Skelet #26 does not halt when started in state `E` on the blank tape.

This is used to close Skelet #15 (`sporadicMachine7`): mirroring Skelet #15 and
relabelling its states yields exactly Skelet #26, but with the start state mapped
to `E`.  From `⟨4, default⟩` the machine reaches the counter configuration
`D 0 0 1` in 21 concrete steps (Coq `execute`), entering the closed counter
family, so it never halts. -/
lemma enters_E : (⟨(4 : Label 4), default⟩ : Config 4 1) -[M]->* D 0 0 1 := by
  refine stepN_evstep 21 ?_
  decide

theorem nonHalting_E : ¬ M.halts (⟨(4 : Label 4), default⟩ : Config 4 1) := by
  have cs : ClosedSet M
      (fun C => ∃ (m : PosNum) (a : Symbol 1), reset_invariant m ∧ C = D 0 a m)
      (⟨(4 : Label 4), default⟩ : Config 4 1) := by
    refine ⟨?_, ?_⟩
    · rintro ⟨C, m, a, hinv, rfl⟩
      obtain ⟨m', a', hstep, hinv'⟩ := D_next m a hinv
      exact ⟨⟨D 0 a' m', m', a', hinv', rfl⟩, hstep⟩
    · obtain ⟨m', hstep, hinv'⟩ := D0_next 1
      exact ⟨⟨D 0 1 m', m', 1, hinv', rfl⟩, enters_E.trans hstep.to_evstep⟩
  exact cs.nonHalting

end Deciders.Skelet.Skelet26
