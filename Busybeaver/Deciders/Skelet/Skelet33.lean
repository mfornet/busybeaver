import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Cases
import Busybeaver.Deciders.Skelet.EvStepTactics
import Busybeaver.TM.Table.Parse
import Busybeaver.Deciders.Skelet.ShiftOverflowBins
import Busybeaver.Deciders.Skelet.TapeCalc
import Busybeaver.Deciders.Skelet.Skelet26

/-!
## Skelet #33 (`sporadicMachine10`) development

A Lean port of `Coq-BB5/BusyCoq/Skelet33.v`.  Skelet #33
(`1RB1LC_0RC0RB_1LD0LA_1LE---_1LA1RE`) differs from Skelet #34 only in the
E-on-1 transition (`1RE` instead of `1RA`): reading a `1` in state `E` keeps the
machine in `E` and moves right, so the right-counter carry is a rightward `E`
sweep (Coq `R_inc_has0`/`R_inc_all1`).  The reset argument uses a `leads`
leading-bits invariant and a `reset_invariant`, closing on the family `E 1 m`
with `leads (b m)`.
-/
open Turing
open TM.Table
open Deciders.Skelet.ShiftOverflowBins
open Deciders.Skelet.ShiftOverflow
open Deciders.Skelet.FixedBin

namespace Deciders.Skelet.Skelet33

open Deciders.Skelet.Skelet26 (prepare_K)

abbrev M : Machine 4 1 := mach["1RB1LC_0RC0RB_1LD0LA_1LE---_1LA1RE"]

local notation "𝟙" => (1 : Symbol 1)
local notation "𝟘" => (0 : Symbol 1)

-- Transitions (A=0, B=1, C=2, D=3, E=4).  Identical to Skelet #34 except `gE1`.
lemma gA0 : M.get 0 0 = .next 1 .right 1 := by decide
lemma gA1 : M.get 0 1 = .next 1 .left 2 := by decide
lemma gB0 : M.get 1 0 = .next 0 .right 2 := by decide
lemma gB1 : M.get 1 1 = .next 0 .right 1 := by decide
lemma gC0 : M.get 2 0 = .next 1 .left 3 := by decide
lemma gC1 : M.get 2 1 = .next 0 .left 0 := by decide
lemma gD0 : M.get 3 0 = .next 1 .left 4 := by decide
lemma gE0 : M.get 4 0 = .next 1 .left 0 := by decide
lemma gE1 : M.get 4 1 = .next 1 .right 4 := by decide
-- blank-edge
lemma gA0d : M.get 0 default = .next 1 .right 1 := by decide
lemma gB0d : M.get 1 default = .next 0 .right 2 := by decide
lemma gC0d : M.get 2 default = .next 1 .left 3 := by decide
lemma gD0d : M.get 3 default = .next 1 .left 4 := by decide
lemma gE0d : M.get 4 default = .next 1 .left 0 := by decide

/-- Rightward directed configuration (Coq `l {{q}}> r`). -/
def headR (q : Label 4) (L R : ListBlank (Symbol 1)) : Config 4 1 := ⟨q, Tape.mk' L R⟩

open TM.Table (headL)

/-- The counter configuration `D n m` (Coq `D`): `L n <{{C}} [1;0;1;0;1;0] *> R m`. -/
def D (n : Num) (m : PosNum) : Config 4 1 :=
  headL 2 (L n) (ListBlank.cons 𝟙 (ListBlank.cons 𝟘 (ListBlank.cons 𝟙 (ListBlank.cons 𝟘
    (ListBlank.cons 𝟙 (ListBlank.cons 𝟘 (R m)))))))

/-- The reset configuration `E n m` (Coq `E`): `K' n <{{C}} [1;0;1;0] *> R m`. -/
def E (n : PosNum) (m : PosNum) : Config 4 1 :=
  headL 2 (K' n) (ListBlank.cons 𝟙 (ListBlank.cons 𝟘 (ListBlank.cons 𝟙 (ListBlank.cons 𝟘 (R m)))))

/-- Positive successor of a `Num` (Coq `N.succ_pos`). -/
def succPos : Num → PosNum
  | .zero => 1
  | .pos p => p.succ

lemma succPos_cast (n : Num) : (succPos n : ℕ) = (n : ℕ) + 1 := by
  cases n with
  | zero => rfl
  | pos p => simp only [succPos, PosNum.cast_succ, Num.cast_pos]

/-- Left counter increment sweep, base case `n = 0` (Coq `L_inc`, `N0` case). -/
lemma L_inc_zero (r : ListBlank (Symbol 1)) :
    headL 2 (L 0) r -[M]->* headR 1 (L' .one) r := by
  rw [show (L 0) = (∅ : ListBlank (Symbol 1)) from rfl, TM.Table.headL_empty]
  simp only [L', headR]
  evsteps step_left_edge gC0 r, step_left_edge gD0 _, step_left_edge gE0 _, step_right_mk' gA0 _ _, step_right_mk' gB1 _ _, step_right_mk' gB1 _ _, step_right_mk' gB1 _ _

lemma headL_L' (k : PosNum) (R : ListBlank (Symbol 1)) :
    headL 2 (L' k) R
      = (⟨2, Tape.mk' (K' k) (ListBlank.cons (0 : Symbol 1) R)⟩ : Config 4 1) := by
  rw [L'_as_K']; simp [headL_cons]

lemma L'_inc (p : PosNum) (r : ListBlank (Symbol 1)) :
    headL 2 (L' p) r -[M]->* headR 1 (L' (PosNum.succ p)) r := by
  induction p using PosNum.recOn generalizing r with
  | one =>
      simp only [L', headR, headL_cons, PosNum.succ]
      evchain step_left_mk' gC0 _ _, step_left_mk' gD0 _ _, step_left_mk' gE0 _ _, step_left_edge gA1 _
      refine Machine.EvStep.trans (L_inc_zero _) ?_
      simp only [L', headR]
      evsteps step_right_mk' gB1 _ _, step_right_mk' gB1 _ _, step_right_mk' gB1 _ _, step_right_mk' gB1 _ _
  | bit1 k ih =>
      simp only [L', headR, headL_cons, PosNum.succ]
      evchain step_left_mk' gC0 _ _, step_left_mk' gD0 _ _, step_left_mk' gE0 _ _
      rw [L'_as_K']
      evchain step_left_mk' gA1 _ _
      have key := ih (ListBlank.cons 1 (ListBlank.cons 1 (ListBlank.cons 1 (ListBlank.cons 1 r))))
      rw [headL_L'] at key
      refine Machine.EvStep.trans key ?_
      simp only [headR]
      evsteps step_right_mk' gB1 _ _, step_right_mk' gB1 _ _, step_right_mk' gB1 _ _, step_right_mk' gB1 _ _
  | bit0 k ih =>
      simp only [L', headR, headL_cons, PosNum.succ]
      evsteps step_left_mk' gC0 _ _, step_left_mk' gD0 _ _, step_left_mk' gE0 _ _, step_right_mk' gA0 _ _, step_right_mk' gB1 _ _, step_right_mk' gB1 _ _, step_right_mk' gB1 _ _

lemma L_inc (n : Num) (r : ListBlank (Symbol 1)) :
    headL 2 (L n) r -[M]->* headR 1 (L (Num.succ n)) r := by
  cases n with
  | zero => exact L_inc_zero r
  | pos p => exact L'_inc p r

/-- Right counter increment with no overflow (Coq `R_inc_has0`). -/
lemma R_inc_has0 {n : PosNum} (h : Has0 n) (l : side) :
    headR 4 (ListBlank.cons 𝟙 l) (R n) -[M]->* headL 0 l (ListBlank.cons 𝟘 (R n.succ)) := by
  induction h generalizing l with
  | bit0 n =>
      show headR 4 (ListBlank.cons 𝟙 l) (ListBlank.cons 𝟙 (ListBlank.cons 𝟘 (R n)))
        -[M]->* headL 0 l (ListBlank.cons 𝟘 (ListBlank.cons 𝟙 (ListBlank.cons 𝟙 (R n))))
      evsteps step_right_mk' gE1 _ _, step_left_mk' gE0 _ _, step_left_mk' gA1 _ _, step_left_head gC1 _ _
  | @bit1 n h ih =>
      show headR 4 (ListBlank.cons 𝟙 l) (ListBlank.cons 𝟙 (ListBlank.cons 𝟙 (R n)))
        -[M]->* headL 0 l (ListBlank.cons 𝟘 (ListBlank.cons 𝟙 (ListBlank.cons 𝟘 (R n.succ))))
      evchain step_right_mk' gE1 _ _, step_right_mk' gE1 _ _
      refine (ih (ListBlank.cons 𝟙 (ListBlank.cons 𝟙 l))).trans ?_
      rw [headL_cons]
      evsteps step_left_mk' gA1 _ _, step_left_head gC1 _ _

/-- Right counter increment with overflow (Coq `R_inc_all1`). -/
lemma R_inc_all1 {n : PosNum} (h : All1 n) (l : side) :
    headR 4 (ListBlank.cons 𝟙 l) (R n) -[M]->* headL 2 l (R n.succ) := by
  induction h generalizing l with
  | one =>
      show headR 4 (ListBlank.cons 𝟙 l) (ListBlank.cons 𝟙 (ListBlank.cons 𝟙 ∅))
        -[M]->* headL 2 l (ListBlank.cons 𝟙 (ListBlank.cons 𝟘 (ListBlank.cons 𝟙 (ListBlank.cons 𝟙 ∅))))
      evsteps step_right_mk' gE1 _ _, step_right_mk' gE1 _ _, step_left_blank gE0d _, step_left_mk' gA1 _ _, step_left_mk' gC1 _ _, step_left_head gA1 _ _
  | @bit1 m hm ih =>
      show headR 4 (ListBlank.cons 𝟙 l) (ListBlank.cons 𝟙 (ListBlank.cons 𝟙 (R m)))
        -[M]->* headL 2 l (ListBlank.cons 𝟙 (ListBlank.cons 𝟘 (R m.succ)))
      evchain step_right_mk' gE1 _ _, step_right_mk' gE1 _ _
      refine (ih (ListBlank.cons 𝟙 (ListBlank.cons 𝟙 l))).trans ?_
      rw [headL_cons]
      evsteps step_left_mk' gC1 _ _, step_left_head gA1 _ _

/-- One counter increment (Coq `D_inc`). -/
lemma D_inc {n : Num} {m : PosNum} (h : Has0 m) :
    D n m -[M]->* D (Num.succ n) m.succ := by
  unfold D
  refine (L_inc n _).trans ?_
  evchain step_right_mk' gB1 _ _, step_right_mk' gB0 _ _, step_left_mk' gC1 _ _, step_right_mk' gA0 _ _, step_right_mk' gB0 _ _, step_left_mk' gC0 _ _, step_left_mk' gD0 _ _, step_right_mk' gE1 _ _, step_right_mk' gE1 _ _, step_right_mk' gE1 _ _, step_right_mk' gE1 _ _, step_left_mk' gE0 _ _, step_left_mk' gA1 _ _, step_left_mk' gC1 _ _, step_left_mk' gA1 _ _, step_left_mk' gC1 _ _, step_right_mk' gA0 _ _, step_right_mk' gB0 _ _, step_left_mk' gC1 _ _, step_right_mk' gA0 _ _, step_right_mk' gB0 _ _, step_left_mk' gC0 _ _, step_left_mk' gD0 _ _, step_right_mk' gE1 _ _, step_right_mk' gE1 _ _, step_right_mk' gE1 _ _, step_right_mk' gE1 _ _, step_right_mk' gE1 _ _
  refine (R_inc_has0 h _).trans ?_
  rw [headL_cons]
  evsteps step_left_mk' gA1 _ _, step_left_mk' gC1 _ _, step_left_mk' gA1 _ _, step_left_mk' gC1 _ _, step_left_head gA1 _ _

/-- Iterated increment by `u ≤ b m` (Coq `D_run`). -/
lemma D_run {n : Num} {m : PosNum} (u : ℕ) (hu : u ≤ b m) :
    D n m -[M]->* D ((u : Num) + n) (addN u m) := by
  induction' u with u ih generalizing n m;
  · simpa using Machine.EvStep.refl
  · have hbm : 0 < b m := by
      linarith;
    convert ( D_inc ( Deciders.Skelet.ShiftOverflow.bgt0_has0 hbm ) ).trans ( ih _ ) using 1;
    · congr! 1;
      norm_num [ add_assoc, Num.add ];
      cases n <;> aesop;
    · rw [ Deciders.Skelet.ShiftOverflow.b_succ hbm ] ; omega

/-- Run to saturation (Coq `D_finish`). -/
lemma D_finish {n : Num} {m : PosNum} :
    D n m -[M]->* D ((b m : Num) + n) (addN (b m) m) :=
  D_run (b m) le_rfl

/-- Start of the reset cycle (Coq `start_reset`). -/
lemma start_reset (n : Num) {m : PosNum} (h : All1 m) :
    D n m -[M]->* E (succPos n) (m.succ.bit1) := by
  unfold D
  refine (L_inc n _).trans ?_
  rw [L_as_K]
  evchain step_right_mk' gB1 _ _, step_right_mk' gB0 _ _, step_left_mk' gC1 _ _, step_right_mk' gA0 _ _, step_right_mk' gB0 _ _, step_left_mk' gC0 _ _, step_left_mk' gD0 _ _, step_right_mk' gE1 _ _, step_right_mk' gE1 _ _, step_right_mk' gE1 _ _, step_right_mk' gE1 _ _, step_left_mk' gE0 _ _, step_left_mk' gA1 _ _, step_left_mk' gC1 _ _, step_left_mk' gA1 _ _, step_left_mk' gC1 _ _, step_right_mk' gA0 _ _, step_right_mk' gB0 _ _, step_left_mk' gC1 _ _, step_right_mk' gA0 _ _, step_right_mk' gB0 _ _, step_left_mk' gC0 _ _, step_left_mk' gD0 _ _, step_right_mk' gE1 _ _, step_right_mk' gE1 _ _, step_right_mk' gE1 _ _, step_right_mk' gE1 _ _, step_right_mk' gE1 _ _
  refine (R_inc_all1 h _).trans ?_
  rw [headL_cons]
  evsteps step_left_mk' gC1 _ _, step_left_mk' gA1 _ _, step_left_mk' gC1 _ _, step_left_mk' gA1 _ _, step_left_mk' gC1 _ _, step_right_mk' gA0 _ _, step_right_mk' gB0 _ _, step_left_mk' gC1 _ _, step_right_mk' gA0 _ _, step_right_mk' gB0 _ _, step_left_mk' gC0 _ _, step_left_mk' gD0 _ _, step_right_mk' gE1 _ _, step_right_mk' gE1 _ _, step_right_mk' gE1 _ _, step_right_mk' gE1 _ _, step_left_mk' gE0 _ _, step_left_mk' gA1 _ _, step_left_mk' gC1 _ _, step_left_mk' gA1 _ _, step_left_mk' gC1 _ _, step_left_head gA1 _ _

/-- Coq `eat_LI`. -/
lemma eat_LI (l : side) (t : PosNum) :
    headL 2 (ListBlank.cons 𝟘 (ListBlank.cons 𝟘 (ListBlank.cons 𝟘 (ListBlank.cons 𝟙 l)))) (R t)
      -[M]->* headL 2 l (R t.bit1.bit1) := by
  rw [headL_cons]
  evsteps step_left_mk' gC0 _ _, step_left_mk' gD0 _ _, step_left_mk' gE0 _ _, step_left_head gA1 _ _

set_option maxHeartbeats 1000000 in
/-- Coq `eat_KI`. -/
lemma eat_KI {t : PosNum} (h : Has0 t) (hP : Has0 t.succ) (l : side) :
    headL 2 (ListBlank.cons 𝟘 (ListBlank.cons 𝟘 (ListBlank.cons 𝟙 (ListBlank.cons 𝟘 l)))) (R t)
      -[M]->* headL 2 l (R t.succ.succ.bit0.bit0) := by
  cases t with
  | one => cases h
  | bit0 t' =>
      cases hP with
      | bit1 hP' =>
        rw [show R (PosNum.bit0 t') = ListBlank.cons 𝟙 (ListBlank.cons 𝟘 (R t')) from rfl, headL_cons]
        evchain step_left_mk' gC0 _ _, step_left_mk' gD0 _ _, step_right_mk' gE1 _ _, step_right_mk' gE1 _ _, step_right_mk' gE1 _ _, step_right_mk' gE1 _ _, step_left_mk' gE0 _ _, step_left_mk' gA1 _ _, step_left_mk' gC1 _ _, step_left_mk' gA1 _ _, step_left_mk' gC1 _ _, step_right_mk' gA0 _ _, step_right_mk' gB0 _ _, step_left_mk' gC1 _ _, step_right_mk' gA0 _ _, step_right_mk' gB0 _ _, step_left_mk' gC0 _ _, step_left_mk' gD0 _ _, step_right_mk' gE1 _ _, step_right_mk' gE1 _ _, step_right_mk' gE1 _ _, step_right_mk' gE1 _ _, step_right_mk' gE1 _ _
        refine (R_inc_has0 hP' _).trans ?_
        rw [headL_cons]
        evsteps step_left_mk' gA1 _ _, step_left_mk' gC1 _ _, step_left_mk' gA1 _ _, step_left_mk' gC1 _ _, step_left_head gA1 _ _
  | bit1 t' =>
      rw [headL_cons]
      evchain step_left_mk' gC0 _ _, step_left_mk' gD0 _ _, step_right_mk' gE1 _ _, step_right_mk' gE1 _ _, step_right_mk' gE1 _ _
      refine (R_inc_has0 h _).trans ?_
      rw [headL_cons]
      evchain step_left_mk' gA1 _ _, step_left_mk' gC1 _ _, step_right_mk' gA0 _ _, step_right_mk' gB0 _ _, step_left_mk' gC1 _ _, step_right_mk' gA0 _ _, step_right_mk' gB0 _ _, step_left_mk' gC0 _ _, step_left_mk' gD0 _ _, step_right_mk' gE1 _ _, step_right_mk' gE1 _ _, step_right_mk' gE1 _ _
      refine (R_inc_has0 (Has0.bit0 (PosNum.succ t')) _).trans ?_
      rw [headL_cons]
      evsteps step_left_mk' gA1 _ _, step_left_mk' gC1 _ _, step_left_head gA1 _ _

open Deciders.Skelet.FixedBin in
/-- Increment of a fixed-width `Lk` block (Coq `Lk_inc`). -/
lemma Lk_inc {k : ℕ} {n n' : Bin k} (hn : Succ n n') (l : side) (r : side) :
    headL 2 ((Lk n : List (Symbol 1)) ++ l) r -[M]->* headR 1 ((Lk n' : List (Symbol 1)) ++ l) r := by
  induction hn generalizing l r with
  | b0 n =>
      simp only [Lk, ListBlank.append_cons]
      rw [headL_cons]
      evsteps step_left_mk' gC0 _ _, step_left_mk' gD0 _ _, step_left_mk' gE0 _ _, step_right_mk' gA0 _ _, step_right_mk' gB1 _ _, step_right_mk' gB1 _ _, step_right_mk' gB1 _ _
  | @b1 k' np ns hp ih =>
      simp only [Lk, ListBlank.append_cons]
      rw [headL_cons]
      evchain step_left_mk' gC0 _ _, step_left_mk' gD0 _ _, step_left_mk' gE0 _ _, step_left_head gA1 _ _
      refine (ih l (ListBlank.cons 𝟙 (ListBlank.cons 𝟙 (ListBlank.cons 𝟙 (ListBlank.cons 𝟙 r))))).trans ?_
      evsteps step_right_mk' gB1 _ _, step_right_mk' gB1 _ _, step_right_mk' gB1 _ _, step_right_mk' gB1 _ _

open Deciders.Skelet.FixedBin in
/-- Coq `LaR_inc`. -/
lemma LaR_inc {k : ℕ} {np ns : Bin k} (hn : Succ np ns) {m : PosNum} (hm : Has0 m) (hPm : Has0 m.succ)
    (l : side) :
    headL 2 ((Lk np : List (Symbol 1)) ++ l)
        (ListBlank.cons 𝟙 (ListBlank.cons 𝟘 (ListBlank.cons 𝟙 (ListBlank.cons 𝟘 (R m)))))
      -[M]->* headL 2 ((Lk ns : List (Symbol 1)) ++ l)
        (ListBlank.cons 𝟙 (ListBlank.cons 𝟘 (ListBlank.cons 𝟙 (ListBlank.cons 𝟘 (R m.succ.succ))))) := by
  refine (Lk_inc hn l _).trans ?_
  evchain step_right_mk' gB1 _ _, step_right_mk' gB0 _ _, step_left_mk' gC1 _ _, step_right_mk' gA0 _ _, step_right_mk' gB0 _ _, step_left_mk' gC0 _ _, step_left_mk' gD0 _ _, step_right_mk' gE1 _ _, step_right_mk' gE1 _ _, step_right_mk' gE1 _ _
  refine (R_inc_has0 hm _).trans ?_
  rw [headL_cons]
  evchain step_left_mk' gA1 _ _, step_left_mk' gC1 _ _, step_right_mk' gA0 _ _, step_right_mk' gB0 _ _, step_left_mk' gC1 _ _, step_right_mk' gA0 _ _, step_right_mk' gB0 _ _, step_left_mk' gC0 _ _, step_left_mk' gD0 _ _, step_right_mk' gE1 _ _, step_right_mk' gE1 _ _, step_right_mk' gE1 _ _
  refine (R_inc_has0 hPm _).trans ?_
  rw [headL_cons]
  evsteps step_left_mk' gA1 _ _, step_left_mk' gC1 _ _, step_left_head gA1 _ _

open Deciders.Skelet.FixedBin in
/-- Coq `LaR_incs`. -/
lemma LaR_incs {k : ℕ} {u : ℕ} {np ns : Bin k} (hp : Plus u np ns) {m : PosNum}
    (hu : 2 * u ≤ b m) (l : side) :
    headL 2 ((Lk np : List (Symbol 1)) ++ l)
        (ListBlank.cons 𝟙 (ListBlank.cons 𝟘 (ListBlank.cons 𝟙 (ListBlank.cons 𝟘 (R m)))))
      -[M]->* headL 2 ((Lk ns : List (Symbol 1)) ++ l)
        (ListBlank.cons 𝟙 (ListBlank.cons 𝟘 (ListBlank.cons 𝟙 (ListBlank.cons 𝟘 (R (addN (2 * u) m)))))) := by
  induction hp generalizing m with
  | zero n => simpa using Machine.EvStep.refl
  | @succ ucount bnp bmid bns s p ih =>
      have hbm : 0 < b m := by omega
      have hbm2 : 0 < b m.succ := by rw [b_succ hbm]; omega
      refine (LaR_inc s (bgt0_has0 hbm) (bgt0_has0 hbm2) l).trans ?_
      have hbound : 2 * ucount ≤ b m.succ.succ := by rw [b_succ hbm2, b_succ hbm]; omega
      have key := ih (m := m.succ.succ) hbound
      have hw : addN (2 * (ucount + 1)) m = addN (2 * ucount) m.succ.succ := by
        unfold addN
        rw [show 2 * (ucount + 1) = 2 * ucount + 2 from by ring, Function.iterate_add_apply]
        rfl
      rw [hw]
      exact key

open Deciders.Skelet.FixedBin in
/-- Coq `LaR_max`. -/
lemma LaR_max {k : ℕ} {m : PosNum} (hm : 2 * (2 ^ k - 1) ≤ b m) (l : side) :
    headL 2 ((Lk (binMin k) : List (Symbol 1)) ++ l)
        (ListBlank.cons 𝟙 (ListBlank.cons 𝟘 (ListBlank.cons 𝟙 (ListBlank.cons 𝟘 (R m)))))
      -[M]->* headL 2 ((Lk (binMax k) : List (Symbol 1)) ++ l)
        (ListBlank.cons 𝟙 (ListBlank.cons 𝟘 (ListBlank.cons 𝟙 (ListBlank.cons 𝟘 (R (addN (2 * (2 ^ k - 1)) m)))))) :=
  LaR_incs (inc_to_max k) hm l

/-- Coq `f`. -/
def f (m : PosNum) (k : ℕ) : PosNum := (addN (2 * (2 ^ k - 1)) m).bit0

/-- Coq `has0_f`. -/
lemma has0_f (m : PosNum) (k : ℕ) : Has0 (f m k) := Has0.bit0 _

/-- Reinterpret the `[1;0;1;0]` prefix over `R (addN (2*(2^k-1)) m)` as `R (f m k)~0`. -/
lemma R_ff (m : PosNum) (k : ℕ) :
    ListBlank.cons 𝟙 (ListBlank.cons 𝟘 (ListBlank.cons 𝟙 (ListBlank.cons 𝟘 (R (addN (2 * (2 ^ k - 1)) m)))))
      = R (f m k).bit0 := rfl

open Deciders.Skelet.FixedBin in
/-- Coq `eat_bin_max`. -/
lemma eat_bin_max (k : ℕ) {t : PosNum} (h : Has0 t) (hP : Has0 t.succ) (l : side) :
    headL 2 ((Lk (binMax k) : List (Symbol 1)) ++
        ListBlank.cons 𝟘 (ListBlank.cons 𝟘 (ListBlank.cons 𝟙 (ListBlank.cons 𝟘 l)))) (R t)
      -[M]->* headL 2 l
        (ListBlank.cons 𝟙 (ListBlank.cons 𝟘 (ListBlank.cons 𝟙 (ListBlank.cons 𝟘 (R (pow4 k t.succ).succ))))) := by
  induction k generalizing t with
  | zero =>
      simp only [binMax, Lk, ListBlank.append_empty]
      exact eat_KI h hP l
  | succ k ih =>
      simp only [binMax, Lk, ListBlank.append_cons]
      refine (eat_LI _ t).trans ?_
      exact ih (Has0.bit1 (Has0.bit1 h)) (Has0.bit0 _)

open Deciders.Skelet.FixedBin in
/-- Coq `drop_KI`. -/
lemma drop_KI {k : ℕ} {m : PosNum} (hm : 2 * (2 ^ k - 1) ≤ b m) (l : side) :
    headL 2 ((Lk (binMin k) : List (Symbol 1)) ++
        ListBlank.cons 𝟘 (ListBlank.cons 𝟘 (ListBlank.cons 𝟙 (ListBlank.cons 𝟘 l))))
        (ListBlank.cons 𝟙 (ListBlank.cons 𝟘 (ListBlank.cons 𝟙 (ListBlank.cons 𝟘 (R m)))))
      -[M]->* headL 2 l
        (ListBlank.cons 𝟙 (ListBlank.cons 𝟘 (ListBlank.cons 𝟙 (ListBlank.cons 𝟘 (R (pow4 k (f m k).bit1).succ))))) := by
  refine (LaR_max hm _).trans ?_
  rw [R_ff]
  exact eat_bin_max k (Has0.bit0 (f m k)) (Has0.bit1 (has0_f m k)) l

/-! ### Leading-bits invariant (Coq `leads`) -/

/-- Coq `leads'`: `n = 1`, or `n` starts (MSB-first) with `11`. -/
inductive leads' : PosNum → Prop where
  | one : leads' 1
  | bit1 {n : PosNum} : leads' n → leads' n.bit1
  | bit0 {n : PosNum} : leads' n → n ≠ 1 → leads' n.bit0

/-- Coq `leads`. -/
def leads (n : ℕ) : Prop := ∃ p : PosNum, (p : ℕ) = n ∧ leads' p

lemma leads_add0_rev {n : PosNum} (h : leads' n.bit0) : leads' n := by
  cases h; assumption

lemma leads_pow2_rev {n : PosNum} {k : ℕ} (h : leads' ((pow2' k) * n)) : leads' n := by
  induction k with
  | zero => rw [show pow2' 0 = 1 from rfl, one_mul] at h; exact h
  | succ k ih =>
      apply ih
      apply leads_add0_rev
      rw [show pow2' (k + 1) = (pow2' k).bit0 from rfl,
          show (pow2' k).bit0 * n = (pow2' k * n).bit0 from by
            apply PosNum.to_nat_inj.mp; push_cast; ring] at h
      exact h

lemma leads_pow2 {k : ℕ} (h : leads' (pow2' k)) : k = 0 := by
  induction k with
  | zero => rfl
  | succ k ih =>
      exfalso
      rw [show pow2' (k + 1) = (pow2' k).bit0 from rfl] at h
      cases h with
      | bit0 h1 h2 => exact h2 (by rw [ih h1]; rfl)

lemma leads_3_pow2 (q : ℕ) : leads' (3 * pow2' q) := by
  induction q with
  | zero => exact leads'.bit1 leads'.one
  | succ q ih =>
      rw [show pow2' (q + 1) = (pow2' q).bit0 from rfl,
          show (3 : PosNum) * (pow2' q).bit0 = (3 * pow2' q).bit0 from by
            apply PosNum.to_nat_inj.mp; push_cast; ring]
      refine leads'.bit0 ih ?_
      intro hcontra
      have hc : ((3 * pow2' q : PosNum) : ℕ) = 3 * 2 ^ q := by
        rw [PosNum.cast_mul, pow2'_cast]; rfl
      rw [hcontra] at hc
      simp only [PosNum.cast_one] at hc
      have h2 : 1 ≤ 2 ^ q := Nat.one_le_two_pow
      omega

lemma leads_3_pow2_r {q : ℕ} {r : PosNum} (h : (r : ℕ) < 2 ^ q) : leads' (3 * pow2' q + r) := by
  induction q generalizing r with
  | zero =>
      exfalso
      have h1 : 1 ≤ (r : ℕ) := r.one_le_cast
      simp only [pow_zero] at h; omega
  | succ k ih =>
      rw [show pow2' (k + 1) = (pow2' k).bit0 from rfl,
          show (3 : PosNum) * (pow2' k).bit0 = (3 * pow2' k).bit0 from by
            apply PosNum.to_nat_inj.mp; push_cast; ring]
      have h2 : (1 : ℕ) ≤ 2 ^ k := Nat.one_le_two_pow
      cases r with
      | one =>
          rw [show (3 * pow2' k).bit0 + PosNum.one = (3 * pow2' k).bit1 from rfl]
          exact leads'.bit1 (leads_3_pow2 k)
      | bit0 r' =>
          rw [show (3 * pow2' k).bit0 + r'.bit0 = (3 * pow2' k + r').bit0 from by
                apply PosNum.to_nat_inj.mp; push_cast; ring]
          have hr : ((r'.bit0 : PosNum) : ℕ) < 2 ^ (k + 1) := h
          rw [PosNum.cast_bit0, pow_succ] at hr
          refine leads'.bit0 (ih (by omega)) ?_
          intro hc
          have hcast : ((3 * pow2' k + r' : PosNum) : ℕ) = ((1 : PosNum) : ℕ) := by rw [hc]
          rw [PosNum.cast_add, PosNum.cast_mul, pow2'_cast, PosNum.cast_one] at hcast
          have h3 : 1 ≤ (r' : ℕ) := r'.one_le_cast
          have h4 : 1 ≤ ((3 : PosNum) : ℕ) := PosNum.one_le_cast 3
          nlinarith
      | bit1 r' =>
          rw [show (3 * pow2' k).bit0 + r'.bit1 = (3 * pow2' k + r').bit1 from by
                apply PosNum.to_nat_inj.mp; push_cast; ring]
          have hr : ((r'.bit1 : PosNum) : ℕ) < 2 ^ (k + 1) := h
          rw [PosNum.cast_bit1, pow_succ] at hr
          exact leads'.bit1 (ih (by omega))

/-- `((3 * pow2' q : PosNum) : ℕ) = 3 * 2 ^ q`. -/
lemma cast_3pow2 (q : ℕ) : ((3 * pow2' q : PosNum) : ℕ) = 3 * 2 ^ q := by
  rw [PosNum.cast_mul, pow2'_cast]; rfl

/-- `((3 * pow2' q + r : PosNum) : ℕ) = 3 * 2 ^ q + (r : ℕ)`. -/
lemma cast_3pow2_add (q : ℕ) (r : PosNum) :
    ((3 * pow2' q + r : PosNum) : ℕ) = 3 * 2 ^ q + (r : ℕ) := by
  rw [PosNum.cast_add, cast_3pow2]

/-- Any positive natural number is realized by some `PosNum`. -/
lemma exists_posNum (r : ℕ) (h : 0 < r) : ∃ p : PosNum, (p : ℕ) = r := by
  induction r with
  | zero => omega
  | succ n ih =>
      rcases Nat.eq_zero_or_pos n with hn | hn
      · exact ⟨1, by simp [hn]⟩
      · obtain ⟨p, hp⟩ := ih hn
        exact ⟨p.succ, by rw [PosNum.cast_succ, hp]⟩

/-
Pure arithmetic core of `step_reset`'s reset-invariant preservation.
-/
lemma reset_arith {q r k p : ℕ} (hrlt : r < 2 ^ q) (h2n : 2 * (2 ^ k + 2 ^ (k + 1) * p) ≤ r) :
    ∃ (q' r' : ℕ),
      2 ^ (2 * k) * (4 * ((3 * 2 ^ q + r) - 2 * (2 ^ k - 1)) + 3) - 2 = 3 * 2 ^ q' + r'
        ∧ 2 * p ≤ r' ∧ r' < 2 ^ q' := by
  refine' ⟨ q + 2 * k + 2, _, _, _, _ ⟩;
  exact 2 ^ ( 2 * k ) * ( 4 * r - 8 * 2 ^ k + 11 ) - 2;
  · have hc : (1:ℕ) ≤ 2 ^ k := Nat.one_le_two_pow
    have hr2c : 2 * 2 ^ k ≤ r := by
      have : 2 * 2 ^ k ≤ 2 * (2 ^ k + 2 ^ (k + 1) * p) := by
        nlinarith [Nat.zero_le (2 ^ (k + 1) * p)]
      omega
    have hpowq : 2 ^ (q + 2 * k + 2) = 4 * (2 ^ (2 * k) * 2 ^ q) := by
      rw [pow_add, pow_add]; ring
    set a := 2 ^ (2 * k) with ha
    set b := 2 ^ q with hb
    have ha1 : 1 ≤ a := Nat.one_le_two_pow
    set s := 4 * r - 8 * 2 ^ k + 11 with hs
    have key : 4 * (3 * b + r - 2 * (2 ^ k - 1)) + 3 = 12 * b + s := by rw [hs]; omega
    have hexp : a * (12 * b + s) = 12 * (a * b) + a * s := by ring
    have hY : 2 ≤ a * s := by
      have hs11 : 11 ≤ s := by omega
      nlinarith
    rw [hpowq, key, hexp]
    omega
  · refine' le_tsub_of_add_le_left _;
    ring_nf at *;
    nlinarith [ pow_pos ( by decide : 0 < 2 ) k, pow_pos ( by decide : 0 < 2 ) ( k * 2 ), Nat.sub_add_cancel ( show 2 ^ k * 8 ≤ r * 4 from by nlinarith [ pow_pos ( by decide : 0 < 2 ) k ] ) ];
  · rw [ tsub_lt_iff_left ];
    · norm_num [ pow_add ] at *;
      nlinarith [ pow_pos ( by decide : 0 < 2 ) k, pow_pos ( by decide : 0 < 2 ) ( 2 * k ), Nat.sub_add_cancel ( show 8 * 2 ^ k ≤ 4 * r from by nlinarith [ pow_pos ( by decide : 0 < 2 ) k ] ) ];
    · exact le_trans ( by norm_num ) ( Nat.mul_le_mul ( Nat.one_le_pow _ _ ( by norm_num ) ) ( Nat.le_add_left _ _ ) )

/-- Coq `reset_invariant`. -/
def reset_invariant (n m : PosNum) : Prop :=
  leads' n ∧ ∃ (q : ℕ) (r : PosNum),
    (b m : ℕ) = ((3 * pow2' q + r : PosNum) : ℕ) ∧ 2 * (n : ℕ) ≤ (r : ℕ) ∧ (r : ℕ) < 2 ^ q

lemma reset_invariant_leads_b_m {n m : PosNum} (h : reset_invariant n m) : leads (b m) := by
  obtain ⟨_, q, r, h1, _, h3⟩ := h
  exact ⟨3 * pow2' q + r, h1.symm, leads_3_pow2_r h3⟩

/-- Coq `step_reset_odd`. -/
lemma step_reset_odd (n m : PosNum) : E n.bit1 m -[M]->* E n (m.bit1.bit0) := by
  unfold E
  rw [show K' n.bit1 = ListBlank.cons 𝟘 (ListBlank.cons 𝟘 (ListBlank.cons 𝟙 (ListBlank.cons 𝟘 (K' n)))) from rfl, headL_cons]
  evsteps step_left_mk' gC0 _ _, step_left_mk' gD0 _ _, step_right_mk' gE1 _ _, step_right_mk' gE1 _ _, step_right_mk' gE1 _ _, step_right_mk' gE1 _ _, step_left_mk' gE0 _ _, step_left_mk' gA1 _ _, step_left_mk' gC1 _ _, step_left_mk' gA1 _ _, step_left_mk' gC1 _ _, step_right_mk' gA0 _ _, step_right_mk' gB0 _ _, step_left_mk' gC1 _ _, step_right_mk' gA0 _ _, step_right_mk' gB0 _ _, step_left_mk' gC0 _ _, step_left_mk' gD0 _ _, step_right_mk' gE1 _ _, step_right_mk' gE1 _ _, step_right_mk' gE1 _ _, step_right_mk' gE1 _ _, step_right_mk' gE1 _ _, step_right_mk' gE1 _ _, step_left_mk' gE0 _ _, step_left_mk' gA1 _ _, step_left_mk' gC1 _ _, step_left_mk' gA1 _ _, step_left_mk' gC1 _ _, step_left_mk' gA1 _ _, step_left_mk' gC1 _ _, step_left_head gA1 _ _

/-- Coq `step_reset`. -/
lemma step_reset (n m : PosNum) (hn1 : n ≠ 1) (hinv : reset_invariant n m) :
    ∃ (n' m' : PosNum), (E n m -[M]->* E n' m') ∧ (n' : ℕ) < (n : ℕ) ∧ reset_invariant n' m' := by
  obtain ⟨hlead, q, r, hbm, h2n, hrlt⟩ := hinv
  have hbm' : b m = 3 * 2 ^ q + (r : ℕ) := hbm.trans (cast_3pow2_add q r)
  obtain ⟨k, n', hK, hn⟩ := prepare_K (Num.pos n) (by have h : 1 ≤ (n : ℕ) := n.one_le_cast; simp only [Num.cast_pos]; omega)
  simp only [Num.cast_pos] at hn
  cases n' with
  | zero =>
      exfalso
      have hnk : (n : ℕ) = 2 ^ k := by simpa using hn
      have hnp : n = pow2' k := PosNum.to_nat_inj.mp (by rw [hnk, pow2'_cast])
      subst hnp
      have hk0 : k = 0 := leads_pow2 hlead
      subst hk0
      exact hn1 rfl
  | pos p =>
      have hnp : (n : ℕ) = 2 ^ k + 2 ^ (k + 1) * (p : ℕ) := by simpa using hn
      have h2k : (1 : ℕ) ≤ 2 ^ k := Nat.one_le_two_pow
      have hrle : (r : ℕ) ≤ b m := by rw [hbm']; omega
      have hkn : 2 ^ k ≤ (n : ℕ) := by rw [hnp]; omega
      have hbound : 2 * (2 ^ k - 1) ≤ b m := by omega
      refine ⟨p, (pow4 k (f m k).bit1).succ, ?_, ?_, ?_⟩
      · show E n m -[M]->* E p (pow4 k (f m k).bit1).succ
        unfold E
        rw [show K' n = K (Num.pos n) from rfl, hK]
        exact drop_KI hbound (K (Num.pos p))
      · rw [hnp]
        have h1 : (1 : ℕ) ≤ 2 ^ (k + 1) := Nat.one_le_two_pow
        have hp1 : (1 : ℕ) ≤ (p : ℕ) := p.one_le_cast
        nlinarith [h1, hp1]
      · refine ⟨?_, ?_⟩
        · have hnn : n = pow2' k * (PosNum.bit1 p) := by
            apply PosNum.to_nat_inj.mp
            rw [hnp]; push_cast [pow2'_cast]; ring
          rw [hnn] at hlead
          cases leads_pow2_rev hlead with
          | bit1 hlp => exact hlp
        · have hbt : b (addN (2 * (2 ^ k - 1)) m) = b m - 2 * (2 ^ k - 1) := b_add _ hbound
          have hbfk : b (f m k) = 2 * (b m - 2 * (2 ^ k - 1)) + 1 := by
            rw [f]; show b (PosNum.bit0 _) = _; simp only [b]; rw [hbt]
          have hbfk1 : b ((f m k).bit1) = 2 * (2 * (b m - 2 * (2 ^ k - 1)) + 1) := by
            show b (PosNum.bit1 _) = _; simp only [b]; rw [hbfk]
          have hbpow : b (pow4 k (f m k).bit1)
              = 2 ^ (2 * k) * (2 * (2 * (b m - 2 * (2 ^ k - 1)) + 1) + 1) - 1 := by
            rw [b_pow4, hbfk1]
          have hppos : 0 < b (pow4 k (f m k).bit1) := by
            rw [hbpow]
            have h := Nat.one_le_two_pow (n := 2 * k)
            have hi : 3 ≤ 2 * (2 * (b m - 2 * (2 ^ k - 1)) + 1) + 1 := by omega
            have hge : 3 ≤ 2 ^ (2 * k) * (2 * (2 * (b m - 2 * (2 ^ k - 1)) + 1) + 1) := by
              nlinarith [h, hi]
            omega
          have hbmm : b (pow4 k (f m k).bit1).succ
              = 2 ^ (2 * k) * (4 * (b m - 2 * (2 ^ k - 1)) + 3) - 2 := by
            rw [b_succ hppos, hbpow]
            have hz : 2 * (2 * (b m - 2 * (2 ^ k - 1)) + 1) + 1
                = 4 * (b m - 2 * (2 ^ k - 1)) + 3 := by ring
            rw [hz]; omega
          rw [hbm'] at hbmm
          obtain ⟨q', r', harith, h2p, hr'lt⟩ := reset_arith hrlt (by rw [← hnp]; exact h2n)
          have hr'pos : 0 < r' := by
            have hp1 : (1 : ℕ) ≤ (p : ℕ) := p.one_le_cast; omega
          obtain ⟨rp, hrp⟩ := exists_posNum r' hr'pos
          refine ⟨q', rp, ?_, ?_, ?_⟩
          · rw [hbmm, harith, cast_3pow2_add, hrp]
          · rw [hrp]; exact h2p
          · rw [hrp]; exact hr'lt

/-- Coq `do_reset`. -/
lemma do_reset (n m : PosNum) (hinv : reset_invariant n m) :
    ∃ m' : PosNum, (E n m -[M]->* E 1 m') ∧ leads (b m') := by
  have H : ∀ k : ℕ, ∀ (n m : PosNum), (n : ℕ) = k → reset_invariant n m →
      ∃ m' : PosNum, (E n m -[M]->* E 1 m') ∧ leads (b m') := by
    intro k
    induction k using Nat.strong_induction_on with
    | _ k ih =>
      intro n m hk hinv
      by_cases hn1 : n = 1
      · subst hn1; exact ⟨m, Machine.EvStep.refl, reset_invariant_leads_b_m hinv⟩
      · obtain ⟨n', m', hstep, hlt, hinv'⟩ := step_reset n m hn1 hinv
        obtain ⟨m'', hstep', hleads'⟩ := ih (n' : ℕ) (by omega) n' m' rfl hinv'
        exact ⟨m'', hstep.trans hstep', hleads'⟩
  exact H (n : ℕ) n m rfl hinv

/-- Coq `E_start`. -/
lemma E_start (m : PosNum) : E 1 m -[M]->+ D 0 m.bit1 := by
  unfold E
  rw [show K' 1 = ListBlank.cons 𝟘 (ListBlank.cons 𝟘 (ListBlank.cons 𝟙 ∅)) from rfl, headL_cons]
  refine Trans.trans (Machine.Progress.single (step_left_mk' gC0 _ _)) (?_ : _ -[M]->* _)
  evsteps step_left_mk' gD0 _ _, step_right_mk' gE1 _ _, step_right_mk' gE1 _ _, step_right_mk' gE1 _ _, step_right_mk' gE1 _ _, step_left_mk' gE0 _ _, step_left_mk' gA1 _ _, step_left_mk' gC1 _ _, step_left_mk' gA1 _ _, step_left_edge gC1 _, step_right_mk' gA0 _ _, step_right_mk' gB0 _ _, step_left_mk' gC1 _ _, step_right_mk' gA0 _ _, step_right_mk' gB0 _ _, step_left_mk' gC0 _ _, step_left_mk' gD0 _ _, step_right_mk' gE1 _ _, step_right_mk' gE1 _ _, step_right_mk' gE1 _ _, step_right_mk' gE1 _ _, step_right_mk' gE1 _ _, step_right_mk' gE1 _ _, step_left_mk' gE0 _ _, step_left_mk' gA1 _ _, step_left_mk' gC1 _ _, step_left_mk' gA1 _ _, step_left_mk' gC1 _ _, step_left_mk' gA1 _ _, step_left_mk' gC1 _ _, step_left_edge gA1 _

/-
Coq `E_next`.
-/
lemma E_next (m : PosNum) (h : leads (b m)) :
    ∃ m' : PosNum, (E 1 m -[M]->+ E 1 m') ∧ leads (b m') := by
  -- Apply the lemma `do_reset` to obtain the required `m'` and the leading condition for `b m'`.
  obtain ⟨bm, hbm, hlead⟩ := h
  obtain ⟨k, hk⟩ := b_add_pow2 m
  have hkcast : b m + m + 1 = 2^k := by
    convert congr_arg ( fun x : PosNum => ( x : ℕ ) ) hk using 1;
    · simp +decide [ addN_cast, PosNum.cast_succ ];
    · exact (pow2'_cast k).symm
  have hx : (bm + m).succ = pow2' k := by
    refine' PosNum.to_nat_inj.mp _;
    simp +decide [ ← hk, hbm, addN_cast ]
  have hbm2 : b m.bit1 = 2 * b m := rfl
  -- Prove that $b M0 = 3 * 2^{k+2} + (2^{k+2} - 7)$
  have hM0 : b ((bm + m).succ.bit0.bit1.bit1.bit0) = 3 * 2^(k+2) + (2^(k+2) - 7) := by
    rw [ hx ];
    simp +arith +decide [ b, pow_succ' ];
    rw [ show b ( pow2' k ) = 2 ^ k - 1 from b_pow2 k ];
    linarith [ Nat.sub_add_cancel ( show 1 ≤ 2 ^ k from Nat.one_le_pow _ _ ( by decide ) ), Nat.sub_add_cancel ( show 7 ≤ 4 * 2 ^ k from by linarith [ Nat.pow_le_pow_right ( by decide : 1 ≤ 2 ) ( show k ≥ 1 from Nat.pos_of_ne_zero ( by rintro rfl; linarith [ show ( b m : ℕ ) ≥ 0 from Nat.zero_le _, show ( m : ℕ ) ≥ 1 from m.one_le_cast ] ) ) ] ) ];
  -- Prove that $reset_invariant bm M0$
  have hinv : reset_invariant bm ((bm + m).succ.bit0.bit1.bit1.bit0) := by
    refine' ⟨ hlead, k + 2, _ ⟩;
    -- Let `r = 2^(k+2) - 7`. Prove `(r:ℕ) = 2^(k+2) - 7` (use `Nat.sub_add_cancel`), then prove the two bounds `2*(bm:ℕ) ≤ (r:ℕ)` and `(r:ℕ) < 2^(k+2)` via `omega` (with `hbm`, `hkcast`, `hbm2`, `Nat.one_le_two_pow`, and `m.one_le_cast`).
    use (Deciders.Skelet.Skelet33.exists_posNum (2^(k+2)-7) (by
    rcases k with ( _ | _ | k ) <;> simp_all +arith +decide [ Nat.pow_succ' ];
    grind)).choose
    generalize_proofs at *;
    rename_i h; have := h.choose_spec; simp_all +decide [ pow_succ' ] ;
    exact le_tsub_of_add_le_left ( by linarith [ show ( m : ℕ ) ≥ 1 from m.one_le_cast ] );
  obtain ⟨ m', hfin, hleads' ⟩ := do_reset bm _ hinv;
  have hDf : D 0 m.bit1 -[M]->* D (b m.bit1 : Num) (addN (b m.bit1) m.bit1) := by
    convert D_finish using 1;
    norm_num;
  have hidx : succPos (b m.bit1 : Num) = bm.bit1 := by
    refine' PosNum.to_nat_inj.mp _;
    simp +decide [ hbm2, hbm ];
    simp +decide [ ← two_mul, succPos_cast ]
  have hma : (addN (b m.bit1) m.bit1).succ = ((bm + m).succ).bit0 := by
    apply PosNum.to_nat_inj.mp; simp [hbm2, addN_cast, hbm]; ring;
  have hall : All1 (addN (b m.bit1) m.bit1) := by
    exact b0_all1 ( b_add_self _ );
  have := start_reset ( b m.bit1 : Num ) hall; simp_all +decide ;
  exact ⟨ m', by exact Trans.trans ( E_start m ) ( hDf.trans this ) |> fun h => Trans.trans h ( step_reset_odd _ _ ) |> fun h => Trans.trans h hfin, hleads' ⟩

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

/-- `init` reaches `E 1 17` (Coq `c0 -->* E 1 17`). -/
lemma enters : init -[M]->* E 1 17 := by
  refine stepN_evstep 175 ?_
  decide

lemma leads_b_17 : leads (b 17) := by
  refine ⟨PosNum.bit0 (PosNum.bit1 (PosNum.bit1 PosNum.one)), ?_, ?_⟩
  · decide
  · exact leads'.bit0 (leads'.bit1 (leads'.bit1 leads'.one)) (by decide)

/-- Skelet #33 (`sporadicMachine10`) does not halt (Coq `nonhalt`). -/
theorem nonHalting : ¬ M.halts init := by
  have cs : ClosedSet M (fun C => ∃ m : PosNum, C = E 1 m ∧ leads (b m)) init := by
    refine ⟨?_, ?_⟩
    · rintro ⟨C, m, rfl, hm⟩
      obtain ⟨m', hstep, hm'⟩ := E_next m hm
      exact ⟨⟨E 1 m', m', rfl, hm'⟩, hstep⟩
    · exact ⟨⟨E 1 17, 17, rfl, leads_b_17⟩, enters⟩
  exact cs.nonHalting

end Deciders.Skelet.Skelet33
