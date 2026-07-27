import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Cases
import Busybeaver.Deciders.Skelet.EvStepTactics
import Busybeaver.TM.Table.Parse
import Busybeaver.Deciders.Skelet.ShiftOverflowBins
import Busybeaver.Deciders.Skelet.TapeCalc
import Busybeaver.Deciders.Skelet.Skelet26

/-!
## Skelet #34 (`sporadicMachine11`) development

A Lean port of `Coq-BB5/BusyCoq/Skelet34.v` (sligocki's Skelet #34 analysis).
Skelet #34 is another shift-overflow binary counter, sharing the `FixedBin` /
`ShiftOverflow` / `ShiftOverflowBins` arithmetic and tape encodings with Skelet
#26, and even reusing the pure combinatorial helpers `f`, `f_lt`, `has0_f`,
`R_f`, `prepare_K` from the Skelet #26 development.  Its reset is a single
`E`-sweep (no `J`/`E0`/`E1` split), so the argument is shorter than #26.
-/
open Turing
open TM.Table
open Deciders.Skelet.ShiftOverflowBins
open Deciders.Skelet.ShiftOverflow
open Deciders.Skelet.FixedBin

namespace Deciders.Skelet.Skelet34

open Deciders.Skelet.Skelet26 (f f1 f_as_f1 has0_f f_lt R_f prepare_K)

abbrev M : Machine 4 1 := mach["1RB1LC_0RC0RB_1LD0LA_1LE---_1LA1RA"]

local notation "𝟙" => (1 : Symbol 1)
local notation "𝟘" => (0 : Symbol 1)

-- Transitions (A=0, B=1, C=2, D=3, E=4).
lemma gA0 : M.get 0 0 = .next 1 .right 1 := by decide
lemma gA1 : M.get 0 1 = .next 1 .left 2 := by decide
lemma gB0 : M.get 1 0 = .next 0 .right 2 := by decide
lemma gB1 : M.get 1 1 = .next 0 .right 1 := by decide
lemma gC0 : M.get 2 0 = .next 1 .left 3 := by decide
lemma gC1 : M.get 2 1 = .next 0 .left 0 := by decide
lemma gD0 : M.get 3 0 = .next 1 .left 4 := by decide
lemma gE0 : M.get 4 0 = .next 1 .left 0 := by decide
lemma gE1 : M.get 4 1 = .next 1 .right 0 := by decide
-- blank-edge
lemma gA0d : M.get 0 default = .next 1 .right 1 := by decide
lemma gB0d : M.get 1 default = .next 0 .right 2 := by decide
lemma gC0d : M.get 2 default = .next 1 .left 3 := by decide
lemma gD0d : M.get 3 default = .next 1 .left 4 := by decide
lemma gE0d : M.get 4 default = .next 1 .left 0 := by decide

/-- Rightward directed configuration (Coq `l {{q}}> r`). -/
def headR (q : Label 4) (L R : ListBlank (Symbol 1)) : Config 4 1 := ⟨q, Tape.mk' L R⟩

open TM.Table (headL)

/-- The counter configuration `D n m` (Coq `D`): `L n <{{C}} [1;0;1;0] *> R m`. -/
def D (n : Num) (m : PosNum) : Config 4 1 :=
  headL 2 (L n) (ListBlank.cons 𝟙 (ListBlank.cons 𝟘 (ListBlank.cons 𝟙 (ListBlank.cons 𝟘 (R m)))))

/-- The reset configuration `E n a m` (Coq `E`): `K n <{{C}} [1;0;1;a] *> R m`. -/
def E (n : Num) (a : Symbol 1) (m : PosNum) : Config 4 1 :=
  headL 2 (K n) (ListBlank.cons 𝟙 (ListBlank.cons 𝟘 (ListBlank.cons 𝟙 (ListBlank.cons a (R m)))))

/-
Left counter increment sweep, base case `n = 0` (Coq `L_inc`, `N0` case).
-/
lemma L_inc_zero (r : ListBlank (Symbol 1)) :
    headL 2 (L 0) r -[M]->* headR 1 (L' .one) r := by
  rw [show (L 0) = (∅ : ListBlank (Symbol 1)) from rfl, TM.Table.headL_empty]
  simp only [L', headR]
  evsteps step_left_edge gC0 r, step_left_edge gD0 _, step_left_edge gE0 _, step_right_mk' gA0 _ _, step_right_mk' gB1 _ _, step_right_mk' gB1 _ _, step_right_mk' gB1 _ _

/-- `headL` over a positive left-counter body `L' k`, in explicit `Tape.mk'` form
(uses `L'_as_K'`). -/
lemma headL_L' (k : PosNum) (R : ListBlank (Symbol 1)) :
    headL 2 (L' k) R
      = (⟨2, Tape.mk' (K' k) (ListBlank.cons (0 : Symbol 1) R)⟩ : Config 4 1) := by
  rw [L'_as_K']; simp [headL_cons]

/-- Left counter increment sweep on a positive counter (Coq `L_inc`, positive part). -/
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

/-- Left counter increment sweep (Coq `L_inc`). -/
lemma L_inc (n : Num) (r : ListBlank (Symbol 1)) :
    headL 2 (L n) r -[M]->* headR 1 (L (Num.succ n)) r := by
  cases n with
  | zero => exact L_inc_zero r
  | pos p => exact L'_inc p r

/-- Right counter increment with no overflow (Coq `R_inc_has0`). -/
lemma R_inc_has0 {n : PosNum} (h : Has0 n) (l : ListBlank (Symbol 1)) :
    headR 2 (ListBlank.cons 𝟘 l) (R n) -[M]->* headL 0 l (ListBlank.cons 𝟘 (R n.succ)) := by
  induction h generalizing l with
  | bit0 n =>
      show headR 2 (ListBlank.cons 𝟘 l) (ListBlank.cons 𝟙 (ListBlank.cons 𝟘 (R n)))
        -[M]->* headL 0 l (ListBlank.cons 𝟘 (ListBlank.cons 𝟙 (ListBlank.cons 𝟙 (R n))))
      evsteps step_left_mk' gC1 _ _, step_right_mk' gA0 _ _, step_right_mk' gB0 _ _, step_left_mk' gC0 _ _, step_left_mk' gD0 _ _, step_right_mk' gE1 _ _, step_left_mk' gA1 _ _, step_left_head gC1 _ _
  | @bit1 n h ih =>
      show headR 2 (ListBlank.cons 𝟘 l) (ListBlank.cons 𝟙 (ListBlank.cons 𝟙 (R n)))
        -[M]->* headL 0 l (ListBlank.cons 𝟘 (ListBlank.cons 𝟙 (ListBlank.cons 𝟘 (R n.succ))))
      evchain step_left_mk' gC1 _ _, step_right_mk' gA0 _ _, step_right_mk' gB0 _ _, step_left_mk' gC1 _ _, step_right_mk' gA0 _ _, step_right_mk' gB0 _ _
      refine (ih (ListBlank.cons 𝟙 (ListBlank.cons 𝟙 l))).trans ?_
      rw [headL_cons]
      evsteps step_left_mk' gA1 _ _, step_left_head gC1 _ _

/-- One counter increment (Coq `D_inc`). -/
lemma D_inc {n : Num} {m : PosNum} (h : Has0 m) :
    D n m -[M]->* D (Num.succ n) m.succ := by
  unfold D
  refine (L_inc n _).trans ?_
  evchain step_right_mk' gB1 _ _, step_right_mk' gB0 _ _, step_left_mk' gC1 _ _, step_right_mk' gA0 _ _, step_right_mk' gB0 _ _, step_left_mk' gC0 _ _, step_left_mk' gD0 _ _, step_right_mk' gE1 _ _, step_left_mk' gA1 _ _, step_left_mk' gC1 _ _, step_right_mk' gA0 _ _, step_right_mk' gB0 _ _, step_left_mk' gC1 _ _, step_right_mk' gA0 _ _, step_right_mk' gB0 _ _, step_left_mk' gC1 _ _, step_right_mk' gA0 _ _, step_right_mk' gB0 _ _
  refine (R_inc_has0 h _).trans ?_
  rw [headL_cons]
  evsteps step_left_mk' gA1 _ _, step_left_mk' gC1 _ _, step_left_head gA1 _ _

/-
Iterated increment by `u ≤ b m` (Coq `D_run`).
-/
lemma D_run {n : Num} {m : PosNum} (u : ℕ) (hu : u ≤ b m) :
    D n m -[M]->* D ((u : Num) + n) (addN u m) := by
  induction' u with u ih generalizing n m;
  · simpa using Machine.EvStep.refl
  · -- From `hu : u+1 ≤ b m` get `hbm : 0 < b m` by omega.
    have hbm : 0 < b m := by
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

/-- Right counter increment with overflow (Coq `R_inc_all1`). -/
lemma R_inc_all1 {n : PosNum} (h : All1 n) (l : ListBlank (Symbol 1)) :
    headR 2 (ListBlank.cons 𝟘 l) (R n) -[M]->* headL 2 l (R n.succ) := by
  induction h generalizing l with
  | one =>
      show headR 2 (ListBlank.cons 𝟘 l) (ListBlank.cons 𝟙 (ListBlank.cons 𝟙 ∅))
        -[M]->* headL 2 l (ListBlank.cons 𝟙 (ListBlank.cons 𝟘 (ListBlank.cons 𝟙 (ListBlank.cons 𝟙 ∅))))
      evsteps step_left_mk' gC1 _ _, step_right_mk' gA0 _ _, step_right_mk' gB0 _ _, step_left_mk' gC1 _ _, step_right_mk' gA0 _ _, step_right_mk' gB0 _ _, step_left_blank gC0d _, step_left_mk' gD0 _ _, step_right_mk' gE1 _ _, step_left_mk' gA1 _ _, step_left_mk' gC1 _ _, step_left_head gA1 _ _
  | @bit1 m hm ih =>
      show headR 2 (ListBlank.cons 𝟘 l) (ListBlank.cons 𝟙 (ListBlank.cons 𝟙 (R m)))
        -[M]->* headL 2 l (ListBlank.cons 𝟙 (ListBlank.cons 𝟘 (R m.succ)))
      evchain step_left_mk' gC1 _ _, step_right_mk' gA0 _ _, step_right_mk' gB0 _ _, step_left_mk' gC1 _ _, step_right_mk' gA0 _ _, step_right_mk' gB0 _ _
      refine (ih (ListBlank.cons 𝟙 (ListBlank.cons 𝟙 l))).trans ?_
      rw [headL_cons]
      evsteps step_left_mk' gC1 _ _, step_left_head gA1 _ _

/-- Start of the reset cycle (Coq `start_reset`). -/
lemma start_reset (n : Num) {m : PosNum} (h : All1 m) :
    D n m -[M]->* E (Num.succ n) 1 m.succ := by
  unfold D
  refine (L_inc n _).trans ?_
  rw [L_as_K]
  evchain step_right_mk' gB1 _ _, step_right_mk' gB0 _ _, step_left_mk' gC1 _ _, step_right_mk' gA0 _ _, step_right_mk' gB0 _ _, step_left_mk' gC0 _ _, step_left_mk' gD0 _ _, step_right_mk' gE1 _ _, step_left_mk' gA1 _ _, step_left_mk' gC1 _ _, step_right_mk' gA0 _ _, step_right_mk' gB0 _ _, step_left_mk' gC1 _ _, step_right_mk' gA0 _ _, step_right_mk' gB0 _ _, step_left_mk' gC1 _ _, step_right_mk' gA0 _ _, step_right_mk' gB0 _ _
  refine (R_inc_all1 h _).trans ?_
  rw [headL_cons]
  evsteps step_left_mk' gC1 _ _, step_left_mk' gA1 _ _, step_left_mk' gC1 _ _, step_right_mk' gA0 _ _, step_right_mk' gB0 _ _, step_left_mk' gC1 _ _, step_right_mk' gA0 _ _, step_right_mk' gB0 _ _, step_left_mk' gC0 _ _, step_left_mk' gD0 _ _, step_right_mk' gE1 _ _, step_left_mk' gA1 _ _, step_left_mk' gC1 _ _, step_left_head gA1 _ _

/-- `start_reset` as a strict-progress step (Coq `start_reset'`). -/
lemma start_reset' (n : Num) {m : PosNum} (h : All1 m) :
    D n m -[M]->+ E (Num.succ n) 1 m.succ := by
  unfold D
  refine Trans.trans (L_inc n _) (?_ : _ -[M]->+ _)
  rw [L_as_K]
  refine Trans.trans (Machine.Progress.single (step_right_mk' gB1 _ _)) (?_ : _ -[M]->* _)
  evchain step_right_mk' gB0 _ _, step_left_mk' gC1 _ _, step_right_mk' gA0 _ _, step_right_mk' gB0 _ _, step_left_mk' gC0 _ _, step_left_mk' gD0 _ _, step_right_mk' gE1 _ _, step_left_mk' gA1 _ _, step_left_mk' gC1 _ _, step_right_mk' gA0 _ _, step_right_mk' gB0 _ _, step_left_mk' gC1 _ _, step_right_mk' gA0 _ _, step_right_mk' gB0 _ _, step_left_mk' gC1 _ _, step_right_mk' gA0 _ _, step_right_mk' gB0 _ _
  refine (R_inc_all1 h _).trans ?_
  rw [headL_cons]
  evsteps step_left_mk' gC1 _ _, step_left_mk' gA1 _ _, step_left_mk' gC1 _ _, step_right_mk' gA0 _ _, step_right_mk' gB0 _ _, step_left_mk' gC1 _ _, step_right_mk' gA0 _ _, step_right_mk' gB0 _ _, step_left_mk' gC0 _ _, step_left_mk' gD0 _ _, step_right_mk' gE1 _ _, step_left_mk' gA1 _ _, step_left_mk' gC1 _ _, step_left_head gA1 _ _

/-- Coq `eat_LI`. -/
lemma eat_LI (l : side) (t : PosNum) :
    headL 2 (ListBlank.cons 𝟘 (ListBlank.cons 𝟘 (ListBlank.cons 𝟘 (ListBlank.cons 𝟙 l)))) (R t)
      -[M]->* headL 2 l (R t.bit1.bit1) := by
  rw [headL_cons]
  evsteps step_left_mk' gC0 _ _, step_left_mk' gD0 _ _, step_left_mk' gE0 _ _, step_left_head gA1 _ _

/-- Coq `eat_KI`. -/
lemma eat_KI {t : PosNum} (h : Has0 t) (l : side) :
    headL 2 (ListBlank.cons 𝟘 (ListBlank.cons 𝟘 (ListBlank.cons 𝟙 (ListBlank.cons 𝟘 l)))) (R t)
      -[M]->* headL 2 l (R t.succ.bit0.bit0) := by
  rw [headL_cons]
  evchain step_left_mk' gC0 _ _, step_left_mk' gD0 _ _, step_right_mk' gE1 _ _, step_left_mk' gA1 _ _, step_left_mk' gC1 _ _, step_right_mk' gA0 _ _, step_right_mk' gB0 _ _, step_left_mk' gC1 _ _, step_right_mk' gA0 _ _, step_right_mk' gB0 _ _, step_left_mk' gC1 _ _, step_right_mk' gA0 _ _, step_right_mk' gB0 _ _
  refine (R_inc_has0 h _).trans ?_
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
lemma LaR_inc {k : ℕ} (a : Symbol 1) {np ns : Bin k} (hn : Succ np ns) {m : PosNum} (hm : Has0 m)
    (l : side) :
    headL 2 ((Lk np : List (Symbol 1)) ++ l)
        (ListBlank.cons 𝟙 (ListBlank.cons 𝟘 (ListBlank.cons 𝟙 (ListBlank.cons a (R m)))))
      -[M]->* headL 2 ((Lk ns : List (Symbol 1)) ++ l)
        (ListBlank.cons 𝟙 (ListBlank.cons 𝟘 (ListBlank.cons 𝟙 (ListBlank.cons a (R m.succ))))) := by
  match a with
  | 0 =>
      refine (Lk_inc hn l _).trans ?_
      evchain step_right_mk' gB1 _ _, step_right_mk' gB0 _ _, step_left_mk' gC1 _ _, step_right_mk' gA0 _ _, step_right_mk' gB0 _ _, step_left_mk' gC0 _ _, step_left_mk' gD0 _ _, step_right_mk' gE1 _ _, step_left_mk' gA1 _ _, step_left_mk' gC1 _ _, step_right_mk' gA0 _ _, step_right_mk' gB0 _ _, step_left_mk' gC1 _ _, step_right_mk' gA0 _ _, step_right_mk' gB0 _ _, step_left_mk' gC1 _ _, step_right_mk' gA0 _ _, step_right_mk' gB0 _ _
      refine (R_inc_has0 hm _).trans ?_
      rw [headL_cons]
      evsteps step_left_mk' gA1 _ _, step_left_mk' gC1 _ _, step_left_head gA1 _ _
  | 1 =>
      refine (Lk_inc hn l _).trans ?_
      evchain step_right_mk' gB1 _ _, step_right_mk' gB0 _ _, step_left_mk' gC1 _ _, step_right_mk' gA0 _ _, step_right_mk' gB0 _ _, step_left_mk' gC1 _ _, step_right_mk' gA0 _ _, step_right_mk' gB0 _ _
      refine (R_inc_has0 hm _).trans ?_
      rw [headL_cons]
      evsteps step_left_mk' gA1 _ _, step_left_mk' gC1 _ _, step_right_mk' gA0 _ _, step_right_mk' gB0 _ _, step_left_mk' gC1 _ _, step_right_mk' gA0 _ _, step_right_mk' gB0 _ _, step_left_mk' gC0 _ _, step_left_mk' gD0 _ _, step_right_mk' gE1 _ _, step_left_mk' gA1 _ _, step_left_mk' gC1 _ _, step_left_head gA1 _ _

open Deciders.Skelet.FixedBin in
/-- Coq `LaR_incs`. -/
lemma LaR_incs {k : ℕ} (a : Symbol 1) {u : ℕ} {np ns : Bin k} (hp : Plus u np ns) {m : PosNum}
    (hu : u ≤ b m) (l : side) :
    headL 2 ((Lk np : List (Symbol 1)) ++ l)
        (ListBlank.cons 𝟙 (ListBlank.cons 𝟘 (ListBlank.cons 𝟙 (ListBlank.cons a (R m)))))
      -[M]->* headL 2 ((Lk ns : List (Symbol 1)) ++ l)
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
    headL 2 ((Lk (binMin k) : List (Symbol 1)) ++ l)
        (ListBlank.cons 𝟙 (ListBlank.cons 𝟘 (ListBlank.cons 𝟙 (ListBlank.cons a (R m)))))
      -[M]->* headL 2 ((Lk (binMax k) : List (Symbol 1)) ++ l)
        (ListBlank.cons 𝟙 (ListBlank.cons 𝟘 (ListBlank.cons 𝟙 (ListBlank.cons a (R (addN (2 ^ k - 1) m)))))) :=
  LaR_incs a (inc_to_max k) hm l

open Deciders.Skelet.FixedBin in
/-- Coq `eat_bin_max`. -/
lemma eat_bin_max (k : ℕ) {t : PosNum} (h : Has0 t) (l : side) :
    headL 2 ((Lk (binMax k) : List (Symbol 1)) ++
        ListBlank.cons 𝟘 (ListBlank.cons 𝟘 (ListBlank.cons 𝟙 (ListBlank.cons 𝟘 l)))) (R t)
      -[M]->* headL 2 l
        (ListBlank.cons 𝟙 (ListBlank.cons 𝟘 (ListBlank.cons 𝟙 (ListBlank.cons 𝟘 (R (pow4 k t.succ)))))) := by
  induction k generalizing t with
  | zero =>
      simp only [binMax, Lk, ListBlank.append_empty]
      exact eat_KI h l
  | succ k ih =>
      simp only [binMax, Lk, ListBlank.append_cons]
      refine (eat_LI _ t).trans ?_
      exact ih (Has0.bit1 (Has0.bit1 h))

open Deciders.Skelet.FixedBin in
/-- Coq `drop_KI`. -/
lemma drop_KI {k : ℕ} (a : Symbol 1) {m : PosNum} (hm : 2 ^ k - 1 ≤ b m) (l : side) :
    headL 2 ((Lk (binMin k) : List (Symbol 1)) ++
        ListBlank.cons 𝟘 (ListBlank.cons 𝟘 (ListBlank.cons 𝟙 (ListBlank.cons 𝟘 l))))
        (ListBlank.cons 𝟙 (ListBlank.cons 𝟘 (ListBlank.cons 𝟙 (ListBlank.cons a (R m)))))
      -[M]->* headL 2 l
        (ListBlank.cons 𝟙 (ListBlank.cons 𝟘 (ListBlank.cons 𝟙 (ListBlank.cons 𝟘 (R (pow4 k (f m a k).succ)))))) := by
  refine (LaR_max a hm _).trans ?_
  rw [R_f]
  exact eat_bin_max k (has0_f m a k) l

/-- Coq `step_reset`. -/
lemma step_reset (n : Num) (m : PosNum) (a : Symbol 1) (hinv : (n : ℕ) ≤ b m) (hpos : 0 < (n : ℕ)) :
    ∃ (n' : Num) (m' : PosNum),
      (E n a m -[M]->* E n' 0 m') ∧ (n' : ℕ) < (n : ℕ) ∧ (n' : ℕ) ≤ b m' := by
  obtain ⟨k, n', hK, hn⟩ := prepare_K n hpos
  refine ⟨n', pow4 k (f m a k).succ, ?_, ?_, ?_⟩
  · unfold E; rw [hK]; exact drop_KI a (by omega) (K n')
  · nlinarith [Nat.one_le_pow k 2 (by norm_num : 0 < 2),
      Nat.one_le_pow (k + 1) 2 (by norm_num : 0 < 2)]
  · have hbt : b (addN (2 ^ k - 1) m) = b m - (2 ^ k - 1) := by
      apply b_add; omega
    have hbf1 : b (f1 m a k) ≥ 2 * b (addN (2 ^ k - 1) m) := by
      unfold f1; split_ifs <;> simp_all +decide [b]
    have hbm' : b (pow4 k (f m a k).succ) ≥ 2 * b (f1 m a k) := by
      rw [b_pow4]
      rw [show b (f m a k).succ = b (f1 m a k) * 2 from ?_]
      · exact Nat.le_sub_one_of_lt (by
          nlinarith only [Nat.one_le_pow (2 * k) 2 (by norm_num : 0 < 2),
            Nat.zero_le (b (f1 m a k))])
      · rw [show f m a k = (f1 m a k).bit0 from ?_, b_succ]
        · exact Nat.sub_eq_of_eq_add <| by
            rw [show b (f1 m a k |> PosNum.bit0) = 2 * b (f1 m a k) + 1 from rfl]; ring
        · exact Nat.succ_pos _
        · exact f_as_f1 m a k
    have hbm_ge : 2 ^ k - 1 ≤ b m := by omega
    nlinarith [hbt, hbf1, hbm', hinv, hn, pow_succ' 2 k,
      Nat.sub_add_cancel (show 1 ≤ 2 ^ k from Nat.one_le_pow _ _ (by decide)),
      Nat.sub_add_cancel hbm_ge, Nat.zero_le (n' : ℕ), Nat.zero_le (b (f1 m a k)),
      Nat.zero_le (b (addN (2 ^ k - 1) m))]

/-
Coq `do_reset`.
-/
lemma do_reset (n : Num) (m : PosNum) (a : Symbol 1) (hinv : (n : ℕ) ≤ b m) (hpos : 0 < (n : ℕ)) :
    ∃ m' : PosNum, E n a m -[M]->* E 0 0 m' := by
  obtain ⟨ n', m', h ⟩ := step_reset n m a hinv hpos;
  obtain ⟨ h₁, h₂, h₃ ⟩ := h;
  induction' h₂ : ( n' : ℕ ) using Nat.strong_induction_on with k ih generalizing n' m';
  by_cases h₄ : 0 < ( n' : ℕ );
  · obtain ⟨ n'', m'', h₅, h₆, h₇ ⟩ := step_reset n' m' 0 ( by linarith ) h₄;
    exact ih _ ( by linarith ) _ _ ( h₁.trans h₅ ) ( by linarith ) ( by linarith ) rfl;
  · cases n' <;> aesop

/-
Coq `D_next`.
-/
lemma D_next (m : PosNum) : ∃ m' : PosNum, D 0 m -[M]->+ D 0 m' := by
  -- Let `m'' := (addN (b m) m : PosNum).succ`
  let m'' := (addN (b m) m : PosNum).succ;
  -- We obtain a `D finish` step and use it to produce the intermediate configuration `D (b m : Num) (addN (b m) m)`.
  -- Then we `start_reset'` (for `E`) and `do_reset` (for `E` to `E 0 0`) to reach the final `D 0 m'`.
  let finishStep : D 0 m -[M]->* D (b m : Num) (addN (b m) m) := by
    simpa using D_finish (n := 0) (m := m)
  have hreset : ∃ m' : PosNum, D 0 m -[M]->+ D 0 m' := by
    have hall : All1 (addN (b m) m) := b0_all1 (b_add_self m);
    have hsucc : b m'' = ((addN (b m) m : PosNum) : ℕ) := by
      exact b0_succ ( b_add_self m )
    have hle : ((Num.succ (b m : Num) : Num) : ℕ) ≤ b m'' := by
      rw [hsucc];
      simp +arith +decide [ Num.cast_succ, addN_cast ]
    have hpos : 0 < ((Num.succ (b m : Num) : Num) : ℕ) := by
      grind +suggestions
    obtain ⟨m', hsteps⟩ := do_reset (Num.succ (b m : Num)) m'' 1 hle hpos
    use m';
    have c2 : D (b m : Num) (addN (b m) m) -[M]->+ E (Num.succ (b m : Num)) 1 m'' := start_reset' (b m : Num) hall;
    exact Trans.trans (Trans.trans finishStep c2) hsteps;
  exact hreset

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

set_option maxRecDepth 8192 in
/-- `init` reaches `D 0 1441` (Coq `c0 -->* D 0 1441`). -/
lemma enters : init -[M]->* D 0 1441 := by
  refine stepN_evstep 608 ?_
  decide

/-- Skelet #34 (`sporadicMachine11`) does not halt (Coq `nonhalt`). -/
theorem nonHalting : ¬ M.halts init := by
  have cs : ClosedSet M (fun C => ∃ m : PosNum, C = D 0 m) init := by
    refine ⟨?_, ?_⟩
    · rintro ⟨C, m, rfl⟩
      obtain ⟨m', hstep⟩ := D_next m
      exact ⟨⟨D 0 m', m', rfl⟩, hstep⟩
    · exact ⟨⟨D 0 1441, 1441, rfl⟩, enters⟩
  exact cs.nonHalting

end Deciders.Skelet.Skelet34
