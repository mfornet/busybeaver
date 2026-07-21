import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Cases
import Busybeaver.Deciders.BoundExplore
import Busybeaver.Deciders.FAR
import Busybeaver.Deciders.Loop1
import Busybeaver.Deciders.NGramCPS
import Busybeaver.Deciders.RepWL
import Busybeaver.Deciders.WFAR
import Busybeaver.Enumerate.Perm
import Busybeaver.Enumerate.Symmetry
import Busybeaver.TM.Table.Parse
import Busybeaver.Deciders.Skelet.ShiftOverflowBins
import Busybeaver.Deciders.Skelet.Skelet17
import Busybeaver.Deciders.Skelet.TapeCalc
import Busybeaver.Deciders.Skelet.Skelet1.Cycle

/-- `evsteps t₁, …, tₙ` applies `n` consecutive single machine steps via
`Machine.EvStep.step` and closes the chain with `Machine.EvStep.refl`. -/
local syntax "evsteps " term,+ : tactic
local macro_rules
  | `(tactic| evsteps $t:term) =>
      `(tactic| exact TM.Table.Machine.EvStep.step $t TM.Table.Machine.EvStep.refl)
  | `(tactic| evsteps $t:term, $ts:term,*) =>
      `(tactic| refine TM.Table.Machine.EvStep.step $t ?_ <;> evsteps $ts,*)

/-- `evchain t₁, …, tₙ` applies `n` consecutive single machine steps via
`Machine.EvStep.step`, leaving the remaining goal open for further tactics. -/
local syntax "evchain " term,+ : tactic
local macro_rules
  | `(tactic| evchain $t:term) =>
      `(tactic| refine TM.Table.Machine.EvStep.step $t ?_)
  | `(tactic| evchain $t:term, $ts:term,*) =>
      `(tactic| refine TM.Table.Machine.EvStep.step $t ?_ <;> evchain $ts,*)

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
end Skelet26Inline

/-!
## Skelet #34 (`sporadicMachine11`) development

A Lean port of `Coq-BB5/BusyCoq/Skelet34.v` (sligocki's Skelet #34 analysis).
Skelet #34 is another shift-overflow binary counter, sharing the `FixedBin` /
`ShiftOverflow` / `ShiftOverflowBins` arithmetic and tape encodings with Skelet
#26, and even reusing the pure combinatorial helpers `f`, `f_lt`, `has0_f`,
`R_f`, `prepare_K` from the Skelet #26 development.  Its reset is a single
`E`-sweep (no `J`/`E0`/`E1` split), so the argument is shorter than #26.
-/
section Skelet34Inline
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
end Skelet34Inline

section Skelet35Inline
open Turing
open TM.Table
open Deciders.Skelet.ShiftOverflowBins
open Deciders.Skelet.ShiftOverflow
open Deciders.Skelet.FixedBin

namespace Deciders.Skelet.Skelet35

open Deciders.Skelet.Skelet26 (f f1 f_as_f1 has0_f f_lt R_f prepare_K)

abbrev M : Machine 4 1 := mach["1RB1LC_0RC0RB_1LD0LA_1LE---_1LA0LA"]

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
lemma gE1 : M.get 4 1 = .next 0 .left 0 := by decide
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
      evsteps step_left_mk' gC1 _ _, step_right_mk' gA0 _ _, step_right_mk' gB0 _ _, step_left_mk' gC0 _ _, step_left_mk' gD0 _ _, step_left_head gE1 _ _
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
  evchain step_right_mk' gB1 _ _, step_right_mk' gB0 _ _, step_left_mk' gC1 _ _, step_right_mk' gA0 _ _, step_right_mk' gB0 _ _, step_left_mk' gC0 _ _, step_left_mk' gD0 _ _, step_left_mk' gE1 _ _, step_right_mk' gA0 _ _, step_right_mk' gB0 _ _, step_left_mk' gC1 _ _, step_right_mk' gA0 _ _, step_right_mk' gB0 _ _, step_left_mk' gC1 _ _, step_right_mk' gA0 _ _, step_right_mk' gB0 _ _
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
      evsteps step_left_mk' gC1 _ _, step_right_mk' gA0 _ _, step_right_mk' gB0 _ _, step_left_mk' gC1 _ _, step_right_mk' gA0 _ _, step_right_mk' gB0 _ _, step_left_blank gC0d _, step_left_mk' gD0 _ _, step_left_mk' gE1 _ _, step_left_head gA1 _ _
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
  evchain step_right_mk' gB1 _ _, step_right_mk' gB0 _ _, step_left_mk' gC1 _ _, step_right_mk' gA0 _ _, step_right_mk' gB0 _ _, step_left_mk' gC0 _ _, step_left_mk' gD0 _ _, step_left_mk' gE1 _ _, step_right_mk' gA0 _ _, step_right_mk' gB0 _ _, step_left_mk' gC1 _ _, step_right_mk' gA0 _ _, step_right_mk' gB0 _ _, step_left_mk' gC1 _ _, step_right_mk' gA0 _ _, step_right_mk' gB0 _ _
  refine (R_inc_all1 h _).trans ?_
  rw [headL_cons]
  evsteps step_left_mk' gC1 _ _, step_left_mk' gA1 _ _, step_left_mk' gC1 _ _, step_right_mk' gA0 _ _, step_right_mk' gB0 _ _, step_left_mk' gC1 _ _, step_right_mk' gA0 _ _, step_right_mk' gB0 _ _, step_left_mk' gC0 _ _, step_left_mk' gD0 _ _, step_left_mk' gE1 _ _, step_left_head gA1 _ _

/-- `start_reset` as a strict-progress step (Coq `start_reset'`). -/
lemma start_reset' (n : Num) {m : PosNum} (h : All1 m) :
    D n m -[M]->+ E (Num.succ n) 1 m.succ := by
  unfold D
  refine Trans.trans (L_inc n _) (?_ : _ -[M]->+ _)
  rw [L_as_K]
  refine Trans.trans (Machine.Progress.single (step_right_mk' gB1 _ _)) (?_ : _ -[M]->* _)
  evchain step_right_mk' gB0 _ _, step_left_mk' gC1 _ _, step_right_mk' gA0 _ _, step_right_mk' gB0 _ _, step_left_mk' gC0 _ _, step_left_mk' gD0 _ _, step_left_mk' gE1 _ _, step_right_mk' gA0 _ _, step_right_mk' gB0 _ _, step_left_mk' gC1 _ _, step_right_mk' gA0 _ _, step_right_mk' gB0 _ _, step_left_mk' gC1 _ _, step_right_mk' gA0 _ _, step_right_mk' gB0 _ _
  refine (R_inc_all1 h _).trans ?_
  rw [headL_cons]
  evsteps step_left_mk' gC1 _ _, step_left_mk' gA1 _ _, step_left_mk' gC1 _ _, step_right_mk' gA0 _ _, step_right_mk' gB0 _ _, step_left_mk' gC1 _ _, step_right_mk' gA0 _ _, step_right_mk' gB0 _ _, step_left_mk' gC0 _ _, step_left_mk' gD0 _ _, step_left_mk' gE1 _ _, step_left_head gA1 _ _

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
  evchain step_left_mk' gC0 _ _, step_left_mk' gD0 _ _, step_left_mk' gE1 _ _, step_right_mk' gA0 _ _, step_right_mk' gB0 _ _, step_left_mk' gC1 _ _, step_right_mk' gA0 _ _, step_right_mk' gB0 _ _, step_left_mk' gC1 _ _, step_right_mk' gA0 _ _, step_right_mk' gB0 _ _
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
      evchain step_right_mk' gB1 _ _, step_right_mk' gB0 _ _, step_left_mk' gC1 _ _, step_right_mk' gA0 _ _, step_right_mk' gB0 _ _, step_left_mk' gC0 _ _, step_left_mk' gD0 _ _, step_left_mk' gE1 _ _, step_right_mk' gA0 _ _, step_right_mk' gB0 _ _, step_left_mk' gC1 _ _, step_right_mk' gA0 _ _, step_right_mk' gB0 _ _, step_left_mk' gC1 _ _, step_right_mk' gA0 _ _, step_right_mk' gB0 _ _
      refine (R_inc_has0 hm _).trans ?_
      rw [headL_cons]
      evsteps step_left_mk' gA1 _ _, step_left_mk' gC1 _ _, step_left_head gA1 _ _
  | 1 =>
      refine (Lk_inc hn l _).trans ?_
      evchain step_right_mk' gB1 _ _, step_right_mk' gB0 _ _, step_left_mk' gC1 _ _, step_right_mk' gA0 _ _, step_right_mk' gB0 _ _, step_left_mk' gC1 _ _, step_right_mk' gA0 _ _, step_right_mk' gB0 _ _
      refine (R_inc_has0 hm _).trans ?_
      rw [headL_cons]
      evsteps step_left_mk' gA1 _ _, step_left_mk' gC1 _ _, step_right_mk' gA0 _ _, step_right_mk' gB0 _ _, step_left_mk' gC1 _ _, step_right_mk' gA0 _ _, step_right_mk' gB0 _ _, step_left_mk' gC0 _ _, step_left_mk' gD0 _ _, step_left_mk' gE1 _ _, step_left_head gA1 _ _

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
  refine stepN_evstep 552 ?_
  decide

/-- Skelet #35 (`sporadicMachine12`) does not halt (Coq `nonhalt`). -/
theorem nonHalting : ¬ M.halts init := by
  have cs : ClosedSet M (fun C => ∃ m : PosNum, C = D 0 m) init := by
    refine ⟨?_, ?_⟩
    · rintro ⟨C, m, rfl⟩
      obtain ⟨m', hstep⟩ := D_next m
      exact ⟨⟨D 0 m', m', rfl⟩, hstep⟩
    · exact ⟨⟨D 0 1441, 1441, rfl⟩, enters⟩
  exact cs.nonHalting

end Deciders.Skelet.Skelet35
end Skelet35Inline

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
section Skelet33Inline
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
end Skelet33Inline

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
  | zero => simp [zigzagAcc, tp]
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
theorem sporadicMachine5_nonHalting : ¬ sporadicMachine5.halts init :=
  Deciders.Skelet.Skelet1.nonHalting

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
      evsteps sB, sC
  | zO n, l => by
      have sB := step_left_mk' (l₀ := 𝟙) gB0 l (Zs n)
      have sC := step_left_head gC1 l (ListBlank.cons 𝟘 (Zs n))
      simp only [Zs, zI]
      evsteps sB, sC
  | zIO n, l => by
      have sB := step_right_mk' gB1 (ListBlank.cons 𝟙 l) (ListBlank.cons 𝟘 (Zs n))
      have sA := step_right_mk' gA0 (ListBlank.cons 𝟙 (ListBlank.cons 𝟙 l)) (Zs n)
      have ih := incr_right n (ListBlank.cons 𝟙 (ListBlank.cons 𝟙 l))
      have sD1 := step_left_mk' (l₀ := 𝟙) gD1 l (Zs (zI n))
      have sD2 := step_left_head gD1 l (ListBlank.cons 𝟘 (Zs (zI n)))
      simp only [headL_cons] at ih
      simp only [Zs, zI]
      evchain sB, sA
      refine ih.trans ?_
      evsteps sD1, sD2

/-- Left-counter increment sweep (Coq `incr_left`): the head, entering the left
accumulator in state `D`, applies the Zeckendorf carry `zI` to it and returns to
the right boundary in state `A`.  Forward `refine` steps; Lean infers the tapes. -/
lemma incr_left : ∀ (n : Dorf) (r : ListBlank (Symbol 1)),
    headL 3 (Ts n) (ListBlank.cons 𝟙 (ListBlank.cons 𝟙 r))
      -[M]->* (⟨0, Tape.mk' (Ts (zI n)) r⟩ : Config 4 1)
  | zend, r => by
      simp only [Ts, zI, headL_empty]
      evsteps step_left_edge gD0 _, step_right_mk' gC0 _ _, step_right_mk' gE1 _ _,
        step_right_mk' gB1 _ _, step_right_mk' gA1 _ _
  | zO n, r => by
      simp only [Ts, zI, headL_cons]
      evsteps step_left_mk' (l₀ := 𝟘) gD0 _ _, step_right_mk' gC0 _ _, step_right_mk' gE1 _ _,
        step_right_mk' gB1 _ _, step_right_mk' gA1 _ _
  | zIO n, r => by
      simp only [Ts, zI, headL_cons]
      evchain step_left_mk' (l₀ := 𝟙) gD0 _ _, step_left_mk' (l₀ := 𝟘) gC1 _ _,
        step_left_mk' (l₀ := 𝟙) gD0 _ _, step_left_head gC1 _ _
      refine (incr_left n _).trans ?_
      evsteps step_right_mk' gA1 _ _, step_right_mk' gA1 _ _, step_right_mk' gA1 _ _,
        step_right_mk' gA1 _ _

/-- One macro-step: the counter increments (Coq `incr_D`). -/
lemma incr_D (n : Dorf) : Dcfg n -[M]->+ Dcfg (incr n) := by
  cases n with
  | zend =>
      simp only [Dcfg, incr, zI, Ls, Zs, Ts, headL_empty, headL_cons, cons_zero_empty]
      refine Trans.trans (Machine.Progress.single (step_left_edge gD0 _))
        (?_ : _ -[M]->* _)
      evchain step_right_mk' gC0 _ _, step_right_mk' gE1 _ _, step_right_mk' gB1 _ _,
        step_right_blank gA0d _, step_left_blank (l₀ := 𝟙) gB0d _, step_left_mk' gC1 _ _,
        step_left_mk' gD1 _ _
      simp only [cons_zero_empty]
      exact Machine.EvStep.refl
  | zO n =>
      cases n with
      | zend =>
          simp only [Dcfg, incr, zI, Ls, Zs, Ts, headL_empty, headL_cons, cons_zero_empty]
          refine Trans.trans (Machine.Progress.single (step_left_edge gD0 _))
            (?_ : _ -[M]->* _)
          evchain step_right_mk' gC0 _ _, step_right_mk' gE1 _ _, step_right_mk' gB1 _ _,
            step_right_blank gA0d _, step_left_blank (l₀ := 𝟙) gB0d _, step_left_mk' gC1 _ _,
            step_left_mk' gD1 _ _
          simp only [cons_zero_empty]
          exact Machine.EvStep.refl
      | zO n =>
          simp only [Dcfg, incr, zI, Ls, Zs, Ts, headL_cons]
          refine Trans.trans (Machine.Progress.single (step_left_mk' gD0 _ _))
            (?_ : _ -[M]->* _)
          evchain step_right_mk' gC0 _ _, step_right_mk' gE1 _ _, step_right_mk' gB1 _ _,
            step_right_mk' gA0 _ _
          refine (incr_right n _).trans ?_
          simp only [headL_cons]
          evsteps step_left_mk' gD1 _ _
      | zIO n =>
          simp only [Dcfg, incr, zI, Ls, Zs, Ts, headL_cons]
          refine Trans.trans (Machine.Progress.single (step_left_mk' gD0 _ _))
            (?_ : _ -[M]->* _)
          evchain step_left_mk' gC1 _ _, step_left_mk' gD0 _ _, step_left_head gC1 _ _
          refine (incr_left n _).trans ?_
          evsteps step_right_mk' gA1 _ _, step_right_mk' gA1 _ _, step_right_mk' gA0 _ _,
            step_left_mk' gB0 _ _, step_left_mk' gC1 _ _
  | zIO n =>
      simp only [Dcfg, incr, Ls, Zs, headL_cons]
      refine Trans.trans (Machine.Progress.single (step_left_mk' gD0 _ _))
        (?_ : _ -[M]->* _)
      evchain step_left_head gC1 _ _
      refine (incr_left n _).trans ?_
      evchain step_right_mk' gA0 _ _
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
  evsteps s0, s1, s2

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
/-!
### Non-halting proof for `sporadicMachine7` (Skelet #15)

`1RB---_1RC1LB_1LD1RE_1LB0LD_1RA0RC` is Skelet #15, which the Coq proof
(`BusyCoq/Skelet15.v`) closes by observing that it is Skelet #26 "with a different
initial state": mirroring the machine (`Machine.symm`, Coq `flip`) and relabelling
its states by the 5-cycle `A↦E, B↦C, C↦A, D↦B, E↦D` turns it into Skelet #26
(`sporadicMachine9`).  A relabelling is a composition of state swaps
(`Machine.perm`), each of which is halting-equivalent (`Machine.perm.equiv`), and
mirroring is halting-equivalent on the blank tape (`Machine.symm.equiv`).  The
composition maps the start state `A` to `E`, so the blank-tape run of Skelet #15
is halting-equivalent to Skelet #26 started in state `E`, which does not halt by
`Deciders.Skelet.Skelet26.nonHalting_E`. -/
theorem sporadicMachine7_nonHalting : ¬ sporadicMachine7.halts init := by
  have e0 : (sporadicMachine7, (⟨(0 : Label 4), default⟩ : Config 4 1)) =H
            (sporadicMachine7.symm, (⟨(0 : Label 4), default⟩ : Config 4 1)) :=
    Machine.symm.equiv
  have e1 : (sporadicMachine7.symm, (⟨(0 : Label 4), default⟩ : Config 4 1)) =H
            (sporadicMachine7.symm.perm 1 2,
              (⟨Machine.swap (1 : Label 4) 2 0, default⟩ : Config 4 1)) :=
    Machine.perm.equiv
  have e2 : (sporadicMachine7.symm.perm 1 2,
              (⟨Machine.swap (1 : Label 4) 2 0, default⟩ : Config 4 1)) =H
            ((sporadicMachine7.symm.perm 1 2).perm 3 1,
              (⟨Machine.swap (3 : Label 4) 1 (Machine.swap 1 2 0), default⟩ : Config 4 1)) :=
    Machine.perm.equiv
  have e3 : ((sporadicMachine7.symm.perm 1 2).perm 3 1,
              (⟨Machine.swap (3 : Label 4) 1 (Machine.swap 1 2 0), default⟩ : Config 4 1)) =H
            (((sporadicMachine7.symm.perm 1 2).perm 3 1).perm 4 3,
              (⟨Machine.swap (4 : Label 4) 3 (Machine.swap 3 1 (Machine.swap 1 2 0)), default⟩
                : Config 4 1)) :=
    Machine.perm.equiv
  have e4 : (((sporadicMachine7.symm.perm 1 2).perm 3 1).perm 4 3,
              (⟨Machine.swap (4 : Label 4) 3 (Machine.swap 3 1 (Machine.swap 1 2 0)), default⟩
                : Config 4 1)) =H
            ((((sporadicMachine7.symm.perm 1 2).perm 3 1).perm 4 3).perm 0 4,
              (⟨Machine.swap (0 : Label 4) 4 (Machine.swap 4 3 (Machine.swap 3 1 (Machine.swap 1 2 0))),
                  default⟩ : Config 4 1)) :=
    Machine.perm.equiv
  have hfin : ((((sporadicMachine7.symm).perm 1 2).perm 3 1).perm 4 3).perm 0 4
      = Deciders.Skelet.Skelet26.M := by decide
  have hstate : Machine.swap (0 : Label 4) 4 (Machine.swap 4 3 (Machine.swap 3 1 (Machine.swap 1 2 0)))
      = (4 : Label 4) := by decide
  have E := ((((e0.trans e1).trans e2).trans e3).trans e4)
  rw [hfin, hstate] at E
  intro hhalt
  exact Deciders.Skelet.Skelet26.nonHalting_E (E.mp hhalt)

def sporadicMachine8 : Machine 4 1 := mach["1RB---_0LC1RE_0LD1LC_1RA1LB_0RB0RA"]
/-- Skelet #17 does not halt: the Gray-code counter proof, ported from Coq
`BB5_Skelet17.v` (see `Busybeaver/Deciders/Skelet/Skelet17.lean`). -/
theorem sporadicMachine8_nonHalting : ¬ sporadicMachine8.halts init :=
  Deciders.Skelet.Skelet17.nonHalting

def sporadicMachine9 : Machine 4 1 := mach["1RB1LD_1RC0RB_1LA1RC_1LE0LA_1LC---"]
theorem sporadicMachine9_nonHalting : ¬ sporadicMachine9.halts init :=
  Deciders.Skelet.Skelet26.nonHalting

def sporadicMachine10 : Machine 4 1 := mach["1RB1LC_0RC0RB_1LD0LA_1LE---_1LA1RE"]
theorem sporadicMachine10_nonHalting : ¬ sporadicMachine10.halts init :=
  Deciders.Skelet.Skelet33.nonHalting

def sporadicMachine11 : Machine 4 1 := mach["1RB1LC_0RC0RB_1LD0LA_1LE---_1LA1RA"]
theorem sporadicMachine11_nonHalting : ¬ sporadicMachine11.halts init :=
  Deciders.Skelet.Skelet34.nonHalting

def sporadicMachine12 : Machine 4 1 := mach["1RB1LC_0RC0RB_1LD0LA_1LE---_1LA0LA"]
theorem sporadicMachine12_nonHalting : ¬ sporadicMachine12.halts init :=
  Deciders.Skelet.Skelet35.nonHalting

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

/-!
## Normal-form (NF) table lookup

Coq's BB5 pipeline ends with `NF_decider table_based_decider`, which canonicalises
each machine with `TM_to_NF` before the table lookup.  This catches machines the
enumeration emits in a different orbit representative than the hardcoded key (mirror
images, or machines whose leading transition writes a blank).  We port `TM_to_NF`
(`List_Tape.v`) as an executable transform built from the existing `perm` (state
swap) and `symm` (tape reversal) symmetries.

The transform preserves non-halting, so a non-halting verdict for `toNF M` transfers
to `M`.  That preservation lemma is currently `sorry`: the executable behaviour is
correct, the proof is future work.  See [bb5-undecided-holdouts-diagnosis].
-/

/-- `St_suc`, saturating at the top state, matching Coq's `St_suc` (`St4 ↦ St4`). -/
def stSuc (cur : Label l) : Label l :=
  if h : cur.val + 1 ≤ l then ⟨cur.val + 1, by omega⟩ else cur

/-- `TM_to_write_nonzero_first`: relabel so the first transition writes a non-blank
symbol, by repeatedly swapping the start state with the target of a blank-writing
first move. -/
def writeNonzeroFirst : ℕ → Machine l s → Machine l s
  | 0, M => M
  | T + 1, M =>
    match M.get default default with
    | .next sym _ tgt =>
        if sym = default ∧ tgt ≠ default then
          writeNonzeroFirst T (M.perm default tgt)
        else M
    | .halt => M

/-- `TM_to_TNF_NF`: simulate from the blank tape and rename states into first-visit
order via state swaps. -/
def tnfRelabel : ℕ → Machine l s → Label l → Config l s → Machine l s
  | 0, M, _, _ => M
  | T + 1, M, cur, C =>
    match M.step C with
    | none => M
    | some C0 =>
        if cur.val < C0.state.val then
          let nxt := stSuc cur
          if nxt = C0.state then
            tnfRelabel T M nxt C0
          else
            tnfRelabel T (M.perm nxt C0.state) nxt ⟨nxt, C0.tape⟩
        else
          tnfRelabel T M cur C0

/-- `TM_to_rev_NF`: mirror the machine if its first move is to the left. -/
def revNF (M : Machine l s) : Machine l s :=
  match M.get default default with
  | .next _ .left _ => M.symm
  | _ => M

/-- Coq's `TM_to_NF`: write-nonzero-first, then TNF relabel (110 steps), then
reverse-if-left.  `TM_simplify` is the identity here and is omitted. -/
def toNF (M : Machine l s) : Machine l s :=
  revNF (tnfRelabel 110 (writeNonzeroFirst 100 M) default init)

/-- Consing the blank symbol onto the blank tape yields the blank tape. -/
lemma ListBlank_cons_default {Γ : Type} [Inhabited Γ] :
    Turing.ListBlank.cons (default : Γ) default = default := by
  have hnth : ∀ (i : ℕ), (default : Turing.ListBlank Γ).nth i = default := by
    intro i
    induction i with
    | zero => rfl
    | succ n ih => rw [Turing.ListBlank.nth_succ]; exact ih
  apply Turing.ListBlank.ext
  intro i
  cases i with
  | zero => rfl
  | succ n => rw [Turing.ListBlank.nth_succ, Turing.ListBlank.tail_cons, hnth, hnth]

/-- Writing the blank symbol on the blank tape and moving keeps the blank tape. -/
lemma write_default_move_default {Γ : Type} [Inhabited Γ] (d : Turing.Dir) :
    ((default : Turing.Tape Γ).write default).move d = default := by
  have hl : (default : Turing.Tape Γ).left = default := rfl
  have hr : (default : Turing.Tape Γ).right = default := rfl
  have hh : (default : Turing.ListBlank Γ).head = default := rfl
  have ht : (default : Turing.ListBlank Γ).tail = default := rfl
  cases d <;>
    simp only [Turing.Tape.write, Turing.Tape.move, hl, hr, hh, ht, ListBlank_cons_default] <;>
    rfl

/-
Swapping the start state with the target of a *blank-writing* first move
preserves halting from `init`.  This is the "triviality of a blank-writing first
step": from `init` the machine takes one step that writes a blank and moves,
landing in `⟨tgt, default⟩` (the tape is still blank), which is exactly the
`perm`-image of `init`.
-/
lemma writeNonzeroFirst_swap_equiv {M : Machine l s} {d : Turing.Dir} {tgt : Label l}
    (h : M.get default default = .next default d tgt) :
    ((M, init) : Machine l s × Config l s) =H (M.perm default tgt, init) := by
      refine' ( Machine.equi_halts.trans _ _ );
      exact ⟨ M, ⟨ tgt, default ⟩ ⟩;
      · -- Since the first move of M writes a blank and moves, landing in `⟨tgt, default⟩`, the single step from `init` to `⟨tgt, default⟩` is valid.
        have h_single_step : (init -[M]-> ⟨tgt, default⟩) :=
          Machine.step.some' h rfl (write_default_move_default d).symm
        exact Machine.equi_halts.mono ( Machine.Multistep.single h_single_step );
      · have hpe := Machine.perm.equiv (M := M) (q := default) (q' := tgt) (C := tgt) (T := default)
        simp only [Machine.swap.right] at hpe
        exact hpe

/-
`writeNonzeroFirst` preserves halting from `init`.
-/
lemma writeNonzeroFirst_equiv (T : ℕ) (M : Machine l s) :
    ((M, init) : Machine l s × Config l s) =H (writeNonzeroFirst T M, init) := by
      induction' T with T ih generalizing M <;> simp +decide [ writeNonzeroFirst ];
      · exact Machine.equi_halts.refl;
      · cases h : M.get 0 0 <;> simp +decide;
        · exact Machine.equi_halts.refl;
        · split_ifs with hcond
          · obtain ⟨hsym, -⟩ := hcond
            rw [hsym] at h
            exact (writeNonzeroFirst_swap_equiv h).trans (ih _)
          · exact Machine.equi_halts.refl

/-
`tnfRelabel` preserves halting from `init` (each renaming step is a state
swap of two non-start states, hence an `nz_equi`).
-/
lemma tnfRelabel_equiv (T : ℕ) (M : Machine l s) (cur : Label l) (C : Config l s) :
    ((M, init) : Machine l s × Config l s) =H (tnfRelabel T M cur C, init) := by
      induction' T with T ih generalizing M cur C <;> simp_all +decide [ tnfRelabel ];
      · exact Machine.equi_halts.refl;
      · cases h : M.step C <;> simp_all +decide [ Machine.equi_halts.refl ];
        split_ifs;
        · convert ih M _ _ using 1;
        · unfold stSuc at *;
          split_ifs at * <;> simp_all +decide [ Fin.ext_iff ];
          · convert Machine.equi_halts.trans ( Machine.perm.nz_equi _ _ ) ( ih _ _ _ ) using 1 <;>
            first
              | rfl
              | exact ne_of_gt ( Nat.succ_pos _ )
              | exact ne_of_gt ( lt_of_le_of_lt ( Nat.zero_le _ ) ‹_› )
          · grind;
        · exact ih _ _ _
/-
`revNF` preserves halting from `init` (identity or a tape reversal).
-/
lemma revNF_equiv (M : Machine l s) :
    ((M, init) : Machine l s × Config l s) =H (revNF M, init) := by
      unfold revNF; cases h : M.get default default <;> simp_all +decide ;
      · exact Machine.equi_halts.refl;
      · cases ‹Turing.Dir› <;> simp +decide [ * ];
        · exact Machine.symm.equiv
        · rfl

/-- `toNF` preserves halting from `init`. -/
lemma toNF_equiv (M : Machine l s) :
    ((M, init) : Machine l s × Config l s) =H (toNF M, init) := by
  unfold toNF
  refine Machine.equi_halts.trans (writeNonzeroFirst_equiv 100 M) ?_
  refine Machine.equi_halts.trans
    (tnfRelabel_equiv 110 (writeNonzeroFirst 100 M) default init) ?_
  exact revNF_equiv _

/-- `toNF` preserves non-halting. -/
theorem toNF_nonHalting {M : Machine l s} (h : ¬ (toNF M).halts init) : ¬ M.halts init :=
  fun hc => h ((toNF_equiv M).mp hc)

/-- Normal-form table decider: canonicalise with `toNF`, look the result up in the
table, and transfer a non-halting verdict back to the original machine.  Mirrors
Coq's `NF_decider table_based_decider` (only the non-halting direction propagates).

A `.halt` row is skipped before running its decider: `toNF` preserves halting in both
directions, so a normalised machine matching a halt row necessarily halts, and the
only verdict its `haltDecider` could produce is a `.halts_prf` we discard here.
Running it would spend tens of millions of steps in a halting search for nothing. -/
def nfTableDecider (table : Table) (M : Machine 4 1) : HaltM M Unit :=
  match findInTable? table (toNF M) with
  | some (.halt _) => .unknown ()
  | some d =>
      match d.run (toNF M) with
      | .loops_prf hnh => .loops_prf (toNF_nonHalting hnh)
      | _ => .unknown ()
  | none => .unknown ()

end Deciders.BB5Table
