import Busybeaver.Deciders.Sweep
import Busybeaver.Deciders.Skelet.TapeCalc
import Busybeaver.TM.Table.Parse
import Busybeaver.TM.Table.ClosedSet

/-!
# Skelet #1 (`1RB1RD_1LC0RC_1RA1LD_0RE0LB_---1RC`)

A Lean port of `Coq-BB5/BusyCoq/Skelet1.v` (sligocki's analysis, see
<https://www.sligocki.com/2023/03/13/skelet-1-infinite.html>).

This file develops the "block rules": macro-steps of the real machine `M` on
symbolic tape segments.  Everything is expressed with `Turing.Tape.mk' L R` and
the directed configurations `AR` (head faces right, state `A`) and `CL` (head
faces left, state `C`), mirroring BusyCoq's `l |> r` and `l <| r`.

The base rules are all discharged by the `crush` tactic, which simulates the
concrete machine step-by-step across the (finite) block window, uniformly in the
abstract tape tails.
-/

namespace Deciders.Skelet.Skelet1

open Turing TM.Table

abbrev M : Machine 4 1 := mach["1RB1RD_1LC0RC_1RA1LD_0RE0LB_---1RC"]

abbrev LB := ListBlank (Symbol 1)

/-! ## Transition table (A=0, B=1, C=2, D=3, E=4). -/
lemma gA0 : M.get 0 0 = .next 1 .right 1 := by decide
lemma gA1 : M.get 0 1 = .next 1 .right 3 := by decide
lemma gB0 : M.get 1 0 = .next 1 .left 2 := by decide
lemma gB1 : M.get 1 1 = .next 0 .right 2 := by decide
lemma gC0 : M.get 2 0 = .next 1 .right 0 := by decide
lemma gC1 : M.get 2 1 = .next 1 .left 3 := by decide
lemma gD0 : M.get 3 0 = .next 0 .right 4 := by decide
lemma gD1 : M.get 3 1 = .next 0 .left 1 := by decide
lemma gE1 : M.get 4 1 = .next 1 .right 2 := by decide
-- blank-edge (reading the blank symbol `default = 0`)
lemma gA0d : M.get 0 default = .next 1 .right 1 := by decide
lemma gB0d : M.get 1 default = .next 1 .left 2 := by decide
lemma gC0d : M.get 2 default = .next 1 .right 0 := by decide
lemma gD0d : M.get 3 default = .next 0 .right 4 := by decide

@[simp] lemma czero : ListBlank.cons (0 : Symbol 1) (∅ : LB) = (∅ : LB) :=
  ListBlank.cons_default_empty

/-! ## Directed configurations.

`AR l r` is BusyCoq's `l |> r` (head in state `A`, reading the top of `r`).
`CL l r` is BusyCoq's `l <| r = l <{{C}} 1 >> 0 >> r` (head in state `C`,
reading the top of `l`, with a `1,0` prefix on the right). -/
def AR (l r : LB) : Config 4 1 := ⟨0, Tape.mk' l r⟩
def CL (l r : LB) : Config 4 1 := headL 2 l (ListBlank.cons 1 (ListBlank.cons 0 r))

/-! ## Blocks (as lists of symbols, nearest-the-head first).

`run n = 1^n 0`.  Left blocks `<+` and right blocks `+>` are plain list
concatenation with the appropriate operand order (Coq `Helper.v`:
`l <+ xs = xs ++ l`, `xs +> r = xs ++ r`). -/
def run (n : ℕ) : List (Symbol 1) := List.replicate n 1 ++ [0]

def x  : List (Symbol 1) := run 2 ++ run 2
def Dl : List (Symbol 1) := run 1 ++ run 2
def Dr : List (Symbol 1) := run 2 ++ run 1
def C0 : List (Symbol 1) := run 2 ++ run 3 ++ run 2
def C1 : List (Symbol 1) := run 1 ++ run 0 ++ run 2
def C2 : List (Symbol 1) := run 2 ++ run 4
def C3 : List (Symbol 1) := run 1 ++ run 1
abbrev C : List (Symbol 1) := C3
def P  : List (Symbol 1) := run 2
def F0 : List (Symbol 1) := run 2 ++ run 3 ++ run 4
def F1 : List (Symbol 1) := run 1 ++ run 0 ++ run 4
def F2 : List (Symbol 1) := run 2 ++ run 6
def F3 : List (Symbol 1) := run 1 ++ run 3
def G0 : List (Symbol 1) := run 2 ++ run 3 ++ run 3 ++ run 2
def G1 : List (Symbol 1) := run 1 ++ run 0 ++ run 3 ++ run 2
def G2 : List (Symbol 1) := run 2 ++ run 5 ++ run 2

/-- Right/left blank edge (`const 0`). -/
abbrev RB : LB := (∅ : LB)

/-! ## Single-step peeler lemmas (used by the `crush` tactic). -/

private lemma evR {q q' : Label 4} {a b : Symbol 1} (h : M.get q a = .next b .right q')
    {L R : LB} {T : Config 4 1}
    (k : (⟨q', Tape.mk' (ListBlank.cons b L) R⟩ : Config 4 1) -[M]->* T) :
    (⟨q, Tape.mk' L (ListBlank.cons a R)⟩ : Config 4 1) -[M]->* T :=
  Machine.EvStep.step (step_right_mk' h L R) k

private lemma evL {q q' : Label 4} {a b l₀ : Symbol 1} (h : M.get q a = .next b .left q')
    {L R : LB} {T : Config 4 1}
    (k : (⟨q', Tape.mk' L (ListBlank.cons l₀ (ListBlank.cons b R))⟩ : Config 4 1) -[M]->* T) :
    (⟨q, Tape.mk' (ListBlank.cons l₀ L) (ListBlank.cons a R)⟩ : Config 4 1) -[M]->* T :=
  Machine.EvStep.step (step_left_mk' h L R) k

private lemma evLe {q q' : Label 4} {a b : Symbol 1} (h : M.get q a = .next b .left q')
    {L R : LB} {T : Config 4 1}
    (k : headL q' L (ListBlank.cons b R) -[M]->* T) :
    (⟨q, Tape.mk' L (ListBlank.cons a R)⟩ : Config 4 1) -[M]->* T :=
  Machine.EvStep.step (step_left_head h L R) k

private lemma evRb {q q' : Label 4} {b : Symbol 1} (h : M.get q default = .next b .right q')
    {L : LB} {T : Config 4 1}
    (k : (⟨q', Tape.mk' (ListBlank.cons b L) (∅ : LB)⟩ : Config 4 1) -[M]->* T) :
    (⟨q, Tape.mk' L (∅ : LB)⟩ : Config 4 1) -[M]->* T :=
  Machine.EvStep.step (step_right_blank h L) k

private lemma evLb {q q' : Label 4} {b l₀ : Symbol 1} (h : M.get q default = .next b .left q')
    {L : LB} {T : Config 4 1}
    (k : (⟨q', Tape.mk' L (ListBlank.cons l₀ (ListBlank.cons b (∅ : LB)))⟩ : Config 4 1) -[M]->* T) :
    (⟨q, Tape.mk' (ListBlank.cons l₀ L) (∅ : LB)⟩ : Config 4 1) -[M]->* T :=
  Machine.EvStep.step (step_left_blank h L) k

private lemma evEdge {q q' : Label 4} {a b : Symbol 1} (h : M.get q a = .next b .left q')
    {R : LB} {T : Config 4 1}
    (k : (⟨q', Tape.mk' (∅ : LB) (ListBlank.cons default (ListBlank.cons b R))⟩ : Config 4 1) -[M]->* T) :
    (⟨q, Tape.mk' (∅ : LB) (ListBlank.cons a R)⟩ : Config 4 1) -[M]->* T :=
  Machine.EvStep.step (step_left_edge h R) k

/-- Prove a base block rule: unfold blocks to concrete `cons` windows, then
repeatedly either stop at the target (`refl`) or peel one machine step. -/
local macro "crush" : tactic =>
  `(tactic| (simp only [AR, CL, x, Dl, Dr, C0, C1, C2, C3, P, F0, F1, F2, F3, G0, G1, G2,
               run, RB, List.replicate, List.cons_append, List.nil_append,
               ListBlank.append_cons, ListBlank.append_empty, czero, headL_cons];
             repeat (first
               | exact Machine.EvStep.refl
               | refine evR gA0 ?_ | refine evR gA1 ?_ | refine evR gB1 ?_ | refine evR gC0 ?_
               | refine evR gD0 ?_ | refine evR gE1 ?_
               | refine evL gB0 ?_ | refine evL gC1 ?_ | refine evL gD1 ?_
               | refine evRb gA0d ?_ | refine evRb gC0d ?_ | refine evRb gD0d ?_
               | refine evLb gB0d ?_
               | refine evEdge gB0 ?_ | refine evEdge gC1 ?_ | refine evEdge gD1 ?_
               | refine evLe gB0 ?_ | refine evLe gC1 ?_ | refine evLe gD1 ?_)))

/-! ## Base block rules. -/

set_option maxRecDepth 8000

lemma rule_x_left (l r : LB) : CL (x ++ l) r -[M]->* CL l (x ++ r) := by crush
lemma rule_D_left (l r : LB) : CL (Dl ++ l) r -[M]->* CL l (Dr ++ r) := by crush
lemma rule_C_left (l r : LB) : CL (C ++ l) r -[M]->* CL l (C ++ r) := by crush
lemma rule_x_right (l r : LB) : AR l (x ++ r) -[M]->* AR (x ++ l) r := by crush
lemma rule_D_right (l r : LB) : AR l (Dr ++ r) -[M]->* AR (Dl ++ l) r := by crush
lemma rule_xR (l : LB) : AR (x ++ l) RB -[M]->* CL l (C ++ x ++ P ++ RB) := by crush
lemma rule_DR (l : LB) : AR (Dl ++ l) RB -[M]->* CL l (x ++ RB) := by crush
lemma rule_L (r : LB) : CL RB (C ++ x ++ r) -[M]->* AR (Dl ++ C1 ++ RB) (P ++ r) := by crush
lemma rule_C30 (l r : LB) : AR (x ++ l) (C ++ r) -[M]->* AR (C0 ++ l) r := by crush
lemma rule_C01 (l r : LB) : CL (C0 ++ l) r -[M]->* AR (x ++ C1 ++ l) r := by crush
lemma rule_C12 (l r : LB) : CL (C1 ++ l) r -[M]->* AR (C2 ++ l) r := by crush
lemma rule_C23 (l r : LB) : CL (C2 ++ l) r -[M]->* AR (x ++ C ++ l) r := by crush
lemma rule_DC (l r : LB) : AR (Dl ++ l) (C ++ r) -[M]->* AR (x ++ P ++ l) r := by crush
lemma rule_C2_C (l r : LB) : AR (C2 ++ l) (C ++ r) -[M]->* AR (F0 ++ l) r := by crush
lemma rule_F0 (l r : LB) : CL (F0 ++ l) r -[M]->* AR (x ++ F1 ++ l) r := by crush
lemma rule_F1 (l r : LB) : CL (F1 ++ l) r -[M]->* AR (F2 ++ l) r := by crush
lemma rule_F2 (l r : LB) : CL (F2 ++ l) r -[M]->* AR (x ++ F3 ++ l) r := by crush
lemma rule_F3 (l r : LB) : CL (F3 ++ x ++ l) r -[M]->* AR (Dl ++ C1 ++ P ++ l) r := by crush
lemma rule_C03 (l r : LB) : AR (C0 ++ l) (C ++ r) -[M]->* AR (G0 ++ l) r := by crush
lemma rule_G0 (l r : LB) : CL (G0 ++ l) r -[M]->* AR (x ++ G1 ++ l) r := by crush
lemma rule_G1 (l r : LB) : CL (G1 ++ l) r -[M]->* AR (G2 ++ l) r := by crush
lemma rule_G2 (l r : LB) : CL (G2 ++ l) r -[M]->* AR (x ++ Dl ++ P ++ l) r := by crush
lemma rule_P_left (l r : LB) : CL (P ++ l) r -[M]->* CL l (P ++ r) := by crush
lemma rule_P_P (l r : LB) : AR l (P ++ P ++ r) -[M]->* AR (x ++ l) r := by crush
lemma rule_P_x (l r : LB) : AR l (P ++ x ++ r) -[M]->* AR (x ++ l) (P ++ r) := by crush
lemma rule_P_R (l : LB) : AR l (P ++ RB) -[M]->* CL l (P ++ RB) := by crush
lemma rule_P_Dx (l r : LB) :
    AR l (P ++ Dr ++ x ++ r) -[M]->* AR (Dl ++ C1 ++ l) (P ++ r) := by crush
lemma rule_P_Cx (l r : LB) :
    AR l (P ++ C ++ x ++ r) -[M]->* CL l (P ++ Dr ++ P ++ r) := by crush
lemma rule_P_DP (l r : LB) :
    AR l (P ++ Dr ++ P ++ r) -[M]->* AR (Dl ++ C1 ++ l) r := by crush
lemma rule_P_DDx (l r : LB) :
    AR l (P ++ Dr ++ Dr ++ x ++ r) -[M]->* AR (Dl ++ C1 ++ C2 ++ l) r := by crush
lemma rule_P_DCx (l r : LB) :
    AR l (P ++ Dr ++ C ++ x ++ r) -[M]->* AR (Dl ++ G1 ++ l) (P ++ r) := by crush

/-! ## Block powers and composite rules. -/

/-- `lpow b n` = the block `b` repeated `n` times. -/
def lpow (b : List (Symbol 1)) : ℕ → List (Symbol 1)
  | 0 => []
  | n + 1 => b ++ lpow b n

@[simp] lemma lpow_zero (b : List (Symbol 1)) : lpow b 0 = [] := rfl
lemma lpow_succ (b : List (Symbol 1)) (n : ℕ) : lpow b (n + 1) = b ++ lpow b n := rfl
lemma lpow_succ' (b : List (Symbol 1)) (n : ℕ) : lpow b (n + 1) = lpow b n ++ b := by
  induction n with
  | zero => simp [lpow_succ, lpow_zero]
  | succ n ih =>
      calc lpow b (n + 2) = b ++ lpow b (n + 1) := lpow_succ b (n + 1)
        _ = b ++ (lpow b n ++ b) := by rw [ih]
        _ = (b ++ lpow b n) ++ b := by rw [List.append_assoc]
        _ = lpow b (n + 1) ++ b := by rw [lpow_succ]

/-- The composite left/right blocks used in the universe cycle.  Left blocks are
stored reversed (`<+`), right blocks in order (`+>`). -/
def Fl : List (Symbol 1) :=
  lpow x 10344 ++ Dl ++ lpow x 7640 ++ C2
def Gl : List (Symbol 1) :=
  Dl ++ lpow x 1538 ++ Dl ++ lpow x 3076 ++ Dl ++ lpow x 72142 ++ Dl ++ lpow x 30826 ++ Dl ++ lpow x 300
def Gr : List (Symbol 1) :=
  lpow x 300 ++ Dr ++ lpow x 30826 ++ Dr ++ lpow x 72142 ++ Dr ++ lpow x 3076 ++ Dr ++ lpow x 1538 ++ Dr
def Hl : List (Symbol 1) :=
  lpow x 1537 ++ Dl ++ C1 ++ lpow x 3075 ++ Dl ++ C1 ++ lpow x 72141 ++ Dl ++ C1 ++
    lpow x 30825 ++ Dl ++ C1 ++ lpow x 299 ++ Dl ++ C1

lemma rule_xn_left (n : ℕ) (l r : LB) :
    CL (lpow x n ++ l) r -[M]->* CL l (lpow x n ++ r) := by
      -- Apply `lpow_succ'` to rewrite `lpow x (n+1)` in terms of `lpow x n`.
      have h_lpow_succ : ∀ (n : ℕ), lpow x (n + 1) = lpow x n ++ x := by
        exact fun n => lpow_succ' x n;
      induction n generalizing l r <;> simp_all +decide;
      · exact Machine.EvStep.refl;
      · rename_i n ih; convert ih _ _ |> Machine.EvStep.trans <| rule_x_left _ _ using 1;
        congr! 1;
        rotate_right;
        exact l;
        · exact ListBlank.append_assoc';
        · simp +decide [← h_lpow_succ];
          rw [lpow_succ]
          simpa [ListBlank.append_assoc'] using
            (rule_x_left _ _).trans (ih _ _)

lemma lpow_x_comm (n : ℕ) : lpow x n ++ x = x ++ lpow x n := by
  rw [← lpow_succ']
  rw [lpow_succ]

lemma lpow_comm (n : ℕ) (l : LB) :
    x ++ (lpow x n ++ l) = lpow x n ++ (x ++ l) := by
  induction n with
  | zero =>
      simp [lpow]
  | succ n ih =>
      simp [lpow_succ, ListBlank.append_assoc', ih]

lemma rule_xn_right (n : ℕ) (l r : LB) :
    AR l (lpow x n ++ r) -[M]->* AR (lpow x n ++ l) r := by
  induction n generalizing l r with
  | zero =>
      simp [lpow]
      exact Machine.EvStep.refl
    | succ n ih =>
        rw [lpow_succ]
        refine Machine.EvStep.trans (rule_x_right l (lpow x n ++ r)) ?_
        convert ih (x ++ l) r using 1
        congr 1
        exact lpow_comm n l

lemma rule_P_xn (n : ℕ) (l r : LB) :
    AR l (P ++ lpow x n ++ r) -[M]->* AR (lpow x n ++ l) (P ++ r) := by
  induction n generalizing l r with
    | zero =>
        simp [lpow]
        exact Machine.EvStep.refl
    | succ n ih =>
        rw [lpow_succ]
        have h1 := rule_P_x l (lpow x n ++ r)
        have h2 := ih (x ++ l) r
        simp only [ListBlank.append_assoc'] at h1 h2 ⊢
        refine Machine.EvStep.trans h1 ?_
        convert h2 using 1
        congr 1
        exact lpow_comm n l

/-- One `x^n Dr` segment swept right (right-associated form). -/
lemma rule_xD_right (n : ℕ) (l r : LB) :
    AR l (lpow x n ++ (Dr ++ r)) -[M]->* AR (Dl ++ (lpow x n ++ l)) r :=
  (rule_xn_right n l (Dr ++ r)).trans (rule_D_right (lpow x n ++ l) r)

/-- One `Dl x^n` segment swept left (right-associated form). -/
lemma rule_Dx_left (n : ℕ) (l r : LB) :
    CL (Dl ++ (lpow x n ++ l)) r -[M]->* CL l (lpow x n ++ (Dr ++ r)) :=
  (rule_D_left (lpow x n ++ l) r).trans (rule_xn_left n l (Dr ++ r))

lemma rule_G_right (l r : LB) : AR l (Gr ++ r) -[M]->* AR (Gl ++ l) r := by
  simp only [Gr, Gl, ListBlank.append_assoc']
  refine (rule_xD_right 300 _ _).trans ?_
  refine (rule_xD_right 30826 _ _).trans ?_
  refine (rule_xD_right 72142 _ _).trans ?_
  refine (rule_xD_right 3076 _ _).trans ?_
  exact rule_xD_right 1538 _ _

lemma rule_G_left (l r : LB) : CL (Gl ++ l) r -[M]->* CL l (Gr ++ r) := by
  simp only [Gr, Gl, ListBlank.append_assoc']
  refine (rule_Dx_left 1538 _ _).trans ?_
  refine (rule_Dx_left 3076 _ _).trans ?_
  refine (rule_Dx_left 72142 _ _).trans ?_
  refine (rule_Dx_left 30826 _ _).trans ?_
  exact rule_Dx_left 300 _ _

lemma rule_Gn_right (n : ℕ) (l r : LB) :
    AR l (lpow Gr n ++ r) -[M]->* AR (lpow Gl n ++ l) r := by
      revert l r;
      induction n <;> simp_all +decide [ lpow_succ' ];
      · -- The identity relation is reflexive.
        intros l r
        apply Machine.EvStep.refl;
      · rename_i n ih; intro l r; rw [ show lpow Gr n ++ Gr ++ r = Gr ++ ( lpow Gr n ++ r ) by
                                        rw [ ← ListBlank.append_assoc' ];
                                        rw [ ← lpow_succ' ];
                                        rw [ lpow_succ ] ] ;
        convert rule_G_right l ( lpow Gr n ++ r ) |> Machine.EvStep.trans <| ih _ _ using 1;
        exact congr_arg₂ _ ( by exact ListBlank.append_assoc' ) rfl

lemma rule_Gn_left (n : ℕ) (l r : LB) :
    CL (lpow Gl n ++ l) r -[M]->* CL l (lpow Gr n ++ r) := by
      revert l r;
      induction n <;> simp_all +decide [ lpow_succ', ListBlank.append_assoc' ];
      · exact fun _ _ => Machine.EvStep.refl;
      · rename_i n ih; intro l r; exact (by
        have h_step : CL (Gl ++ (lpow Gl n ++ l)) r -[M]->* CL (lpow Gl n ++ l) (Gr ++ r) := by
          convert rule_G_left ( lpow Gl n ++ l ) r using 1;
        have h_step2 : CL (Gl ++ (lpow Gl n ++ l)) r -[M]->* CL l (lpow Gr n ++ (Gr ++ r)) := by
          exact h_step.trans ( ih _ _ );
        have h_step3 : CL (lpow Gl n ++ (Gl ++ l)) r = CL (Gl ++ (lpow Gl n ++ l)) r := by
          rw [ ← ListBlank.append_assoc' ];
          rw [ ← lpow_succ' ];
          rw [ lpow_succ ];
          rw [ ListBlank.append_assoc' ];
        exact h_step3.symm ▸ h_step2);

/-- One `Dr x^(n+1)` segment consumed after a leading `P` (mirrors the Coq
`rule_P_Dx`/`rule_P_xn` pair). -/
lemma rule_P_DGseg (n : ℕ) (l r : LB) :
    AR l (P ++ (Dr ++ (lpow x (n + 1) ++ r))) -[M]->* AR (lpow x n ++ (Dl ++ (C1 ++ l))) (P ++ r) := by
  have h1 := rule_P_Dx l (lpow x n ++ r)
  have h2 := rule_P_xn n (Dl ++ (C1 ++ l)) r
  simp only [lpow_succ, ListBlank.append_assoc'] at h1 h2 ⊢
  exact h1.trans h2

lemma rule_P_DG (l r : LB) :
    AR l (P ++ Dr ++ Gr ++ r) -[M]->* AR (Hl ++ l) (P ++ Dr ++ r) := by
      simp +decide [ Gr, Hl, ListBlank.append_assoc', List.append_assoc ];
      refine' ( rule_P_DGseg 299 _ _ ).trans _;
      refine' ( rule_P_DGseg 30825 _ _ ).trans _;
      refine' ( rule_P_DGseg 72141 _ _ ).trans _;
      refine' ( rule_P_DGseg 3075 _ _ ).trans _;
      convert rule_P_DGseg 1537 _ _ using 1

lemma rule_P_DGn (n : ℕ) (l r : LB) :
    AR l (P ++ Dr ++ lpow Gr n ++ r) -[M]->* AR (lpow Hl n ++ l) (P ++ Dr ++ r) := by
      revert l;
      induction n <;> simp_all +decide [lpow_succ];
      · exact fun l => Machine.EvStep.refl;
      · rename_i n ih;
        intro l
        have h_step : AR l (P ++ Dr ++ (Gr ++ lpow Gr n) ++ r) -[M]->* AR (Hl ++ l) (P ++ Dr ++ (lpow Gr n) ++ r) := by
          have := rule_P_DG l (lpow Gr n ++ r);
          simp_all +decide [ List.append_assoc, ListBlank.append_assoc' ]
        generalize_proofs at *; (
        exact h_step.trans ( ih _ ) |> fun h => h.trans ( by
          rw [ ← ListBlank.append_assoc' ];
          rw [ ← lpow_succ' ];
          exact Machine.EvStep.refl ))

end Deciders.Skelet.Skelet1
