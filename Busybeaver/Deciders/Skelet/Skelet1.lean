import Busybeaver.Deciders.Skelet.TapeCalc
import Busybeaver.TM.Table.Parse
import Busybeaver.TM.Table.Reachability
import Busybeaver.TM.Table.ClosedSet

/-!
# Skelet #1 (BB(5) sporadic holdout `1RB1RD_1LC0RC_1RA1LD_0RE0LB_---1RC`)

Port of `Coq-BB5/BusyCoq/Skelet1.v` (sligocki's analysis,
<https://www.sligocki.com/2023/03/13/skelet-1-infinite.html>).  Skelet #1 is the
single hardest BB(5) non-halting holdout: a Collatz-like "Cryptid" that only
becomes eventually periodic (a *translated cycler*) after more than
`5.41 × 10⁵¹` steps, with period `8_468_569_863`.

The Coq proof is a *verified symbolic simulator*:

* a directed **shift-rule** layer (`rule_*`) describing how the head moves blocks
  `x, Dl/Dr, C0..C3, P, F0..F3, G0..G2, ...` around;
* a **symbolic tape** (`lsym`/`rsym`) with an executable `simple_step` and a
  soundness lemma against the real machine;
* a multi-level **`stride`** acceleration for the repeated-`x` runs;
* a `fullstep` symbolic simulator run `88_000_000` times from the post-`init`
  configuration, whose eventual translated cycle certifies non-halting.

This is a large multi-part port; it is being built up incrementally.  Blocks are
concrete `List (Symbol 1)`; a block `b` spliced onto a side is `b ++ side` with
`b`'s *first* element nearest the head (mirroring BusyCoq `Str_app`).
-/

namespace Deciders.Skelet.Skelet1

open Turing TM.Table

-- Each `sim1` step feeds the whole transition table to `simp only`; only the
-- enabled transition fires, so the rest are reported unused.  That is expected.
set_option linter.unusedSimpArgs false

/-- Skelet #1's transition table.  States `A=0, B=1, C=2, D=3, E=4`. -/
abbrev M : Machine 4 1 := mach["1RB1RD_1LC0RC_1RA1LD_0RE0LB_---1RC"]

local notation "𝟙" => (1 : Symbol 1)
local notation "𝟘" => (0 : Symbol 1)

-- Transitions (A=0, B=1, C=2, D=3, E=4)
lemma gA0 : M.get 0 0 = .next 1 .right 1 := by decide
lemma gA1 : M.get 0 1 = .next 1 .right 3 := by decide
lemma gB0 : M.get 1 0 = .next 1 .left 2 := by decide
lemma gB1 : M.get 1 1 = .next 0 .right 2 := by decide
lemma gC0 : M.get 2 0 = .next 1 .right 0 := by decide
lemma gC1 : M.get 2 1 = .next 1 .left 3 := by decide
lemma gD0 : M.get 3 0 = .next 0 .right 4 := by decide
lemma gD1 : M.get 3 1 = .next 0 .left 1 := by decide
lemma gE1 : M.get 4 1 = .next 1 .right 2 := by decide
-- blank-edge variants (head reads the `default` cell at a blank end)
lemma gA0d : M.get 0 default = .next 1 .right 1 := by decide
lemma gB0d : M.get 1 default = .next 1 .left 2 := by decide
lemma gC0d : M.get 2 default = .next 1 .right 0 := by decide
lemma gD0d : M.get 3 default = .next 0 .right 4 := by decide

@[simp] lemma cons_zero_empty : ListBlank.cons (0 : Symbol 1) ∅ = ∅ := ListBlank.cons_default_empty

/-! ## Blocks

Each block is the concrete bit-list that BusyCoq splices onto a tape side.
`run n = 1ⁿ ++ [0]` (Coq `run`, via `l <: s = s :: l`).  Left-side blocks
(`Dl`, `C0`…) and right-side blocks (`Dr`) differ in orientation because BusyCoq
builds them with `<+` (`l <+ xs = xs ++ l`) resp. `+>` (`xs +> r = xs ++ r`). -/

/-- `run n = 1ⁿ ++ [0]`. -/
def run (n : ℕ) : List (Symbol 1) := List.replicate n 𝟙 ++ [𝟘]

/-- `x = run 2 ++ run 2 = [1,1,0,1,1,0]`. -/
def xB : List (Symbol 1) := run 2 ++ run 2
/-- `Dl = run 1 ++ run 2` (left orientation). -/
def DlB : List (Symbol 1) := run 1 ++ run 2
/-- `Dr = run 2 ++ run 1` (right orientation). -/
def DrB : List (Symbol 1) := run 2 ++ run 1
/-- `C0 = run 2 ++ run 3 ++ run 2`. -/
def C0B : List (Symbol 1) := run 2 ++ run 3 ++ run 2
/-- `C1 = run 1 ++ run 0 ++ run 2`. -/
def C1B : List (Symbol 1) := run 1 ++ run 0 ++ run 2
/-- `C2 = run 2 ++ run 4`. -/
def C2B : List (Symbol 1) := run 2 ++ run 4
/-- `C3 = C = run 1 ++ run 1`. -/
def C3B : List (Symbol 1) := run 1 ++ run 1
/-- `P = run 2`. -/
def PB : List (Symbol 1) := run 2
/-- `F0 = run 2 ++ run 3 ++ run 4`. -/
def F0B : List (Symbol 1) := run 2 ++ run 3 ++ run 4
/-- `F1 = run 1 ++ run 0 ++ run 4`. -/
def F1B : List (Symbol 1) := run 1 ++ run 0 ++ run 4
/-- `F2 = run 2 ++ run 6`. -/
def F2B : List (Symbol 1) := run 2 ++ run 6
/-- `F3 = run 1 ++ run 3`. -/
def F3B : List (Symbol 1) := run 1 ++ run 3
/-- `G0 = run 2 ++ run 3 ++ run 3 ++ run 2`. -/
def G0B : List (Symbol 1) := run 2 ++ run 3 ++ run 3 ++ run 2
/-- `G1 = run 1 ++ run 0 ++ run 3 ++ run 2`. -/
def G1B : List (Symbol 1) := run 1 ++ run 0 ++ run 3 ++ run 2
/-- `G2 = run 2 ++ run 5 ++ run 2`. -/
def G2B : List (Symbol 1) := run 2 ++ run 5 ++ run 2

/-! ## Directed configurations

BusyCoq's two directed forms specialised to Skelet #1:

* `l |> r` (Coq `l {{A}}> r`): head in state `A` reading the top of the right
  side `r`.  In `mk'` form this is `⟨A, Tape.mk' l r⟩`.
* `l <| r` (Coq `l <{{C}} 1 >> 0 >> r`): head in state `C` reading the top of the
  left side `l`, with the fixed `1,0` phase marker on the right.  This is
  `headL C l (1 :: 0 :: r)`. -/

/-- `l |> r`: state-`A` head reading the top of the right side. -/
abbrev dR (l r : ListBlank (Symbol 1)) : Config 4 1 := ⟨0, Tape.mk' l r⟩

/-- `l <| r`: state-`C` head reading the top of the left side, `1,0` phase on the right. -/
abbrev dL (l r : ListBlank (Symbol 1)) : Config 4 1 :=
  headL 2 l (ListBlank.cons 𝟙 (ListBlank.cons 𝟘 r))

/-! ## `sim`: brute-force block-crossing tactic

Each `rule_*` lemma is a fixed finite computation: the head crosses a concrete
block (with abstract tails `l`, `r` untouched except at the boundary).  `sim`
repeatedly applies the unique enabled machine step — one alternative per
transition, each using its pre-proven `g**` lemma so the direction and target are
fixed and `first` backtracks cleanly on the non-matching ones.  The `*_mk'`
variants (concrete `cons` on both sides) are preferred; the `step_left_head`
variants fire only for the terminal left-step into the abstract left side,
landing in `headL`/`dL` form.  `refl` closes when the target is reached. -/
/-- One forward machine step, computed by `simp`.  `Machine.step` is reduced on
the current (concrete-headed) `mk'` configuration: exactly the enabled transition
`g**` fires and the tape `write`/`move` are evaluated, yielding `some next`; `rfl`
pins the `EvStep` middle to `next`.  Costs nothing on the non-matching
transitions (`simp` just doesn't rewrite), avoiding the quotient-`whnf` blowup of
trying wrong step lemmas by unification. -/
local macro "sim1" : tactic => `(tactic|
  refine Machine.EvStep.step (by
    simp only [Machine.step, Tape.mk'_head, ListBlank.head_cons, ListBlank.tail_cons,
      ListBlank.head_empty, ListBlank.tail_empty, cons_zero_empty,
      gA0, gA1, gB0, gB1, gC0, gC1, gD0, gD1, gE1, gA0d, gB0d, gC0d, gD0d,
      Tape.write_mk', Tape.move_left_mk', Tape.move_right_mk']; rfl) ?_)

/-- Step forward until the reached configuration matches the target.  `refl` is
tried before each step so the search halts at *waypoint* targets whose head sits
on a concrete block (`… |> P *> r`), not just at targets whose head reads the
abstract tail.  The `refl` check compares two concrete `mk'` configurations, so a
mismatch fails fast on the first differing cell (no quotient blowup). -/
local macro "sim" : tactic => `(tactic|
  repeat (first | exact Machine.EvStep.refl | sim1))

/-- Unfold blocks and directed configs into explicit `cons` chains for `sim`. -/
local macro "unfoldBlocks" : tactic => `(tactic|
  simp only [dL, dR, xB, DlB, DrB, C0B, C1B, C2B, C3B, PB,
    F0B, F1B, F2B, F3B, G0B, G1B, G2B, run,
    List.replicate, List.append_assoc, List.cons_append, List.nil_append,
    ListBlank.append_cons, ListBlank.append_empty, cons_zero_empty, headL_cons, headL_empty])

/-! ## Shift rules

The local step rules (Coq `rule_*`), each a bounded block-crossing. -/

/-- Coq `rule_x_left`: `l <* x <| r -->* l <| x *> r`. -/
lemma rule_x_left (l r : ListBlank (Symbol 1)) :
    dL (xB ++ l) r -[M]->* dL l (xB ++ r) := by
  unfoldBlocks; sim

/-- Coq `rule_D_left`: `l <* Dl <| r -->* l <| Dr *> r`. -/
lemma rule_D_left (l r : ListBlank (Symbol 1)) :
    dL (DlB ++ l) r -[M]->* dL l (DrB ++ r) := by
  unfoldBlocks; sim

/-- Coq `rule_C_left`: `l <* C <| r -->* l <| C *> r`. -/
lemma rule_C_left (l r : ListBlank (Symbol 1)) :
    dL (C3B ++ l) r -[M]->* dL l (C3B ++ r) := by
  unfoldBlocks; sim

/-- Coq `rule_x_right`: `l |> x *> r -->* l <* x |> r`. -/
lemma rule_x_right (l r : ListBlank (Symbol 1)) :
    dR l (xB ++ r) -[M]->* dR (xB ++ l) r := by
  unfoldBlocks; sim

/-- Coq `rule_D_right`: `l |> Dr *> r -->* l <* Dl |> r`. -/
lemma rule_D_right (l r : ListBlank (Symbol 1)) :
    dR l (DrB ++ r) -[M]->* dR (DlB ++ l) r := by
  unfoldBlocks; sim

/-- Coq `rule_C30`: `l <* x |> C *> r -->* l <* C0 |> r`. -/
lemma rule_C30 (l r : ListBlank (Symbol 1)) :
    dR (xB ++ l) (C3B ++ r) -[M]->* dR (C0B ++ l) r := by
  unfoldBlocks; sim

/-- Coq `rule_C01`: `l <* C0 <| r -->* l <* C1 <* x |> r`. -/
lemma rule_C01 (l r : ListBlank (Symbol 1)) :
    dL (C0B ++ l) r -[M]->* dR (xB ++ C1B ++ l) r := by
  unfoldBlocks; sim

/-- Coq `rule_C12`: `l <* C1 <| r -->* l <* C2 |> r`. -/
lemma rule_C12 (l r : ListBlank (Symbol 1)) :
    dL (C1B ++ l) r -[M]->* dR (C2B ++ l) r := by
  unfoldBlocks; sim

/-- Coq `rule_C23`: `l <* C2 <| r -->* l <* C <* x |> r`. -/
lemma rule_C23 (l r : ListBlank (Symbol 1)) :
    dL (C2B ++ l) r -[M]->* dR (xB ++ C3B ++ l) r := by
  unfoldBlocks; sim

/-- Coq `rule_DC`: `l <* Dl |> C *> r -->* l <* P <* x |> r`. -/
lemma rule_DC (l r : ListBlank (Symbol 1)) :
    dR (DlB ++ l) (C3B ++ r) -[M]->* dR (xB ++ PB ++ l) r := by
  unfoldBlocks; sim

/-- Coq `rule_C2_C`: `l <* C2 |> C *> r -->* l <* F0 |> r`. -/
lemma rule_C2_C (l r : ListBlank (Symbol 1)) :
    dR (C2B ++ l) (C3B ++ r) -[M]->* dR (F0B ++ l) r := by
  unfoldBlocks; sim

/-- Coq `rule_F0`: `l <* F0 <| r -->* l <* F1 <* x |> r`. -/
lemma rule_F0 (l r : ListBlank (Symbol 1)) :
    dL (F0B ++ l) r -[M]->* dR (xB ++ F1B ++ l) r := by
  unfoldBlocks; sim

/-- Coq `rule_F1`: `l <* F1 <| r -->* l <* F2 |> r`. -/
lemma rule_F1 (l r : ListBlank (Symbol 1)) :
    dL (F1B ++ l) r -[M]->* dR (F2B ++ l) r := by
  unfoldBlocks; sim

/-- Coq `rule_F2`: `l <* F2 <| r -->* l <* F3 <* x |> r`. -/
lemma rule_F2 (l r : ListBlank (Symbol 1)) :
    dL (F2B ++ l) r -[M]->* dR (xB ++ F3B ++ l) r := by
  unfoldBlocks; sim

/-- Coq `rule_F3`: `l <* x <* F3 <| r -->* l <* P <* C1 <* Dl |> r`. -/
lemma rule_F3 (l r : ListBlank (Symbol 1)) :
    dL (F3B ++ xB ++ l) r -[M]->* dR (DlB ++ C1B ++ PB ++ l) r := by
  unfoldBlocks; sim

/-- Coq `rule_C03`: `l <* C0 |> C *> r -->* l <* G0 |> r`. -/
lemma rule_C03 (l r : ListBlank (Symbol 1)) :
    dR (C0B ++ l) (C3B ++ r) -[M]->* dR (G0B ++ l) r := by
  unfoldBlocks; sim

/-- Coq `rule_G0`: `l <* G0 <| r -->* l <* G1 <* x |> r`. -/
lemma rule_G0 (l r : ListBlank (Symbol 1)) :
    dL (G0B ++ l) r -[M]->* dR (xB ++ G1B ++ l) r := by
  unfoldBlocks; sim

/-- Coq `rule_G1`: `l <* G1 <| r -->* l <* G2 |> r`. -/
lemma rule_G1 (l r : ListBlank (Symbol 1)) :
    dL (G1B ++ l) r -[M]->* dR (G2B ++ l) r := by
  unfoldBlocks; sim

/-- Coq `rule_G2`: `l <* G2 <| r -->* l <* P <* Dl <* x |> r`. -/
lemma rule_G2 (l r : ListBlank (Symbol 1)) :
    dL (G2B ++ l) r -[M]->* dR (xB ++ DlB ++ PB ++ l) r := by
  unfoldBlocks; sim

/-- Coq `rule_P_left`: `l <* P <| r -->* l <| P *> r`. -/
lemma rule_P_left (l r : ListBlank (Symbol 1)) :
    dL (PB ++ l) r -[M]->* dL l (PB ++ r) := by
  unfoldBlocks; sim

/-- Coq `rule_P_P`: `l |> P *> P *> r -->* l <* x |> r`. -/
lemma rule_P_P (l r : ListBlank (Symbol 1)) :
    dR l (PB ++ PB ++ r) -[M]->* dR (xB ++ l) r := by
  unfoldBlocks; sim

/-- Coq `rule_P_x`: `l |> P *> x *> r -->* l <* x |> P *> r`. -/
lemma rule_P_x (l r : ListBlank (Symbol 1)) :
    dR l (PB ++ xB ++ r) -[M]->* dR (xB ++ l) (PB ++ r) := by
  unfoldBlocks; sim

/-- Coq `rule_P_Dx`: `l |> P *> Dr *> x *> r -->* l <* C1 <* Dl |> P *> r`. -/
lemma rule_P_Dx (l r : ListBlank (Symbol 1)) :
    dR l (PB ++ DrB ++ xB ++ r) -[M]->* dR (DlB ++ C1B ++ l) (PB ++ r) := by
  unfoldBlocks; sim

/-- Coq `rule_P_Cx`: `l |> P *> C *> x *> r -->* l <| P *> Dr *> P *> r`. -/
lemma rule_P_Cx (l r : ListBlank (Symbol 1)) :
    dR l (PB ++ C3B ++ xB ++ r) -[M]->* dL l (PB ++ DrB ++ PB ++ r) := by
  unfoldBlocks; sim

/-- Coq `rule_P_DP`: `l |> P *> Dr *> P *> r -->* l <* C1 <* Dl |> r`. -/
lemma rule_P_DP (l r : ListBlank (Symbol 1)) :
    dR l (PB ++ DrB ++ PB ++ r) -[M]->* dR (DlB ++ C1B ++ l) r := by
  unfoldBlocks; sim

/-- Coq `rule_P_DDx`: `l |> P *> Dr *> Dr *> x *> r -->* l <* C2 <* C1 <* Dl |> r`. -/
lemma rule_P_DDx (l r : ListBlank (Symbol 1)) :
    dR l (PB ++ DrB ++ DrB ++ xB ++ r) -[M]->* dR (DlB ++ C1B ++ C2B ++ l) r := by
  unfoldBlocks; sim

/-- Coq `rule_P_DCx`: `l |> P *> Dr *> C *> x *> r -->* l <* G1 <* Dl |> P *> r`. -/
lemma rule_P_DCx (l r : ListBlank (Symbol 1)) :
    dR l (PB ++ DrB ++ C3B ++ xB ++ r) -[M]->* dR (DlB ++ G1B ++ l) (PB ++ r) := by
  unfoldBlocks; sim

/-! ## Boundary rules

At the blank tape ends `R = L = const 0 = ∅`.  A trailing `0` of a block merges
with the blank (`cons 0 ∅ = ∅`), so `sim1` reads the blank via the `g**d`
transition variants. -/

/-- Coq `rule_xR`: `l <* x |> R -->* l <| C *> x *> P *> R`  (`R = ∅`). -/
lemma rule_xR (l : ListBlank (Symbol 1)) :
    dR (xB ++ l) ∅ -[M]->* dL l (C3B ++ xB ++ PB ++ (∅ : ListBlank (Symbol 1))) := by
  unfoldBlocks; sim

/-- Coq `rule_DR`: `l <* Dl |> R -->* l <| x *> R`  (`R = ∅`). -/
lemma rule_DR (l : ListBlank (Symbol 1)) :
    dR (DlB ++ l) ∅ -[M]->* dL l (xB ++ (∅ : ListBlank (Symbol 1))) := by
  unfoldBlocks; sim

/-- Coq `rule_L`: `L <| C *> x *> r -->* L <* C1 <* Dl |> P *> r`  (`L = ∅`). -/
lemma rule_L (r : ListBlank (Symbol 1)) :
    dL ∅ (C3B ++ xB ++ r) -[M]->* dR (DlB ++ C1B ++ (∅ : ListBlank (Symbol 1))) (PB ++ r) := by
  unfoldBlocks; sim

/-- Coq `rule_P_R`: `l |> P *> R -->* l <| P *> R`  (`R = ∅`). -/
lemma rule_P_R (l : ListBlank (Symbol 1)) :
    dR l (PB ++ (∅ : ListBlank (Symbol 1))) -[M]->* dL l (PB ++ (∅ : ListBlank (Symbol 1))) := by
  unfoldBlocks; sim

/-! ## Iterated shift rules

Repeated block powers `b^n` (Coq `b^^n`), and the rules that sweep a whole run of
`x` blocks by induction on the count. -/

/-- Block power `b^n` (Coq `b^^n`): `n` copies concatenated, head-nearest first. -/
def blkPow (b : List (Symbol 1)) : ℕ → List (Symbol 1)
  | 0 => []
  | n + 1 => b ++ blkPow b n

@[simp] lemma blkPow_zero (b : List (Symbol 1)) : blkPow b 0 = [] := rfl
lemma blkPow_succ (b : List (Symbol 1)) (n : ℕ) : blkPow b (n + 1) = b ++ blkPow b n := rfl

@[simp] lemma blkPow_one (b : List (Symbol 1)) : blkPow b 1 = b := by
  simpa using blkPow_succ b 0

/-- Same-block concatenation commutes: `bⁿ ++ b = b ++ bⁿ` (Coq `lpow_shift`). -/
lemma blkPow_comm (b : List (Symbol 1)) (n : ℕ) : blkPow b n ++ b = b ++ blkPow b n := by
  induction n with
  | zero => simp [blkPow]
  | succ n ih => simp only [blkPow_succ, List.append_assoc, ih]

/-- Snoc form: `bⁿ⁺¹ = bⁿ ++ b`. -/
lemma blkPow_snoc (b : List (Symbol 1)) (n : ℕ) : blkPow b (n + 1) = blkPow b n ++ b := by
  rw [blkPow_succ, blkPow_comm]

/-- Additivity: `bⁿ⁺ᵐ = bⁿ ++ bᵐ` (Coq `lpow_add`). -/
lemma blkPow_add (b : List (Symbol 1)) (n m : ℕ) :
    blkPow b (n + m) = blkPow b n ++ blkPow b m := by
  induction n with
  | zero => rw [Nat.zero_add, blkPow_zero, List.nil_append]
  | succ n ih =>
      rw [show n + 1 + m = (n + m) + 1 by omega, blkPow_succ, ih, blkPow_succ, List.append_assoc]

/-- The closing identity of every block-power induction: after crossing one `b`
and then `bⁿ`, `bⁿ ++ (b ++ t)` is the same tape as `b ++ (bⁿ ++ t)`. -/
lemma blkPow_shift (b : List (Symbol 1)) (n : ℕ) (t : ListBlank (Symbol 1)) :
    blkPow b n ++ (b ++ t) = b ++ (blkPow b n ++ t) := by
  rw [← ListBlank.append_assoc', blkPow_comm, ListBlank.append_assoc']

-- Seal `blkPow` now that its equation lemmas are proven: unification must not
-- expand `blkPow xB 72141` while walking an append spine (it would recurse 72141
-- deep).  All later reasoning goes through `blkPow_zero`/`blkPow_succ`/`blkPow_comm`.
attribute [irreducible] blkPow

/-- Iterate a rightward block-crossing rule over a block power (Coq induction on
`b^^n`): a single-copy rule `bR *> · ↦ bL <* ·` lifts to `n` copies. -/
lemma iterate_right (bL bR : List (Symbol 1))
    (h : ∀ l r : ListBlank (Symbol 1), dR l (bR ++ r) -[M]->* dR (bL ++ l) r)
    (n : ℕ) (l r : ListBlank (Symbol 1)) :
    dR l (blkPow bR n ++ r) -[M]->* dR (blkPow bL n ++ l) r := by
  induction n generalizing l with
  | zero => simp only [blkPow_zero, ListBlank.append_empty]; exact Machine.EvStep.refl
  | succ n ih =>
      simp only [blkPow_succ, ListBlank.append_assoc']
      refine (h l (blkPow bR n ++ r)).trans ?_
      refine (ih (bL ++ l)).trans ?_
      rw [blkPow_shift]; exact Machine.EvStep.refl

/-- Iterate a leftward block-crossing rule over a block power. -/
lemma iterate_left (bL bR : List (Symbol 1))
    (h : ∀ l r : ListBlank (Symbol 1), dL (bL ++ l) r -[M]->* dL l (bR ++ r))
    (n : ℕ) (l r : ListBlank (Symbol 1)) :
    dL (blkPow bL n ++ l) r -[M]->* dL l (blkPow bR n ++ r) := by
  induction n generalizing r with
  | zero => simp only [blkPow_zero, ListBlank.append_empty]; exact Machine.EvStep.refl
  | succ n ih =>
      simp only [blkPow_succ, ListBlank.append_assoc']
      refine (h (blkPow bL n ++ l) r).trans ?_
      refine (ih (bR ++ r)).trans ?_
      rw [blkPow_shift]; exact Machine.EvStep.refl

/-- Coq `rule_xn_left`: `l <* x^^n <| r -->* l <| x^^n *> r`. -/
lemma rule_xn_left (n : ℕ) (l r : ListBlank (Symbol 1)) :
    dL (blkPow xB n ++ l) r -[M]->* dL l (blkPow xB n ++ r) := by
  induction n generalizing r with
  | zero => simp only [blkPow_zero, ListBlank.append_empty]; exact Machine.EvStep.refl
  | succ n ih =>
      simp only [blkPow_succ, ListBlank.append_assoc']
      refine (rule_x_left (blkPow xB n ++ l) r).trans ?_
      refine (ih (xB ++ r)).trans ?_
      rw [blkPow_shift]; exact Machine.EvStep.refl

/-- Coq `rule_xn_right`: `l |> x^^n *> r -->* l <* x^^n |> r`. -/
lemma rule_xn_right (n : ℕ) (l r : ListBlank (Symbol 1)) :
    dR l (blkPow xB n ++ r) -[M]->* dR (blkPow xB n ++ l) r := by
  induction n generalizing l with
  | zero => simp only [blkPow_zero, ListBlank.append_empty]; exact Machine.EvStep.refl
  | succ n ih =>
      simp only [blkPow_succ, ListBlank.append_assoc']
      refine (rule_x_right l (blkPow xB n ++ r)).trans ?_
      refine (ih (xB ++ l)).trans ?_
      rw [blkPow_shift]; exact Machine.EvStep.refl

/-- Coq `rule_P_xn`: `l |> P *> x^^n *> r -->* l <* x^^n |> P *> r`. -/
lemma rule_P_xn (n : ℕ) (l r : ListBlank (Symbol 1)) :
    dR l (PB ++ blkPow xB n ++ r) -[M]->* dR (blkPow xB n ++ l) (PB ++ r) := by
  induction n generalizing l with
  | zero => simp only [blkPow_zero, ListBlank.append_empty]; exact Machine.EvStep.refl
  | succ n ih =>
      simp only [blkPow_succ, ListBlank.append_assoc']
      refine (rule_P_x l (blkPow xB n ++ r)).trans ?_
      refine (ih (xB ++ l)).trans ?_
      rw [blkPow_shift]; exact Machine.EvStep.refl

/-! ## Composite `G`/`H` blocks and their rules

`Gr`/`Gl` are the mirror composite blocks the counter's "G-stride" sweeps.  Coq
builds `Gr` with `+>` (order preserved) and `Gl` with `<+` (order reversed), so
`Gl`'s block order is the reverse of `Gr`'s.  Crossing them is a chain of the
iterated `x`-rules and the single-`D` rules. -/

/-- `Gr = x³⁰⁰ Dr x³⁰⁸²⁶ Dr x⁷²¹⁴² Dr x³⁰⁷⁶ Dr x¹⁵³⁸ Dr` (right orientation). -/
def GrB : List (Symbol 1) :=
  blkPow xB 300 ++ DrB ++ blkPow xB 30826 ++ DrB ++ blkPow xB 72142 ++ DrB ++
    blkPow xB 3076 ++ DrB ++ blkPow xB 1538 ++ DrB

/-- `Gl` = `Gr` mirrored: `Dl x¹⁵³⁸ Dl x³⁰⁷⁶ Dl x⁷²¹⁴² Dl x³⁰⁸²⁶ Dl x³⁰⁰`. -/
def GlB : List (Symbol 1) :=
  DlB ++ blkPow xB 1538 ++ DlB ++ blkPow xB 3076 ++ DlB ++ blkPow xB 72142 ++ DlB ++
    blkPow xB 30826 ++ DlB ++ blkPow xB 300

/-- Coq `rule_G_right`: `l |> Gr *> r -->* l <* Gl |> r`. -/
lemma rule_G_right (l r : ListBlank (Symbol 1)) :
    dR l (GrB ++ r) -[M]->* dR (GlB ++ l) r := by
  simp only [GrB, GlB, List.append_assoc, ListBlank.append_assoc']
  refine (rule_xn_right 300 l _).trans ?_
  refine (rule_D_right _ _).trans ?_
  refine (rule_xn_right 30826 _ _).trans ?_
  refine (rule_D_right _ _).trans ?_
  refine (rule_xn_right 72142 _ _).trans ?_
  refine (rule_D_right _ _).trans ?_
  refine (rule_xn_right 3076 _ _).trans ?_
  refine (rule_D_right _ _).trans ?_
  refine (rule_xn_right 1538 _ _).trans ?_
  exact rule_D_right _ _

/-- Coq `rule_G_left`: `l <* Gl <| r -->* l <| Gr *> r`. -/
lemma rule_G_left (l r : ListBlank (Symbol 1)) :
    dL (GlB ++ l) r -[M]->* dL l (GrB ++ r) := by
  simp only [GrB, GlB, List.append_assoc, ListBlank.append_assoc']
  refine (rule_D_left _ _).trans ?_
  refine (rule_xn_left 1538 _ _).trans ?_
  refine (rule_D_left _ _).trans ?_
  refine (rule_xn_left 3076 _ _).trans ?_
  refine (rule_D_left _ _).trans ?_
  refine (rule_xn_left 72142 _ _).trans ?_
  refine (rule_D_left _ _).trans ?_
  refine (rule_xn_left 30826 _ _).trans ?_
  refine (rule_D_left _ _).trans ?_
  exact rule_xn_left 300 _ _

/-- Coq `rule_Gn_right`: `l |> Gr^^n *> r -->* l <* Gl^^n |> r`. -/
lemma rule_Gn_right (n : ℕ) (l r : ListBlank (Symbol 1)) :
    dR l (blkPow GrB n ++ r) -[M]->* dR (blkPow GlB n ++ l) r :=
  iterate_right GlB GrB rule_G_right n l r

/-- Coq `rule_Gn_left`: `l <* Gl^^n <| r -->* l <| Gr^^n *> r`. -/
lemma rule_Gn_left (n : ℕ) (l r : ListBlank (Symbol 1)) :
    dL (blkPow GlB n ++ l) r -[M]->* dL l (blkPow GrB n ++ r) :=
  iterate_left GlB GrB rule_G_left n l r

/-- `Hl` (Coq): the block deposited by one `P·Dr·Gr` macro-step. -/
def HlB : List (Symbol 1) :=
  blkPow xB 1537 ++ DlB ++ C1B ++ blkPow xB 3075 ++ DlB ++ C1B ++ blkPow xB 72141 ++ DlB ++ C1B ++
    blkPow xB 30825 ++ DlB ++ C1B ++ blkPow xB 299 ++ DlB ++ C1B

/-- `Fl` (Coq `C2 <+ x^^7640 <+ Dl <+ x^^10344`). -/
def FlB : List (Symbol 1) :=
  blkPow xB 10344 ++ DlB ++ blkPow xB 7640 ++ C2B

/-- One `P·Dr·x^(m+1)` macro-step, depositing `x^m·Dl·C1`.  The count `m` is kept
*abstract* so no huge block power ever enters a kernel defeq; `rule_P_DG` then
chains five instances, passing the large `blkPowᵢ` around only as opaque atoms. -/
lemma rule_P_Dxn (m : ℕ) (l r : ListBlank (Symbol 1)) :
    dR l (PB ++ (DrB ++ (blkPow xB (m + 1) ++ r))) -[M]->*
      dR (blkPow xB m ++ (DlB ++ C1B ++ l)) (PB ++ r) := by
  rw [blkPow_succ]
  simp only [List.append_assoc, ListBlank.append_assoc']
  refine (rule_P_Dx l (blkPow xB m ++ r)).trans ?_
  exact rule_P_xn m (DlB ++ C1B ++ l) r

/-!
`rule_P_DG`/`rule_P_DGn` (Coq): one macro-step `P·Dr·Gr ↦ Hl` and its iterate.
`rule_P_Dxn` does the per-block work; `rule_P_DG` chains five instances over the
concrete `Gr = x³⁰⁰ Dr x³⁰⁸²⁶ …`.  Perf note: the deposits `Dl ++ C1 ++ …` come
out left-associated while `Hl` is right-associated, so a naive closing `refl`
becomes a whole-term defeq that bridges that associativity across the large block
powers and kernel-timeouts.  Re-associating with `simp` *before* `refl` makes the
close syntactic; the `.trans` chain and the `simp [GrB, HlB]` unfold are each
cheap on their own. -/

/-- Coq `rule_P_DG`: `l |> P *> Dr *> Gr *> r -->* l <* Hl |> P *> Dr *> r`. -/
lemma rule_P_DG (l r : ListBlank (Symbol 1)) :
    dR l (PB ++ DrB ++ GrB ++ r) -[M]->* dR (HlB ++ l) (PB ++ DrB ++ r) := by
  simp only [GrB, HlB, List.append_assoc, ListBlank.append_assoc']
  refine (rule_P_Dxn 299 l _).trans ?_
  refine (rule_P_Dxn 30825 _ _).trans ?_
  refine (rule_P_Dxn 72141 _ _).trans ?_
  refine (rule_P_Dxn 3075 _ _).trans ?_
  refine (rule_P_Dxn 1537 _ _).trans ?_
  -- re-associate the `Dl ++ C1 ++ …` deposits to match Hl's right-nesting so the
  -- final `refl` is syntactic (not a whole-term defeq over the big block powers)
  simp only [List.append_assoc, ListBlank.append_assoc']
  exact Machine.EvStep.refl

/-- `rule_P_DG` with the tape appends right-associated, for chaining in `rule_P_DGn`. -/
lemma rule_P_DG' (l r : ListBlank (Symbol 1)) :
    dR l (PB ++ (DrB ++ (GrB ++ r))) -[M]->* dR (HlB ++ l) (PB ++ (DrB ++ r)) := by
  simpa only [List.append_assoc, ListBlank.append_assoc'] using rule_P_DG l r

/-- Coq `rule_P_DGn`: `l |> P *> Dr *> Gr^^n *> r -->* l <* Hl^^n |> P *> Dr *> r`. -/
lemma rule_P_DGn (n : ℕ) (l r : ListBlank (Symbol 1)) :
    dR l (PB ++ DrB ++ blkPow GrB n ++ r) -[M]->* dR (blkPow HlB n ++ l) (PB ++ DrB ++ r) := by
  induction n generalizing l with
  | zero => simp only [blkPow_zero, ListBlank.append_empty]; exact Machine.EvStep.refl
  | succ n ih =>
      simp only [blkPow_succ, List.append_assoc, ListBlank.append_assoc'] at ih ⊢
      refine (rule_P_DG' l (blkPow GrB n ++ r)).trans ?_
      refine (ih (HlB ++ l)).trans ?_
      rw [blkPow_shift]; exact Machine.EvStep.refl

/-! ## Symbolic tape

The verified simulator represents each tape side as a *list of symbols with
counts* (Coq `lsym`/`rsym`).  Counts are `ℕ` here (BusyCoq uses `positive`; a
count is always `≥ 1`).  The whole point is that a repeated block `x^n` is a
single symbol `l_xs n` carrying the number `n`, never the materialised
`blkPow xB n` — so the simulator manipulates the large Skelet #1 counts
symbolically, and only `lift` maps a symbolic tape back to the concrete
`ListBlank`. -/

/-- Left-tape symbols (Coq `lsym`), head-nearest first. -/
inductive Lsym
  | xs (n : ℕ) | D | P | C0 | C1 | C2 | C3
  | F0 | F1 | F2 | F3 | G0 | G1 | G2
  | Fs (n : ℕ) | Gs (n : ℕ) | Hs (n : ℕ)
  deriving DecidableEq, Repr

/-- Right-tape symbols (Coq `rsym`), head-nearest first. -/
inductive Rsym
  | xs (n : ℕ) | D | C | P | Gs (n : ℕ)
  deriving DecidableEq, Repr

/-- Concrete block a left symbol expands to (spliced head-nearest). -/
def Lsym.block : Lsym → List (Symbol 1)
  | .xs n => blkPow xB n
  | .D => DlB | .P => PB
  | .C0 => C0B | .C1 => C1B | .C2 => C2B | .C3 => C3B
  | .F0 => F0B | .F1 => F1B | .F2 => F2B | .F3 => F3B
  | .G0 => G0B | .G1 => G1B | .G2 => G2B
  | .Fs n => blkPow FlB n | .Gs n => blkPow GlB n | .Hs n => blkPow HlB n

/-- Concrete block a right symbol expands to (spliced head-nearest). -/
def Rsym.block : Rsym → List (Symbol 1)
  | .xs n => blkPow xB n
  | .D => DrB | .C => C3B | .P => PB | .Gs n => blkPow GrB n

/-- Lift a symbolic left tape to a concrete left `ListBlank` (Coq `lift_left`). -/
def liftLeft : List Lsym → ListBlank (Symbol 1)
  | [] => ∅
  | s :: t => s.block ++ liftLeft t

/-- Lift a symbolic right tape to a concrete right `ListBlank` (Coq `lift_right`). -/
def liftRight : List Rsym → ListBlank (Symbol 1)
  | [] => ∅
  | s :: t => s.block ++ liftRight t

/-- Head direction of a symbolic configuration. -/
inductive Dir | left | right
  deriving DecidableEq, Repr

/-- A symbolic configuration: head direction + both symbolic tape sides. -/
structure SConf where
  dir : Dir
  left : List Lsym
  right : List Rsym
  deriving DecidableEq

/-- Lift a symbolic configuration to a concrete `Config` (Coq `lift`): the
directed forms `dL`/`dR` from the two head directions. -/
def SConf.lift : SConf → Config 4 1
  | ⟨.left, l, r⟩ => dL (liftLeft l) (liftRight r)
  | ⟨.right, l, r⟩ => dR (liftLeft l) (liftRight r)

/-! ## Executable symbolic step

`simpleStep` (Coq `simple_step`) advances a symbolic configuration by one
"macro" move, folding whole `x^n`/`G^n` blocks in a single step.  The count-
merging smart constructors keep the symbolic tape normalised (a run of `x`s is
one symbol).  `decr n = n - 1` peels one copy off a block. -/

/-- `n - 1` (Coq `decr`); a count is always `≥ 1` so this drops one copy. -/
def decr (n : ℕ) : ℕ := n - 1

/-- Push `n` copies of `x` onto a left tape, merging with an `xs` head (Coq `lxs`). -/
def lxs (n : ℕ) (l : List Lsym) : List Lsym :=
  if n = 0 then l else match l with | .xs m :: l => .xs (n + m) :: l | l => .xs n :: l

/-- Push `n` copies of `x` onto a right tape, merging with an `xs` head (Coq `rxs`). -/
def rxs (n : ℕ) (r : List Rsym) : List Rsym :=
  if n = 0 then r else match r with | .xs m :: r => .xs (n + m) :: r | r => .xs n :: r

/-- Push `n` copies of `Fl`, merging with an `Fs` head (Coq `Fls`). -/
def Fls (n : ℕ) (l : List Lsym) : List Lsym :=
  if n = 0 then l else match l with | .Fs m :: l => .Fs (n + m) :: l | l => .Fs n :: l

/-- Push `n` copies of `Gl`, merging with a `Gs` head (Coq `Gls`). -/
def Gls (n : ℕ) (l : List Lsym) : List Lsym :=
  if n = 0 then l else match l with | .Gs m :: l => .Gs (n + m) :: l | l => .Gs n :: l

/-- Push `n` copies of `Gr`, merging with a `Gs` head (Coq `Grs`). -/
def Grs (n : ℕ) (r : List Rsym) : List Rsym :=
  if n = 0 then r else match r with | .Gs m :: r => .Gs (n + m) :: r | r => .Gs n :: r

/-- Push `n` copies of `Hl`, merging with an `Hs` head (Coq `Hls`). -/
def Hls (n : ℕ) (l : List Lsym) : List Lsym :=
  if n = 0 then l else match l with | .Hs m :: l => .Hs (n + m) :: l | l => .Hs n :: l

/-! The smart constructors expand under `lift` to the corresponding block power
prepended to the head (Coq `lift_lxs`, …), regardless of count merging. -/

lemma lift_lxs (n : ℕ) (l : List Lsym) :
    liftLeft (lxs n l) = blkPow xB n ++ liftLeft l := by
  cases n with
  | zero => simp [lxs, blkPow_zero]
  | succ n =>
    cases l with
    | nil => simp [lxs, liftLeft, Lsym.block]
    | cons s l => cases s <;> simp [lxs, liftLeft, Lsym.block, blkPow_add, List.append_assoc, ListBlank.append_assoc']

lemma lift_rxs (n : ℕ) (r : List Rsym) :
    liftRight (rxs n r) = blkPow xB n ++ liftRight r := by
  cases n with
  | zero => simp [rxs, blkPow_zero]
  | succ n =>
    cases r with
    | nil => simp [rxs, liftRight, Rsym.block]
    | cons s r => cases s <;> simp [rxs, liftRight, Rsym.block, blkPow_add, List.append_assoc, ListBlank.append_assoc']

lemma lift_Fls (n : ℕ) (l : List Lsym) :
    liftLeft (Fls n l) = blkPow FlB n ++ liftLeft l := by
  cases n with
  | zero => simp [Fls, blkPow_zero]
  | succ n =>
    cases l with
    | nil => simp [Fls, liftLeft, Lsym.block]
    | cons s l => cases s <;> simp [Fls, liftLeft, Lsym.block, blkPow_add, List.append_assoc, ListBlank.append_assoc']

lemma lift_Gls (n : ℕ) (l : List Lsym) :
    liftLeft (Gls n l) = blkPow GlB n ++ liftLeft l := by
  cases n with
  | zero => simp [Gls, blkPow_zero]
  | succ n =>
    cases l with
    | nil => simp [Gls, liftLeft, Lsym.block]
    | cons s l => cases s <;> simp [Gls, liftLeft, Lsym.block, blkPow_add, List.append_assoc, ListBlank.append_assoc']

lemma lift_Grs (n : ℕ) (r : List Rsym) :
    liftRight (Grs n r) = blkPow GrB n ++ liftRight r := by
  cases n with
  | zero => simp [Grs, blkPow_zero]
  | succ n =>
    cases r with
    | nil => simp [Grs, liftRight, Rsym.block]
    | cons s r => cases s <;> simp [Grs, liftRight, Rsym.block, blkPow_add, List.append_assoc, ListBlank.append_assoc']

lemma lift_Hls (n : ℕ) (l : List Lsym) :
    liftLeft (Hls n l) = blkPow HlB n ++ liftLeft l := by
  cases n with
  | zero => simp [Hls, blkPow_zero]
  | succ n =>
    cases l with
    | nil => simp [Hls, liftLeft, Lsym.block]
    | cons s l => cases s <;> simp [Hls, liftLeft, Lsym.block, blkPow_add, List.append_assoc, ListBlank.append_assoc']

/-- Peel one `x` off the front of a right tape (Coq `unrxs`); a `G` block is first
expanded to its `x…Dr…` spelling.  The head must carry a positive count (matched
as `n+1`); a count-0 head — which never occurs in a reachable configuration —
returns `none`, keeping `unrxs_spec` unconditional. -/
def unrxs (r : List Rsym) : Option (List Rsym) :=
  match r with
  | .xs (n + 1) :: r => some (rxs n r)
  | .Gs (n + 1) :: r =>
      some (.xs 299 :: .D :: .xs 30826 :: .D :: .xs 72142 :: .D ::
              .xs 3076 :: .D :: .xs 1538 :: .D :: Grs n r)
  | _ => none

/-- One symbolic macro-step (Coq `simple_step`). -/
def simpleStep : SConf → Option SConf
  | ⟨.right, l, r⟩ =>
    match r with
    | [] =>
      match l with
      | .xs (n + 1) :: l => some ⟨.left, lxs n l, [.C, .xs 1, .P]⟩
      | .D :: l => some ⟨.left, l, [.xs 1]⟩
      | _ => none
    | .xs n :: r => some ⟨.right, lxs n l, r⟩
    | .D :: r => some ⟨.right, .D :: l, r⟩
    | .C :: r =>
      match l with
      | .xs (n + 1) :: l => some ⟨.right, .C0 :: lxs n l, r⟩
      | .D :: l => some ⟨.right, .xs 1 :: .P :: l, r⟩
      | .C0 :: l => some ⟨.right, .G0 :: l, r⟩
      | .C2 :: l => some ⟨.right, .F0 :: l, r⟩
      | _ => none
    | [.P] => some ⟨.left, l, [.P]⟩
    | .P :: .xs n :: r => some ⟨.right, lxs n l, .P :: r⟩
    | .P :: .D :: .xs (n + 1) :: r => some ⟨.right, .D :: .C1 :: l, .P :: rxs n r⟩
    | .P :: .D :: .D :: r =>
      match unrxs r with
      | some r => some ⟨.right, .D :: .C1 :: .C2 :: l, r⟩
      | none => none
    | .P :: .D :: .C :: r =>
      match unrxs r with
      | some r => some ⟨.right, .D :: .G1 :: l, .P :: r⟩
      | none => none
    | .P :: .D :: .P :: r => some ⟨.right, .D :: .C1 :: l, r⟩
    | .P :: .D :: .Gs n :: r => some ⟨.right, Hls n l, .P :: .D :: r⟩
    | .P :: .C :: r =>
      match unrxs r with
      | some r => some ⟨.left, l, .P :: .D :: .P :: r⟩
      | none => none
    | .P :: .P :: r => some ⟨.right, lxs 1 l, r⟩
    | .Gs n :: r => some ⟨.right, Gls n l, r⟩
    | _ => none
  | ⟨.left, l, r⟩ =>
    match l with
    | [] =>
      match r with
      | .C :: r =>
        match unrxs r with
        | some r => some ⟨.right, [.D, .C1], .P :: r⟩
        | none => none
      | _ => none
    | .xs n :: l => some ⟨.left, l, rxs n r⟩
    | .D :: l => some ⟨.left, l, .D :: r⟩
    | .P :: l => some ⟨.left, l, .P :: r⟩
    | .C0 :: l => some ⟨.right, .xs 1 :: .C1 :: l, r⟩
    | .C1 :: l => some ⟨.right, .C2 :: l, r⟩
    | .C2 :: l => some ⟨.right, .xs 1 :: .C3 :: l, r⟩
    | .C3 :: l => some ⟨.left, l, .C :: r⟩
    | .F0 :: l => some ⟨.right, .xs 1 :: .F1 :: l, r⟩
    | .F1 :: l => some ⟨.right, .F2 :: l, r⟩
    | .F2 :: l => some ⟨.right, .xs 1 :: .F3 :: l, r⟩
    | .F3 :: .xs (n + 1) :: l => some ⟨.right, .D :: .C1 :: .P :: lxs n l, r⟩
    | .G0 :: l => some ⟨.right, .xs 1 :: .G1 :: l, r⟩
    | .G1 :: l => some ⟨.right, .G2 :: l, r⟩
    | .G2 :: l => some ⟨.right, .xs 1 :: .D :: .P :: l, r⟩
    | .Gs n :: l => some ⟨.left, l, Grs n r⟩
    | _ => none

/-- Soundness of `unrxs` (Coq `unrxs_spec`): peeling `x` off the symbolic tape
matches prepending one `x` block to the concrete tape. -/
lemma unrxs_spec {r r' : List Rsym} (h : unrxs r = some r') :
    liftRight r = xB ++ liftRight r' := by
  unfold unrxs at h
  split at h
  · -- `.xs (n+1) :: r₀`
    injection h with h; subst h
    rw [liftRight, Rsym.block, lift_rxs, blkPow_succ, ListBlank.append_assoc']
  · -- `.Gs (n+1) :: r₀`
    injection h with h; subst h
    rw [liftRight, Rsym.block, blkPow_succ]
    simp only [liftRight, Rsym.block, lift_Grs, GrB,
      show blkPow xB 300 = xB ++ blkPow xB 299 from blkPow_succ xB 299,
      List.append_assoc, ListBlank.append_assoc']
  · exact absurd h (by simp)

/-! The guarded mid-sequence cases (`x > R`, `x > C`, `> P D x`, `x F3 <`) consume
one `x`, so under `lift` their tail associates differently from the base rules.
These restatements match the `lift` output directly (right-associated, with the
count `n+1` still folded), so `solveStep` can apply them with `_` arguments. -/

lemma rule_xR' (n : ℕ) (l : ListBlank (Symbol 1)) :
    dR (blkPow xB (n + 1) ++ l) ∅ -[M]->*
      dL (blkPow xB n ++ l) (C3B ++ (xB ++ (PB ++ (∅ : ListBlank (Symbol 1))))) := by
  have hb := rule_xR (blkPow xB n ++ l)
  simp only [blkPow_succ, List.append_assoc, ListBlank.append_assoc'] at hb ⊢
  exact hb

lemma rule_C30' (n : ℕ) (l r : ListBlank (Symbol 1)) :
    dR (blkPow xB (n + 1) ++ l) (C3B ++ r) -[M]->* dR (C0B ++ (blkPow xB n ++ l)) r := by
  have hb := rule_C30 (blkPow xB n ++ l) r
  simp only [blkPow_succ, List.append_assoc, ListBlank.append_assoc'] at hb ⊢
  exact hb

lemma rule_P_Dx' (n : ℕ) (l r : ListBlank (Symbol 1)) :
    dR l (PB ++ (DrB ++ (blkPow xB (n + 1) ++ r))) -[M]->*
      dR (DlB ++ (C1B ++ l)) (PB ++ (blkPow xB n ++ r)) := by
  have hb := rule_P_Dx l (blkPow xB n ++ r)
  simp only [blkPow_succ, List.append_assoc, ListBlank.append_assoc'] at hb ⊢
  exact hb

lemma rule_F3' (n : ℕ) (l r : ListBlank (Symbol 1)) :
    dL (F3B ++ (blkPow xB (n + 1) ++ l)) r -[M]->*
      dR (DlB ++ (C1B ++ (PB ++ (blkPow xB n ++ l)))) r := by
  have hb := rule_F3 (blkPow xB n ++ l) r
  simp only [blkPow_succ, List.append_assoc, ListBlank.append_assoc'] at hb ⊢
  exact hb

-- Seal every block so that `solveStep`'s rule dispatch matches at the *atom*
-- level: a wrong rule fails fast (`xB =?= blkPow xB n`, `blkPow GrB ? =?= …`)
-- instead of unfolding a block and churning the append comparison.  All lemmas
-- above that need the unfoldings (`unrxs_spec`, `rule_P_DG`, the `sim` rules) are
-- already elaborated.
attribute [irreducible]
  xB DlB DrB C0B C1B C2B C3B PB F0B F1B F2B F3B G0B G1B G2B GrB GlB HlB FlB

/-- Discharge one reached `simple_step_spec` case: expand `lift` through the head
symbols and count-merging constructors, rewrite any peeled `unrxs` tail, then
apply the matching shift rule. -/
local macro "solveStep" : tactic => `(tactic|
  (simp only [SConf.lift, liftLeft, liftRight, Lsym.block, Rsym.block,
      lift_lxs, lift_rxs, lift_Fls, lift_Gls, lift_Grs, lift_Hls,
      blkPow_succ, blkPow_zero, List.append_nil]
   try rw [unrxs_spec ‹unrxs _ = some _›]
   try simp only [← List.append_assoc, ← ListBlank.append_assoc']
   with_reducible first
    | exact rule_x_left _ _        | exact rule_D_left _ _        | exact rule_C_left _ _
    | exact rule_x_right _ _       | exact rule_D_right _ _       | exact rule_C30 _ _
    | exact rule_C01 _ _           | exact rule_C12 _ _           | exact rule_C23 _ _
    | exact rule_DC _ _            | exact rule_C2_C _ _          | exact rule_F0 _ _
    | exact rule_F1 _ _            | exact rule_F2 _ _            | exact rule_F3 _ _
    | exact rule_C03 _ _           | exact rule_G0 _ _            | exact rule_G1 _ _
    | exact rule_G2 _ _            | exact rule_P_left _ _        | exact rule_P_P _ _
    | exact rule_P_x _ _           | exact rule_P_Dx _ _          | exact rule_P_Cx _ _
    | exact rule_P_DP _ _          | exact rule_P_DDx _ _         | exact rule_P_DCx _ _
    | exact rule_xR _              | exact rule_DR _              | exact rule_L _
    | exact rule_P_R _             | exact rule_xn_left _ _ _     | exact rule_xn_right _ _ _
    | exact rule_P_xn _ _ _        | exact rule_Gn_left _ _ _     | exact rule_Gn_right _ _ _
    | exact rule_P_DGn _ _ _))

/-- Soundness of the symbolic simulator (Coq `simple_step_spec`): every symbolic
macro-step corresponds to a real machine run.  Splits `h` across every
`simpleStep` case and discharges each with `solveStep` (the `x F3 <` case needs a
tail-associativity bridge). -/
lemma simple_step_spec {c c' : SConf} (h : simpleStep c = some c') :
    c.lift -[M]->* c'.lift := by
  obtain ⟨dir, l, r⟩ := c
  cases dir <;>
  · simp only [simpleStep] at h
    repeat' split at h
    all_goals first
      | (injection h with h; subst h; solveStep)
      | (injection h with h; subst h
         -- the guarded mid-sequence cases: match the `lift` form via the primed
         -- rules (right-associated, count `n+1` folded)
         simp only [SConf.lift, liftLeft, liftRight, Lsym.block, Rsym.block,
           lift_lxs, lift_rxs, blkPow_one, blkPow_zero, List.append_nil]
         first
           | exact rule_xR' _ _   | exact rule_C30' _ _ _
           | exact rule_P_Dx' _ _ _ | exact rule_F3' _ _ _)
      | simp at h

/-! ## Stride acceleration

The symbolic simulator folds each `x^n` block into one step, but the counter's
Collatz-like outer loop still needs acceleration to reach the eventual cycle in a
feasible number of steps.  `stride` sweeps a whole run of `x`s through the right
tape at once, applying the carry (Coq `stride`; counts are `ℕ`, with `positive`
`n~0~0 = 4n`, `n~0 = 2n`, `N.shiftr n' 2 = n'/4`). -/

/-- Largest stride available at the head (Coq `max_stride`). -/
def maxStride : ℕ → List Rsym → Option ℕ
  | _, [.P] => none
  | _, .P :: _ => some 0
  | _, [] => some 0
  | xs, .xs xs' :: t => maxStride (xs + xs') t
  | _, .D :: t => maxStride 0 t
  | xs, .C :: t =>
      match maxStride 0 t with
      | some n' => some (min xs (n' >>> 2))
      | none => some xs
  | _, .Gs _ :: t => maxStride 0 t

/-- Sweep a run of `xs` copies of `x` through the tape with stride `n` (Coq
`stride`); `none` if the stride can't complete at the head. -/
def stride : ℕ → ℕ → List Rsym → Option (List Rsym)
  | xs, _, [.P] => some (rxs xs [.P])
  | _, _, .P :: _ => none
  | _, _, [] => none
  | xs, n, .xs xs' :: t => stride (xs + xs') n t
  | xs, n, .D :: t =>
      match stride 0 n t with
      | some t => some (rxs xs (.D :: t))
      | none => none
  | xs, n, .C :: t =>
      if n ≤ xs then
        match stride 0 (4 * n) t with
        | some t => some (rxs (xs - n) (.C :: rxs (2 * n) t))
        | none => none
      else none
  | xs, n, .Gs gs :: t =>
      match stride 0 n t with
      | some t => some (rxs xs (Grs gs t))
      | none => none

/-- Number of `C`-marks left of the head — the stride recursion depth (Coq
`stride_level`). -/
def strideLevel : List Rsym → ℕ
  | [] => 0
  | .C :: t => strideLevel t + 1
  | _ :: t => strideLevel t

/-! Count-merge algebra: pushing two runs is the same as pushing their sum. -/

lemma rxs_rxs (n m : ℕ) (t : List Rsym) : rxs n (rxs m t) = rxs (n + m) t := by
  rcases Nat.eq_zero_or_pos m with rfl | hm
  · rfl
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · rw [Nat.zero_add]; rfl
  unfold rxs
  rw [if_neg hm.ne', if_neg hn.ne', if_neg (by omega : ¬ n + m = 0)]
  cases t with
  | nil => rfl
  | cons s t => cases s with
    | xs k => simp only [Nat.add_assoc]
    | _ => rfl

lemma Grs_Grs (n m : ℕ) (t : List Rsym) : Grs n (Grs m t) = Grs (n + m) t := by
  rcases Nat.eq_zero_or_pos m with rfl | hm
  · rfl
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · rw [Nat.zero_add]; rfl
  unfold Grs
  rw [if_neg hm.ne', if_neg hn.ne', if_neg (by omega : ¬ n + m = 0)]
  cases t with
  | nil => rfl
  | cons s t => cases s with
    | Gs k => simp only [Nat.add_assoc]
    | _ => rfl

/-- A run pushed into a right tape before `stride` folds into the seed (Coq
`stride_rxs`). -/
lemma stride_rxs (xs n xs' : ℕ) (t : List Rsym) :
    stride xs n (rxs xs' t) = stride (xs + xs') n t := by
  rcases Nat.eq_zero_or_pos xs' with rfl | hxs'
  · rw [Nat.add_zero]; rfl
  unfold rxs; rw [if_neg hxs'.ne']
  cases t with
  | nil => rfl
  | cons s t => cases s with
    | xs k => simp only [stride]; rw [Nat.add_assoc]
    | _ => rfl

/-! `strideLevel` is invariant under the count-merging constructors. -/

lemma strideLevel_rxs (xs : ℕ) (t : List Rsym) : strideLevel (rxs xs t) = strideLevel t := by
  rcases Nat.eq_zero_or_pos xs with hxs | hxs
  · subst hxs; simp [rxs]
  · unfold rxs; rw [if_neg (by omega)]
    cases t with
    | nil => rfl
    | cons s t => cases s <;> rfl

lemma strideLevel_Grs (xs : ℕ) (t : List Rsym) : strideLevel (Grs xs t) = strideLevel t := by
  rcases Nat.eq_zero_or_pos xs with hxs | hxs
  · subst hxs; simp [Grs]
  · unfold Grs; rw [if_neg (by omega)]
    cases t with
    | nil => rfl
    | cons s t => cases s <;> rfl

/-- `stride` preserves the number of `C`-marks (Coq `stride_same_level`). -/
lemma stride_same_level (xs n : ℕ) (t t' : List Rsym) (H : stride xs n t = some t') :
    strideLevel t = strideLevel t' := by
  induction t generalizing xs n t' with
  | nil => simp [stride] at H
  | cons s t IH =>
    cases s with
    | xs k =>
      simp only [stride] at H
      simp only [strideLevel]; exact IH (xs + k) n t' H
    | D =>
      simp only [stride] at H
      split at H <;> [skip; simp at H]
      rename_i t1 hE; simp only [Option.some.injEq] at H; subst H
      rw [strideLevel_rxs]; simp only [strideLevel]; exact IH 0 n t1 hE
    | C =>
      simp only [stride] at H
      split at H
      · split at H <;> [skip; simp at H]
        rename_i t1 hE; simp only [Option.some.injEq] at H; subst H
        rw [strideLevel_rxs]; simp only [strideLevel]; rw [strideLevel_rxs]
        exact congrArg (· + 1) (IH 0 (4 * n) t1 hE)
      · simp at H
    | P =>
      cases t with
      | nil => simp only [stride, Option.some.injEq] at H; subst H; rw [strideLevel_rxs]
      | cons s2 t2 => simp [stride] at H
    | Gs gs =>
      simp only [stride] at H
      split at H <;> [skip; simp at H]
      rename_i t1 hE; simp only [Option.some.injEq] at H; subst H
      rw [strideLevel_rxs, strideLevel_Grs]; simp only [strideLevel]; exact IH 0 n t1 hE

/-- Adding to the stride seed factors out as a pushed run (Coq `stride_more`). -/
lemma stride_more (t t' : List Rsym) (xs xs' n : ℕ) (H : stride xs' n t = some t') :
    stride (xs + xs') n t = some (rxs xs t') := by
  induction t generalizing xs' t' n with
  | nil => simp [stride] at H
  | cons s t IH =>
    cases s with
    | xs k =>
      simp only [stride] at H ⊢
      rw [show xs + xs' + k = xs + (xs' + k) from by omega]
      exact IH t' (xs' + k) n H
    | D =>
      simp only [stride] at H ⊢
      split at H <;> [skip; simp at H]
      rename_i t1 hE; simp only [Option.some.injEq] at H; subst H
      rw [rxs_rxs]
    | C =>
      simp only [stride] at H ⊢
      split at H <;> [skip; simp at H]
      rename_i hle
      split at H <;> [skip; simp at H]
      rename_i t1 hE; simp only [Option.some.injEq] at H; subst H
      rw [if_pos (by omega), rxs_rxs, show xs + xs' - n = xs + (xs' - n) from by omega]
    | P =>
      cases t with
      | nil =>
        simp only [stride, Option.some.injEq] at H; subst H
        simp only [stride]; rw [rxs_rxs]
      | cons s2 t2 => simp [stride] at H
    | Gs gs =>
      simp only [stride] at H ⊢
      split at H <;> [skip; simp at H]
      rename_i t1 hE; simp only [Option.some.injEq] at H; subst H
      rw [rxs_rxs]

/-- Striding through a `G`-block (Coq `stride_Grs`). -/
lemma stride_Grs (t t' : List Rsym) (xs gs n : ℕ) (H : stride 0 n t = some t') :
    stride xs n (Grs gs t) = some (rxs xs (Grs gs t')) := by
  rcases Nat.eq_zero_or_pos gs with rfl | hgs
  · exact stride_more t t' xs 0 n H
  cases t with
  | nil => simp [stride] at H
  | cons s t2 =>
    cases s with
    | Gs k =>
      rw [show Grs gs (Rsym.Gs k :: t2) = Rsym.Gs (gs + k) :: t2 from by
        unfold Grs; rw [if_neg hgs.ne']]
      simp only [stride] at H ⊢
      split at H <;> [skip; simp at H]
      rename_i t1 hE; simp only [Option.some.injEq] at H; subst H
      rw [show rxs 0 (Grs k t1) = Grs k t1 from rfl, Grs_Grs]
    | xs k =>
      rw [show Grs gs (Rsym.xs k :: t2) = Rsym.Gs gs :: (Rsym.xs k :: t2) from by
        unfold Grs; rw [if_neg hgs.ne'],
        show stride xs n (Rsym.Gs gs :: (Rsym.xs k :: t2))
          = match stride 0 n (Rsym.xs k :: t2) with
            | some t1 => some (rxs xs (Grs gs t1)) | none => none from rfl, H]
    | D =>
      rw [show Grs gs (Rsym.D :: t2) = Rsym.Gs gs :: (Rsym.D :: t2) from by
        unfold Grs; rw [if_neg hgs.ne'],
        show stride xs n (Rsym.Gs gs :: (Rsym.D :: t2))
          = match stride 0 n (Rsym.D :: t2) with
            | some t1 => some (rxs xs (Grs gs t1)) | none => none from rfl, H]
    | C =>
      rw [show Grs gs (Rsym.C :: t2) = Rsym.Gs gs :: (Rsym.C :: t2) from by
        unfold Grs; rw [if_neg hgs.ne'],
        show stride xs n (Rsym.Gs gs :: (Rsym.C :: t2))
          = match stride 0 n (Rsym.C :: t2) with
            | some t1 => some (rxs xs (Grs gs t1)) | none => none from rfl, H]
    | P =>
      rw [show Grs gs (Rsym.P :: t2) = Rsym.Gs gs :: (Rsym.P :: t2) from by
        unfold Grs; rw [if_neg hgs.ne'],
        show stride xs n (Rsym.Gs gs :: (Rsym.P :: t2))
          = match stride 0 n (Rsym.P :: t2) with
            | some t1 => some (rxs xs (Grs gs t1)) | none => none from rfl, H]

/-- Split a stride of `n + m` into a stride of `n` then `m` (Coq `stride_add`). -/
lemma stride_add (t t2 : List Rsym) (xs n m : ℕ) (H : stride xs (n + m) t = some t2) :
    ∃ t1, stride xs n t = some t1 ∧ stride 0 m t1 = some t2 := by
  induction t generalizing xs t2 n m with
  | nil => simp [stride] at H
  | cons s t IH =>
    cases s with
    | xs k =>
      simp only [stride] at H ⊢
      exact IH t2 (xs + k) n m H
    | D =>
      simp only [stride] at H
      split at H <;> [skip; simp at H]
      rename_i t2' hE; simp only [Option.some.injEq] at H; subst H
      obtain ⟨t1, h1, h2⟩ := IH t2' 0 n m hE
      refine ⟨rxs xs (.D :: t1), ?_, ?_⟩
      · show stride xs n (Rsym.D :: t) = _
        simp only [stride]; rw [h1]
      · rw [stride_rxs, Nat.zero_add]
        show stride xs m (Rsym.D :: t1) = _
        simp only [stride]; rw [h2]
    | C =>
      simp only [stride] at H
      split at H <;> [skip; simp at H]
      rename_i hle
      split at H <;> [skip; simp at H]
      rename_i t2' hE; simp only [Option.some.injEq] at H; subst H
      rw [Nat.mul_add] at hE
      obtain ⟨t1, h1, h2⟩ := IH t2' 0 (4 * n) (4 * m) hE
      refine ⟨rxs (xs - n) (.C :: rxs (2 * n) t1), ?_, ?_⟩
      · show stride xs n (Rsym.C :: t) = _
        simp only [stride]; rw [if_pos (by omega : n ≤ xs), h1]
      · rw [stride_rxs, Nat.zero_add]
        show stride (xs - n) m (Rsym.C :: rxs (2 * n) t1) = _
        simp only [stride]; rw [if_pos (by omega : m ≤ xs - n), stride_rxs]
        have h2' := stride_more t1 t2' (2 * n) 0 (4 * m) h2
        rw [Nat.add_zero] at h2'
        rw [Nat.zero_add, h2']
        simp only [rxs_rxs]
        rw [Nat.sub_sub, show 2 * m + 2 * n = 2 * (n + m) from by omega]
    | P =>
      cases t with
      | nil =>
        simp only [stride, Option.some.injEq] at H; subst H
        refine ⟨rxs xs [.P], ?_, ?_⟩
        · rfl
        · rw [stride_rxs, Nat.zero_add]; rfl
      | cons s2 t2 => simp [stride] at H
    | Gs gs =>
      simp only [stride] at H
      split at H <;> [skip; simp at H]
      rename_i t2' hE; simp only [Option.some.injEq] at H; subst H
      obtain ⟨t1, h1, h2⟩ := IH t2' 0 n m hE
      refine ⟨rxs xs (Grs gs t1), ?_, ?_⟩
      · show stride xs n (Rsym.Gs gs :: t) = _
        simp only [stride]; rw [h1]
      · rw [stride_rxs, Nat.zero_add]
        exact stride_Grs t1 t2' xs gs m h2

/-! ### `stride_correct'` case helpers

Each is one arm of the `stride_correct'` induction, taking the recursion
hypothesis `IH` for the tail `t`. -/

/-- Abbreviation for the stride-correctness statement on a tape `t`. -/
private abbrev StrideStmt (t : List Rsym) : Prop :=
  ∀ (t' : List Rsym) (xs : ℕ) (l : ListBlank (Symbol 1)),
    stride xs 1 t = some t' → dR (blkPow xB xs ++ l) (liftRight t) -[M]->* dL l (liftRight t')

private lemma stride_case_xs (t : List Rsym) (IH : StrideStmt t)
    (t' : List Rsym) (xs xs' : ℕ) (l : ListBlank (Symbol 1))
    (H : stride xs 1 (.xs xs' :: t) = some t') :
    dR (blkPow xB xs ++ l) (liftRight (.xs xs' :: t)) -[M]->* dL l (liftRight t') := by
  simp only [stride] at H
  rw [liftRight, Rsym.block]
  refine (rule_xn_right xs' (blkPow xB xs ++ l) (liftRight t)).trans ?_
  rw [← ListBlank.append_assoc', ← blkPow_add, Nat.add_comm xs' xs]
  exact IH t' (xs + xs') l H

private lemma stride_case_D (t : List Rsym) (IH : StrideStmt t)
    (t' : List Rsym) (xs : ℕ) (l : ListBlank (Symbol 1))
    (H : stride xs 1 (.D :: t) = some t') :
    dR (blkPow xB xs ++ l) (liftRight (.D :: t)) -[M]->* dL l (liftRight t') := by
  simp only [stride] at H
  split at H <;> [skip; simp at H]
  rename_i t1 hE; simp only [Option.some.injEq] at H; subst H
  simp only [liftRight, Rsym.block, lift_rxs]
  refine (rule_D_right (blkPow xB xs ++ l) (liftRight t)).trans ?_
  have hIH := IH t1 0 (DlB ++ (blkPow xB xs ++ l)) hE
  simp only [blkPow_zero, ListBlank.append_empty] at hIH
  refine hIH.trans ?_
  refine (rule_D_left (blkPow xB xs ++ l) (liftRight t1)).trans ?_
  exact rule_xn_left xs l (DrB ++ liftRight t1)

private lemma stride_case_Gs (t : List Rsym) (IH : StrideStmt t)
    (t' : List Rsym) (gs xs : ℕ) (l : ListBlank (Symbol 1))
    (H : stride xs 1 (.Gs gs :: t) = some t') :
    dR (blkPow xB xs ++ l) (liftRight (.Gs gs :: t)) -[M]->* dL l (liftRight t') := by
  simp only [stride] at H
  split at H <;> [skip; simp at H]
  rename_i t1 hE; simp only [Option.some.injEq] at H; subst H
  simp only [liftRight, Rsym.block, lift_rxs, lift_Grs]
  refine (rule_Gn_right gs (blkPow xB xs ++ l) (liftRight t)).trans ?_
  have hIH := IH t1 0 (blkPow GlB gs ++ (blkPow xB xs ++ l)) hE
  simp only [blkPow_zero, ListBlank.append_empty] at hIH
  refine hIH.trans ?_
  refine (rule_Gn_left gs (blkPow xB xs ++ l) (liftRight t1)).trans ?_
  exact rule_xn_left xs l (blkPow GrB gs ++ liftRight t1)

private lemma stride_case_P (t : List Rsym)
    (t' : List Rsym) (xs : ℕ) (l : ListBlank (Symbol 1))
    (H : stride xs 1 (.P :: t) = some t') :
    dR (blkPow xB xs ++ l) (liftRight (.P :: t)) -[M]->* dL l (liftRight t') := by
  cases t with
  | cons s2 t2 => simp [stride] at H
  | nil =>
    simp only [stride, Option.some.injEq] at H; subst H
    simp only [liftRight, Rsym.block, lift_rxs]
    refine (rule_P_R (blkPow xB xs ++ l)).trans ?_
    exact rule_xn_left xs l (PB ++ (∅ : ListBlank (Symbol 1)))

/-- Soundness of one stride (Coq `stride_correct'`): a stride of `1` across the
tape corresponds to a real machine sweep left, carrying `x^xs` and turning the
head around.  Induction on the number of `C`-marks `k`, then on the tape. -/
lemma stride_correct' (k : ℕ) : ∀ (t t' : List Rsym) (xs : ℕ) (l : ListBlank (Symbol 1)),
    strideLevel t = k → stride xs 1 t = some t' →
    dR (blkPow xB xs ++ l) (liftRight t) -[M]->* dL l (liftRight t') := by
  induction k with
  | zero =>
    intro t
    induction t with
    | nil => intro t' xs l _ H; simp [stride] at H
    | cons s t IHt =>
      intro t' xs l Hlevel H
      cases s with
      | xs xs' => exact stride_case_xs t (fun a b c h => IHt a b c Hlevel h) t' xs xs' l H
      | D => exact stride_case_D t (fun a b c h => IHt a b c Hlevel h) t' xs l H
      | Gs gs => exact stride_case_Gs t (fun a b c h => IHt a b c Hlevel h) t' gs xs l H
      | P => exact stride_case_P t t' xs l H
      | C => simp only [strideLevel] at Hlevel; omega
  | succ k IHk =>
    intro t
    induction t with
    | nil => intro t' xs l _ H; simp [stride] at H
    | cons s t IHt =>
      intro t' xs l Hlevel H
      cases s with
      | xs xs' => exact stride_case_xs t (fun a b c h => IHt a b c Hlevel h) t' xs xs' l H
      | D => exact stride_case_D t (fun a b c h => IHt a b c Hlevel h) t' xs l H
      | Gs gs => exact stride_case_Gs t (fun a b c h => IHt a b c Hlevel h) t' gs xs l H
      | P => exact stride_case_P t t' xs l H
      | C =>
        have Hlvl : strideLevel t = k := by simp only [strideLevel] at Hlevel; omega
        simp only [stride] at H
        split at H <;> [skip; simp at H]
        rename_i hle
        split at H <;> [skip; simp at H]
        rename_i tfin hE
        simp only [Option.some.injEq] at H; subst H
        simp only [liftRight, Rsym.block, lift_rxs, Nat.mul_one] at *
        obtain ⟨u, rfl⟩ : ∃ u, xs = u + 1 := ⟨xs - 1, by omega⟩
        simp only [Nat.add_sub_cancel]
        rw [blkPow_succ, ListBlank.append_assoc']
        refine (rule_C30 (blkPow xB u ++ l) (liftRight t)).trans ?_
        -- round 1: stride 0 4 = stride 0 1 then stride 0 3
        rw [show (4 : ℕ) = 1 + 3 from rfl] at hE
        obtain ⟨t1, hst1, hE⟩ := stride_add t tfin 0 1 3 hE
        have r1 := IHk t t1 0 (C0B ++ (blkPow xB u ++ l)) Hlvl hst1
        simp only [blkPow_zero, ListBlank.append_empty] at r1
        refine r1.trans ?_
        refine (rule_C01 (blkPow xB u ++ l) (liftRight t1)).trans ?_
        -- round 2: stride 0 3 = stride 0 1 then stride 0 2
        rw [show (3 : ℕ) = 1 + 2 from rfl] at hE
        obtain ⟨t2, hst2, hE⟩ := stride_add t1 tfin 0 1 2 hE
        have Hlvl1 : strideLevel t1 = k := (stride_same_level 0 1 t t1 hst1).symm.trans Hlvl
        have r2 := IHk t1 t2 0 (xB ++ C1B ++ (blkPow xB u ++ l)) Hlvl1 hst2
        simp only [blkPow_zero, ListBlank.append_empty] at r2
        refine r2.trans ?_
        rw [ListBlank.append_assoc']
        refine (rule_x_left (C1B ++ (blkPow xB u ++ l)) (liftRight t2)).trans ?_
        refine (rule_C12 (blkPow xB u ++ l) (xB ++ liftRight t2)).trans ?_
        refine (rule_x_right (C2B ++ (blkPow xB u ++ l)) (liftRight t2)).trans ?_
        -- round 3: stride 0 2 = stride 0 1 then stride 0 1
        rw [show (2 : ℕ) = 1 + 1 from rfl] at hE
        obtain ⟨t3, hst3, hE⟩ := stride_add t2 tfin 0 1 1 hE
        have Hlvl2 : strideLevel t2 = k := (stride_same_level 0 1 t1 t2 hst2).symm.trans Hlvl1
        have r3 := IHk t2 t3 0 (xB ++ (C2B ++ (blkPow xB u ++ l))) Hlvl2 hst3
        simp only [blkPow_zero, ListBlank.append_empty] at r3
        refine r3.trans ?_
        refine (rule_x_left (C2B ++ (blkPow xB u ++ l)) (liftRight t3)).trans ?_
        refine (rule_C23 (blkPow xB u ++ l) (xB ++ liftRight t3)).trans ?_
        refine (rule_x_right (xB ++ C3B ++ (blkPow xB u ++ l)) (liftRight t3)).trans ?_
        -- round 4: final stride 0 1 t3 = tfin
        have Hlvl3 : strideLevel t3 = k := (stride_same_level 0 1 t2 t3 hst3).symm.trans Hlvl2
        have r4 := IHk t3 tfin 0 (xB ++ (xB ++ C3B ++ (blkPow xB u ++ l))) Hlvl3 hE
        simp only [blkPow_zero, ListBlank.append_empty] at r4
        refine r4.trans ?_
        refine (rule_x_left (xB ++ C3B ++ (blkPow xB u ++ l)) (liftRight tfin)).trans ?_
        rw [ListBlank.append_assoc']
        refine (rule_x_left (C3B ++ (blkPow xB u ++ l)) (xB ++ liftRight tfin)).trans ?_
        refine (rule_C_left (blkPow xB u ++ l) (xB ++ (xB ++ liftRight tfin))).trans ?_
        refine (rule_xn_left u l (C3B ++ (xB ++ (xB ++ liftRight tfin)))).trans ?_
        simp only [show (2 : ℕ) = 1 + 1 from rfl, blkPow_succ, blkPow_zero,
          ListBlank.append_empty, ListBlank.append_assoc']
        exact Machine.EvStep.refl

/-! ## Universal cycle constants (Coq `uni_P`, `uni_T`, `F`, `G`, `J`, `K`) -/

/-- Coq `uni_P`. -/
def uni_P : ℕ := 53946

/-- Coq `uni_T = 4 * uni_P - 5`. -/
def uni_T : ℕ := 4 * uni_P - 5

/-- Coq `J`: the fixed left-tape prefix crossed by one universal cycle. -/
def Jconst : List Lsym :=
  [.D, .C2, .xs 95, .C0,
   .xs 7713, .D, .D, .xs 1866, .C1,
   .xs 13231, .D, .xs 6197, .C3,
   .xs 11066, .D, .xs 7279, .C0,
   .xs 10524, .D, .xs 7550, .C2,
   .xs 10389, .D, .xs 7618, .C1,
   .xs 10355, .D, .xs 7635, .C3,
   .xs 10347, .D, .xs 7639, .C3,
   .xs 10345, .D, .xs 7640, .C1]

/-- Coq `K`: the periodic right tape of the terminal cycle. -/
def Kconst : List Rsym :=
  [.xs 7639, .D, .xs 10347, .C,
   .xs 7635, .D, .xs 10355, .C,
   .xs 7619, .D, .xs 10387, .C,
   .xs 7555, .D, .xs 10515, .C,
   .xs 7299, .D, .xs 11027, .C,
   .xs 6275, .D, .xs 13075, .C,
   .xs 2179, .D, .D, .xs 7088, .C,
   .xs 1, .C, .xs 3849, .P]

/-- Coq `Fls_Fls`. -/
lemma Fls_Fls (n m : ℕ) (l : List Lsym) : Fls n (Fls m l) = Fls (n + m) l := by
  rcases Nat.eq_zero_or_pos m with rfl | hm
  · rfl
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · rw [Nat.zero_add]; rfl
  unfold Fls
  rw [if_neg hm.ne', if_neg hn.ne', if_neg (by omega : ¬ n + m = 0)]
  cases l with
  | nil => rfl
  | cons s l => cases s with
    | Fs k => simp only [Nat.add_assoc]
    | _ => rfl

/-- Coq `stride_correct`: apply `stride_correct'` at the natural level. -/
lemma stride_correct (t t' : List Rsym) (xs : ℕ) (l : ListBlank (Symbol 1))
    (H : stride xs 1 t = some t') :
    dR (blkPow xB xs ++ l) (liftRight t) -[M]->* dL l (liftRight t') :=
  stride_correct' (strideLevel t) t t' xs l rfl H

/-- Coq `stride_correct_0`: the `xs = 0` specialization. -/
lemma stride_correct_0 (t t' : List Rsym) (l : ListBlank (Symbol 1))
    (H : stride 0 1 t = some t') :
    dR l (liftRight t) -[M]->* dL l (liftRight t') := by
  have h := stride_correct t t' 0 l H
  simpa only [blkPow_zero, ListBlank.append_empty] using h

/-! ## The het layer: an executable simulator over `xs + k` counts

The Coq proof of `uni_cycle` is a `repeat apply_step` symbolic tactic
simulation threading the abstract count `xs` through het_add (`xs :+ k`).
Here the same trick is *executable*: counts are `HN` (`pure k` or `het k`
= `xs + k`), abstract tails are markers, and the whole 1,087-meta-step
universal cycle is a single decided certificate (`hetCertificate`), made
sound by substitution-commutation with the concrete layer. -/

/-- A count that is either concrete or `xs + k` for the ambient `xs`. -/
inductive HN
  | pure (k : ℕ)
  | het (k : ℕ)
  deriving DecidableEq, Repr

namespace HN

/-- Substitute the ambient count. -/
def subst (m : ℕ) : HN → ℕ
  | .pure k => k
  | .het k => m + k

/-- Addition; `het + het` (two ambient counts) is unrepresentable. -/
def add : HN → HN → Option HN
  | .pure a, .pure b => some (.pure (a + b))
  | .pure a, .het b => some (.het (a + b))
  | .het a, .pure b => some (.het (a + b))
  | .het _, .het _ => none

/-- Match `n+1`: predecessor, positive for every value of the ambient count. -/
def pos? : HN → Option HN
  | .pure (k + 1) => some (.pure k)
  | .het (k + 1) => some (.het k)
  | _ => none

/-- Guard `n ≤ v`: `some b` when decidable uniformly in the ambient count. -/
def le? (n : ℕ) : HN → Option Bool
  | .pure a => some (decide (n ≤ a))
  | .het a => if n ≤ a then some true else none

/-- `v - n` (meaningful under a `le? n v = some true` guard). -/
def sub : HN → ℕ → HN
  | .pure a, n => .pure (a - n)
  | .het a, n => .het (a - n)

@[simp] lemma subst_pure (m k : ℕ) : HN.subst m (.pure k) = k := rfl
@[simp] lemma subst_het (m k : ℕ) : HN.subst m (.het k) = m + k := rfl

lemma add_subst {a b c : HN} (h : add a b = some c) (m : ℕ) :
    c.subst m = a.subst m + b.subst m := by
  cases a <;> cases b <;>
    simp only [add, Option.some.injEq, reduceCtorEq] at h <;>
    (try cases h) <;> simp [subst] <;> omega

lemma pos?_subst {v n : HN} (h : pos? v = some n) (m : ℕ) :
    v.subst m = n.subst m + 1 := by
  cases v with
  | pure k => cases k with
    | zero => simp [pos?] at h
    | succ k => simp only [pos?, Option.some.injEq] at h; subst h; simp [subst]
  | het k => cases k with
    | zero => simp [pos?] at h
    | succ k => simp only [pos?, Option.some.injEq] at h; subst h; simp [subst]; omega

lemma le?_true {n : ℕ} {v : HN} (h : le? n v = some true) (m : ℕ) :
    n ≤ v.subst m := by
  cases v with
  | pure a => simp only [le?, Option.some.injEq, decide_eq_true_eq] at h; simpa [subst] using h
  | het a =>
    simp only [le?] at h
    split at h
    · rename_i ha; simp [subst]; omega
    · simp at h

lemma le?_false {n : ℕ} {v : HN} (h : le? n v = some false) (m : ℕ) :
    ¬ n ≤ v.subst m := by
  cases v with
  | pure a =>
    simp only [le?, Option.some.injEq] at h
    simp only [subst]
    exact of_decide_eq_false h
  | het a =>
    simp only [le?] at h
    split at h <;> simp at h

lemma sub_subst {n : ℕ} {v : HN} (h : le? n v = some true) (m : ℕ) :
    (v.sub n).subst m = v.subst m - n := by
  cases v with
  | pure a => simp [sub, subst]
  | het a =>
    simp only [le?] at h
    split at h
    · rename_i ha; simp [sub, subst]; omega
    · simp at h

end HN

/-- Left-tape symbols with het counts, plus the abstract-tail marker. -/
inductive HLsym
  | xs (n : HN) | D | P | C0 | C1 | C2 | C3
  | F0 | F1 | F2 | F3 | G0 | G1 | G2
  | Fs (n : HN) | Gs (n : HN) | Hs (n : HN)
  | tailL
  deriving DecidableEq, Repr

/-- Right-tape symbols with het counts, plus the abstract-tail marker. -/
inductive HRsym
  | xs (n : HN) | D | C | P | Gs (n : HN)
  | tailR
  deriving DecidableEq, Repr

/-- Substitute a het left tape: ambient count `m`, tail `lt`.  Counted symbols
are rebuilt with the *smart* constructors so the result is normalization-
insensitive. -/
def substL (m : ℕ) (lt : List Lsym) : List HLsym → List Lsym
  | [] => []
  | .xs v :: l => lxs (v.subst m) (substL m lt l)
  | .D :: l => .D :: substL m lt l
  | .P :: l => .P :: substL m lt l
  | .C0 :: l => .C0 :: substL m lt l
  | .C1 :: l => .C1 :: substL m lt l
  | .C2 :: l => .C2 :: substL m lt l
  | .C3 :: l => .C3 :: substL m lt l
  | .F0 :: l => .F0 :: substL m lt l
  | .F1 :: l => .F1 :: substL m lt l
  | .F2 :: l => .F2 :: substL m lt l
  | .F3 :: l => .F3 :: substL m lt l
  | .G0 :: l => .G0 :: substL m lt l
  | .G1 :: l => .G1 :: substL m lt l
  | .G2 :: l => .G2 :: substL m lt l
  | .Fs v :: l => Fls (v.subst m) (substL m lt l)
  | .Gs v :: l => Gls (v.subst m) (substL m lt l)
  | .Hs v :: l => Hls (v.subst m) (substL m lt l)
  | .tailL :: _ => lt

/-- Substitute a het right tape: ambient count `m`, tail `rt`. -/
def substR (m : ℕ) (rt : List Rsym) : List HRsym → List Rsym
  | [] => []
  | .xs v :: r => rxs (v.subst m) (substR m rt r)
  | .D :: r => .D :: substR m rt r
  | .C :: r => .C :: substR m rt r
  | .P :: r => .P :: substR m rt r
  | .Gs v :: r => Grs (v.subst m) (substR m rt r)
  | .tailR :: _ => rt

/-! ## Het smart constructors and their substitution lemmas -/

def lxsH : HN → List HLsym → Option (List HLsym)
  | .pure 0, l => some l
  | n, .xs v :: l => (n.add v).map (.xs · :: l)
  | n, l => some (.xs n :: l)

def rxsH : HN → List HRsym → Option (List HRsym)
  | .pure 0, r => some r
  | n, .xs v :: r => (n.add v).map (.xs · :: r)
  | n, r => some (.xs n :: r)

def FlsH : HN → List HLsym → Option (List HLsym)
  | .pure 0, l => some l
  | n, .Fs v :: l => (n.add v).map (.Fs · :: l)
  | n, l => some (.Fs n :: l)

def GlsH : HN → List HLsym → Option (List HLsym)
  | .pure 0, l => some l
  | n, .Gs v :: l => (n.add v).map (.Gs · :: l)
  | n, l => some (.Gs n :: l)

def GrsH : HN → List HRsym → Option (List HRsym)
  | .pure 0, r => some r
  | n, .Gs v :: r => (n.add v).map (.Gs · :: r)
  | n, r => some (.Gs n :: r)

def HlsH : HN → List HLsym → Option (List HLsym)
  | .pure 0, l => some l
  | n, .Hs v :: l => (n.add v).map (.Hs · :: l)
  | n, l => some (.Hs n :: l)

/-- Merge lemma for `lxs` (mirror of `rxs_rxs`). -/
lemma lxs_lxs (n m : ℕ) (t : List Lsym) : lxs n (lxs m t) = lxs (n + m) t := by
  rcases Nat.eq_zero_or_pos m with rfl | hm
  · rfl
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · rw [Nat.zero_add]; rfl
  unfold lxs
  rw [if_neg hm.ne', if_neg hn.ne', if_neg (by omega : ¬ n + m = 0)]
  cases t with
  | nil => rfl
  | cons s t => cases s with
    | xs k => simp only [Nat.add_assoc]
    | _ => rfl

/-- Merge lemma for `Gls`. -/
lemma Gls_Gls (n m : ℕ) (t : List Lsym) : Gls n (Gls m t) = Gls (n + m) t := by
  rcases Nat.eq_zero_or_pos m with rfl | hm
  · rfl
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · rw [Nat.zero_add]; rfl
  unfold Gls
  rw [if_neg hm.ne', if_neg hn.ne', if_neg (by omega : ¬ n + m = 0)]
  cases t with
  | nil => rfl
  | cons s t => cases s with
    | Gs k => simp only [Nat.add_assoc]
    | _ => rfl

/-- Merge lemma for `Hls`. -/
lemma Hls_Hls (n m : ℕ) (t : List Lsym) : Hls n (Hls m t) = Hls (n + m) t := by
  rcases Nat.eq_zero_or_pos m with rfl | hm
  · rfl
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · rw [Nat.zero_add]; rfl
  unfold Hls
  rw [if_neg hm.ne', if_neg hn.ne', if_neg (by omega : ¬ n + m = 0)]
  cases t with
  | nil => rfl
  | cons s t => cases s with
    | Hs k => simp only [Nat.add_assoc]
    | _ => rfl

section SubstCommutation

variable (m : ℕ) (lt : List Lsym) (rt : List Rsym)

lemma substR_rxsH {n : HN} {r r' : List HRsym} (h : rxsH n r = some r') :
    substR m rt r' = rxs (n.subst m) (substR m rt r) := by
  unfold rxsH at h
  split at h
  · -- pure-0 skip
    cases h; rfl
  · rw [Option.map_eq_some_iff] at h
    obtain ⟨s, hadd, rfl⟩ := h
    simp only [substR]
    rw [HN.add_subst hadd, ← rxs_rxs]
  · -- push
    cases h; rfl

lemma substL_lxsH {n : HN} {l l' : List HLsym} (h : lxsH n l = some l') :
    substL m lt l' = lxs (n.subst m) (substL m lt l) := by
  unfold lxsH at h
  split at h
  · cases h; rfl
  · rw [Option.map_eq_some_iff] at h
    obtain ⟨s, hadd, rfl⟩ := h
    simp only [substL]
    rw [HN.add_subst hadd, ← lxs_lxs]
  · cases h; rfl

lemma substL_FlsH {n : HN} {l l' : List HLsym} (h : FlsH n l = some l') :
    substL m lt l' = Fls (n.subst m) (substL m lt l) := by
  unfold FlsH at h
  split at h
  · cases h; rfl
  · rw [Option.map_eq_some_iff] at h
    obtain ⟨s, hadd, rfl⟩ := h
    simp only [substL]
    rw [HN.add_subst hadd, ← Fls_Fls]
  · cases h; rfl

lemma substL_GlsH {n : HN} {l l' : List HLsym} (h : GlsH n l = some l') :
    substL m lt l' = Gls (n.subst m) (substL m lt l) := by
  unfold GlsH at h
  split at h
  · cases h; rfl
  · rw [Option.map_eq_some_iff] at h
    obtain ⟨s, hadd, rfl⟩ := h
    simp only [substL]
    rw [HN.add_subst hadd, ← Gls_Gls]
  · cases h; rfl

lemma substR_GrsH {n : HN} {r r' : List HRsym} (h : GrsH n r = some r') :
    substR m rt r' = Grs (n.subst m) (substR m rt r) := by
  unfold GrsH at h
  split at h
  · cases h; rfl
  · rw [Option.map_eq_some_iff] at h
    obtain ⟨s, hadd, rfl⟩ := h
    simp only [substR]
    rw [HN.add_subst hadd, ← Grs_Grs]
  · cases h; rfl

lemma substL_HlsH {n : HN} {l l' : List HLsym} (h : HlsH n l = some l') :
    substL m lt l' = Hls (n.subst m) (substL m lt l) := by
  unfold HlsH at h
  split at h
  · cases h; rfl
  · rw [Option.map_eq_some_iff] at h
    obtain ⟨s, hadd, rfl⟩ := h
    simp only [substL]
    rw [HN.add_subst hadd, ← Hls_Hls]
  · cases h; rfl

end SubstCommutation

/-! ## Het stride

Mirror of `stride`, threading a het accumulator.  At the tail marker the
pending multi-count `n` is deferred to the abstract stride budget: the pair's
second component reports how many abstract strides the walk consumed. -/

def strideH : HN → ℕ → List HRsym → Option (List HRsym × ℕ)
  | _, _, [] => none
  | acc, n, .tailR :: t =>
    match t with
    | [] => (rxsH acc [.tailR]).map fun r => (r, n)
    | _ :: _ => none
  | acc, _, .P :: t =>
    match t with
    | [] => (rxsH acc [.P]).map fun r => (r, 0)
    | _ :: _ => none
  | acc, n, .xs v :: t => (acc.add v).bind fun acc' => strideH acc' n t
  | acc, n, .D :: t =>
      (strideH (.pure 0) n t).bind fun (t, d) =>
        (rxsH acc (.D :: t)).map fun t => (t, d)
  | acc, n, .C :: t =>
      match HN.le? n acc with
      | some true =>
          (strideH (.pure 0) (4 * n) t).bind fun (t, d) =>
            (rxsH (.pure (2 * n)) t).bind fun t =>
              (rxsH (acc.sub n) (.C :: t)).map fun t => (t, d)
      | _ => none
  | acc, n, .Gs v :: t =>
      (strideH (.pure 0) n t).bind fun (t, d) =>
        (GrsH v t).bind fun t =>
          (rxsH acc t).map fun t => (t, d)

/-- Substitution commutes with the het stride: a successful `strideH` walk
consuming `d` abstract strides matches a concrete `stride`, provided the
abstract tail indeed strides `d` times. -/
lemma strideH_subst (m : ℕ) {rt rt' : List Rsym} {t : List HRsym} :
    ∀ {acc : HN} {n : ℕ} {res : List HRsym} {d : ℕ},
      strideH acc n t = some (res, d) → 1 ≤ n →
      (1 ≤ d → stride 0 d rt = some rt') →
      stride (acc.subst m) n (substR m rt t) = some (substR m rt' res) := by
  induction t with
  | nil => intro acc n res d h _ _; simp [strideH] at h
  | cons s t IH =>
    intro acc n res d h hn hrt
    cases s with
    | tailR =>
      cases t with
      | cons _ _ => simp [strideH] at h
      | nil =>
        simp only [strideH, Option.map_eq_some_iff] at h
        obtain ⟨r1, hr1, heq⟩ := h
        injection heq with h1 h2
        subst h1; subst h2
        rw [substR_rxsH m rt' hr1]
        simp only [substR]
        simpa using stride_more rt rt' (acc.subst m) 0 n (hrt hn)
    | P =>
      cases t with
      | cons _ _ => simp [strideH] at h
      | nil =>
        simp only [strideH, Option.map_eq_some_iff] at h
        obtain ⟨r1, hr1, heq⟩ := h
        injection heq with h1 h2
        subst h1
        rw [substR_rxsH m rt' hr1]
        simp only [substR]
        rfl
    | xs v =>
      simp only [strideH] at h
      cases hadd : acc.add v with
      | none => rw [hadd] at h; simp at h
      | some acc' =>
        rw [hadd] at h
        simp only [Option.bind_some] at h
        rw [substR, stride_rxs, ← HN.add_subst hadd]
        exact IH h hn hrt
    | D =>
      simp only [strideH] at h
      cases hs : strideH (.pure 0) n t with
      | none => rw [hs] at h; simp at h
      | some p =>
        obtain ⟨t1, d1⟩ := p
        rw [hs] at h
        simp only [Option.bind_some, Option.map_eq_some_iff] at h
        obtain ⟨t2, ht2, heq⟩ := h
        cases heq
        have inner := IH hs hn hrt
        simp only [HN.subst] at inner
        rw [substR]
        simp only [stride, inner]
        rw [substR_rxsH m rt' ht2]
        simp only [substR]
    | C =>
      simp only [strideH] at h
      cases hle : HN.le? n acc with
      | none => rw [hle] at h; simp at h
      | some b =>
        cases b with
        | false => rw [hle] at h; simp at h
        | true =>
          rw [hle] at h
          cases hs : strideH (.pure 0) (4 * n) t with
          | none => rw [hs] at h; simp at h
          | some p =>
            obtain ⟨t1, d1⟩ := p
            rw [hs] at h
            simp only [Option.bind_some] at h
            cases h2 : rxsH (.pure (2 * n)) t1 with
            | none => rw [h2] at h; simp at h
            | some t2 =>
              rw [h2] at h
              simp only [Option.bind_some, Option.map_eq_some_iff] at h
              obtain ⟨t3, ht3, heq⟩ := h
              cases heq
              have inner := IH hs (by omega) hrt
              simp only [HN.subst] at inner
              rw [substR]
              simp only [stride, if_pos (HN.le?_true hle m), inner]
              rw [substR_rxsH m rt' ht3, HN.sub_subst hle]
              simp only [substR]
              rw [substR_rxsH m rt' h2]
              simp only [HN.subst]
    | Gs v =>
      simp only [strideH] at h
      cases hs : strideH (.pure 0) n t with
      | none => rw [hs] at h; simp at h
      | some p =>
        obtain ⟨t1, d1⟩ := p
        rw [hs] at h
        simp only [Option.bind_some] at h
        cases h2 : GrsH v t1 with
        | none => rw [h2] at h; simp at h
        | some t2 =>
          rw [h2] at h
          simp only [Option.bind_some, Option.map_eq_some_iff] at h
          obtain ⟨t3, ht3, heq⟩ := h
          cases heq
          have inner := IH hs hn hrt
          simp only [HN.subst] at inner
          rw [substR, stride_Grs _ _ _ _ _ inner, substR_rxsH m rt' ht3,
            substR_GrsH m rt' h2]

/-! ## Het simple step -/

/-- Mirror of `unrxs` (peel one `x` off the right tape). -/
def unrxsH (r : List HRsym) : Option (List HRsym) :=
  match r with
  | .xs v :: r => v.pos?.bind fun n => rxsH n r
  | .Gs v :: r => v.pos?.bind fun n =>
      (GrsH n r).map fun t =>
        .xs (.pure 299) :: .D :: .xs (.pure 30826) :: .D :: .xs (.pure 72142) :: .D ::
          .xs (.pure 3076) :: .D :: .xs (.pure 1538) :: .D :: t
  | _ => none

/-- Mirror of `unrxs_spec` through substitution. -/
lemma unrxsH_spec {r r' : List HRsym} (h : unrxsH r = some r') (m : ℕ) (rt : List Rsym) :
    liftRight (substR m rt r) = xB ++ liftRight (substR m rt r') := by
  unfold unrxsH at h
  split at h
  · -- `.xs v :: r₀`
    rename_i v r0
    rw [Option.bind_eq_some_iff] at h
    obtain ⟨n, hn, hx⟩ := h
    rw [substR, substR_rxsH m rt hx, lift_rxs, lift_rxs, HN.pos?_subst hn m,
      blkPow_succ, ListBlank.append_assoc']
  · -- `.Gs v :: r₀`
    rename_i v r0
    rw [Option.bind_eq_some_iff] at h
    obtain ⟨n, hn, hx⟩ := h
    rw [Option.map_eq_some_iff] at hx
    obtain ⟨t, ht, rfl⟩ := hx
    simp only [substR, HN.subst_pure]
    rw [substR_GrsH m rt ht]
    rw [lift_Grs, HN.pos?_subst hn m, blkPow_succ]
    simp only [lift_rxs, liftRight, Rsym.block, lift_Grs]
    rw [GrB, show blkPow xB 300 = xB ++ blkPow xB 299 from blkPow_succ xB 299]
    simp only [List.append_assoc, ListBlank.append_assoc']
  · exact absurd h (by simp)

/-- A het configuration: direction plus both het tape sides. -/
structure HConf where
  dir : Dir
  left : List HLsym
  right : List HRsym
  deriving DecidableEq, Repr

/-- Substitute a het configuration. -/
def HConf.subst (m : ℕ) (lt : List Lsym) (rt : List Rsym) : HConf → SConf
  | ⟨d, l, r⟩ => ⟨d, substL m lt l, substR m rt r⟩

/-- Mirror of `simpleStep`.  Rows that would touch a tail marker are `none`. -/
def simpleStepH : HConf → Option HConf
  | ⟨.right, l, r⟩ =>
    match r with
    | [] =>
      match l with
      | .xs v :: l =>
          v.pos?.bind fun n => (lxsH n l).map fun l =>
            ⟨.left, l, [.C, .xs (.pure 1), .P]⟩
      | .D :: l => some ⟨.left, l, [.xs (.pure 1)]⟩
      | _ => none
    | .xs v :: r => (lxsH v l).map fun l => ⟨.right, l, r⟩
    | .D :: r => some ⟨.right, .D :: l, r⟩
    | .C :: r =>
      match l with
      | .xs v :: l =>
          v.pos?.bind fun n => (lxsH n l).map fun l => ⟨.right, .C0 :: l, r⟩
      | .D :: l => some ⟨.right, .xs (.pure 1) :: .P :: l, r⟩
      | .C0 :: l => some ⟨.right, .G0 :: l, r⟩
      | .C2 :: l => some ⟨.right, .F0 :: l, r⟩
      | _ => none
    | [.P] => some ⟨.left, l, [.P]⟩
    | .P :: .xs v :: r => (lxsH v l).map fun l => ⟨.right, l, .P :: r⟩
    | .P :: .D :: .xs v :: r =>
        v.pos?.bind fun n => (rxsH n r).map fun r =>
          ⟨.right, .D :: .C1 :: l, .P :: r⟩
    | .P :: .D :: .D :: r =>
        (unrxsH r).map fun r => ⟨.right, .D :: .C1 :: .C2 :: l, r⟩
    | .P :: .D :: .C :: r =>
        (unrxsH r).map fun r => ⟨.right, .D :: .G1 :: l, .P :: r⟩
    | .P :: .D :: .P :: r => some ⟨.right, .D :: .C1 :: l, r⟩
    | .P :: .D :: .Gs v :: r =>
        (HlsH v l).map fun l => ⟨.right, l, .P :: .D :: r⟩
    | .P :: .C :: r =>
        (unrxsH r).map fun r => ⟨.left, l, .P :: .D :: .P :: r⟩
    | .P :: .P :: r => (lxsH (.pure 1) l).map fun l => ⟨.right, l, r⟩
    | .Gs v :: r => (GlsH v l).map fun l => ⟨.right, l, r⟩
    | _ => none
  | ⟨.left, l, r⟩ =>
    match l with
    | [] =>
      match r with
      | .C :: r => (unrxsH r).map fun r => ⟨.right, [.D, .C1], .P :: r⟩
      | _ => none
    | .xs v :: l => (rxsH v r).map fun r => ⟨.left, l, r⟩
    | .D :: l => some ⟨.left, l, .D :: r⟩
    | .P :: l => some ⟨.left, l, .P :: r⟩
    | .C0 :: l => some ⟨.right, .xs (.pure 1) :: .C1 :: l, r⟩
    | .C1 :: l => some ⟨.right, .C2 :: l, r⟩
    | .C2 :: l => some ⟨.right, .xs (.pure 1) :: .C3 :: l, r⟩
    | .C3 :: l => some ⟨.left, l, .C :: r⟩
    | .F0 :: l => some ⟨.right, .xs (.pure 1) :: .F1 :: l, r⟩
    | .F1 :: l => some ⟨.right, .F2 :: l, r⟩
    | .F2 :: l => some ⟨.right, .xs (.pure 1) :: .F3 :: l, r⟩
    | .F3 :: .xs v :: l =>
        v.pos?.bind fun n => (lxsH n l).map fun l =>
          ⟨.right, .D :: .C1 :: .P :: l, r⟩
    | .G0 :: l => some ⟨.right, .xs (.pure 1) :: .G1 :: l, r⟩
    | .G1 :: l => some ⟨.right, .G2 :: l, r⟩
    | .G2 :: l => some ⟨.right, .xs (.pure 1) :: .D :: .P :: l, r⟩
    | .Gs v :: l => (GrsH v r).map fun r => ⟨.left, l, r⟩
    | _ => none

/-- Unfold substitution and lift down to `blkPow`-append form. -/
local macro "hetLiftSimp" : tactic => `(tactic|
  simp only [HConf.subst, SConf.lift, substL, substR, liftLeft, liftRight,
    Lsym.block, Rsym.block, HN.subst_pure, HN.subst_het,
    lift_lxs, lift_rxs, lift_Fls, lift_Gls, lift_Grs, lift_Hls,
    blkPow_succ, blkPow_zero, blkPow_one, List.append_nil])

/-- Normalize the rewritten goal and dispatch the matching shift rule. -/
local macro "hetDispatch" : tactic => `(tactic|
  (try simp only [lift_lxs, lift_rxs, lift_Fls, lift_Gls, lift_Grs, lift_Hls,
     HN.subst_pure, HN.subst_het, blkPow_zero, blkPow_one, List.append_nil]
   try simp only [List.append_assoc, ListBlank.append_assoc']
   first
   | (with_reducible first
    | exact rule_x_left _ _        | exact rule_D_left _ _        | exact rule_C_left _ _
    | exact rule_x_right _ _       | exact rule_D_right _ _       | exact rule_C30 _ _
    | exact rule_C01 _ _           | exact rule_C12 _ _           | exact rule_C23 _ _
    | exact rule_DC _ _            | exact rule_C2_C _ _          | exact rule_F0 _ _
    | exact rule_F1 _ _            | exact rule_F2 _ _            | exact rule_F3 _ _
    | exact rule_C03 _ _           | exact rule_G0 _ _            | exact rule_G1 _ _
    | exact rule_G2 _ _            | exact rule_P_left _ _        | exact rule_P_P _ _
    | exact rule_P_x _ _           | exact rule_P_Dx _ _          | exact rule_P_Cx _ _
    | exact rule_P_DP _ _          | exact rule_P_DDx _ _         | exact rule_P_DCx _ _
    | exact rule_xR _              | exact rule_DR _              | exact rule_L _
    | exact rule_P_R _             | exact rule_xn_left _ _ _     | exact rule_xn_right _ _ _
    | exact rule_P_xn _ _ _        | exact rule_Gn_left _ _ _     | exact rule_Gn_right _ _ _
    | exact rule_P_DGn _ _ _
    | exact rule_xR' _ _           | exact rule_C30' _ _ _
    | exact rule_P_Dx' _ _ _       | exact rule_F3' _ _ _)
   | (simp only [← List.append_assoc, ← ListBlank.append_assoc']
      with_reducible first
       | exact rule_x_left _ _        | exact rule_D_left _ _        | exact rule_C_left _ _
       | exact rule_x_right _ _       | exact rule_D_right _ _       | exact rule_C30 _ _
       | exact rule_C01 _ _           | exact rule_C12 _ _           | exact rule_C23 _ _
       | exact rule_DC _ _            | exact rule_C2_C _ _          | exact rule_F0 _ _
       | exact rule_F1 _ _            | exact rule_F2 _ _            | exact rule_F3 _ _
       | exact rule_C03 _ _           | exact rule_G0 _ _            | exact rule_G1 _ _
       | exact rule_G2 _ _            | exact rule_P_left _ _        | exact rule_P_P _ _
       | exact rule_P_x _ _           | exact rule_P_Dx _ _          | exact rule_P_Cx _ _
       | exact rule_P_DP _ _          | exact rule_P_DDx _ _         | exact rule_P_DCx _ _
       | exact rule_xR _              | exact rule_DR _              | exact rule_L _
       | exact rule_P_R _             | exact rule_xn_left _ _ _     | exact rule_xn_right _ _ _
       | exact rule_P_xn _ _ _        | exact rule_Gn_left _ _ _     | exact rule_Gn_right _ _ _
       | exact rule_P_DGn _ _ _
       | exact rule_xR' _ _           | exact rule_C30' _ _ _
       | exact rule_P_Dx' _ _ _       | exact rule_F3' _ _ _)))

set_option maxHeartbeats 1000000 in
/-- The lift-level soundness of one het simple step (mirror of
`simple_step_spec` through substitution). -/
lemma simpleStepH_sound {c c' : HConf} (h : simpleStepH c = some c')
    (m : ℕ) (lt : List Lsym) (rt : List Rsym) :
    (c.subst m lt rt).lift -[M]->* (c'.subst m lt rt).lift := by
  obtain ⟨dir, l, r⟩ := c
  cases dir <;>
  · simp only [simpleStepH] at h
    repeat' split at h
    all_goals first
      | (injection h with h; subst h; hetLiftSimp; hetDispatch)
      | (rw [Option.map_eq_some_iff] at h; obtain ⟨w, hw, h⟩ := h; subst h;
         hetLiftSimp
         try rw [substL_lxsH _ _ hw]
         try rw [substR_rxsH _ _ hw]
         try rw [substL_FlsH _ _ hw]
         try rw [substL_GlsH _ _ hw]
         try rw [substR_GrsH _ _ hw]
         try rw [substL_HlsH _ _ hw]
         try rw [unrxsH_spec hw _ _]
         hetDispatch)
      | (rw [Option.bind_eq_some_iff] at h; obtain ⟨n, hn, h⟩ := h;
         rw [Option.map_eq_some_iff] at h; obtain ⟨w, hw, h⟩ := h; subst h;
         hetLiftSimp
         try rw [substL_lxsH _ _ hw]
         try rw [substR_rxsH _ _ hw]
         try rw [HN.pos?_subst hn _]
         hetDispatch)
      | simp at h

/-! ## Het meta-step, iterated run, and soundness -/

/-- Try a full stride from a rightward config (mirror of `tryStride`);
returns the abstract strides consumed. -/
def tryStrideH (c : HConf) : Option (HConf × ℕ) :=
  match c with
  | ⟨.left, _, _⟩ => none
  | ⟨.right, l, r⟩ => (strideH (.pure 0) 1 r).map fun (r, d) => (⟨.left, l, r⟩, d)

/-- One het meta-step: stride if possible, else a simple step. -/
def stepH (c : HConf) : Option (HConf × ℕ) :=
  match tryStrideH c with
  | some cd => some cd
  | none => (simpleStepH c).map fun c => (c, 0)

/-- Iterate `stepH`, accumulating consumed strides. -/
def hetSteps : ℕ → HConf → Option (HConf × ℕ)
  | 0, c => some (c, 0)
  | n + 1, c =>
    (stepH c).bind fun (c', d) =>
      (hetSteps n c').map fun (c'', d') => (c'', d + d')

/-- Soundness of one het meta-step: a stride step (`1 ≤ d`) advances the
abstract tape by `d` strides; a simple step (`d = 0`) leaves it unchanged. -/
lemma stepH_sound {c c' : HConf} {d : ℕ} (h : stepH c = some (c', d))
    (m : ℕ) (lt : List Lsym) {rt rt' : List Rsym}
    (hrt0 : d = 0 → rt' = rt) (hrt1 : 1 ≤ d → stride 0 d rt = some rt') :
    (c.subst m lt rt).lift -[M]->* (c'.subst m lt rt').lift := by
  simp only [stepH] at h
  cases he : tryStrideH c with
  | some cd =>
    rw [he] at h
    injection h with h; subst h
    obtain ⟨dir, l, r⟩ := c
    cases dir with
    | left => simp [tryStrideH] at he
    | right =>
      simp only [tryStrideH, Option.map_eq_some_iff] at he
      obtain ⟨⟨res, d0⟩, hst, heq⟩ := he
      injection heq with h1 h2
      subst h1; subst h2
      have key := strideH_subst m (t := r) hst le_rfl hrt1
      simp only [HN.subst_pure] at key
      simp only [HConf.subst, SConf.lift]
      exact stride_correct_0 _ _ _ key
  | none =>
    rw [he] at h
    rw [Option.map_eq_some_iff] at h
    obtain ⟨c0, hc0, heq⟩ := h
    injection heq with h1 h2
    subst h1
    rw [hrt0 h2.symm]
    exact simpleStepH_sound hc0 m lt rt

/-- Soundness of the iterated het run: `dtot` consumed strides advance the
abstract tape by `dtot` strides (or leave it unchanged when `dtot = 0`). -/
lemma hetSteps_sound (n : ℕ) {c c' : HConf} {dtot : ℕ}
    (h : hetSteps n c = some (c', dtot)) (m : ℕ) (lt : List Lsym)
    {rt rt' : List Rsym}
    (hrt0 : dtot = 0 → rt' = rt) (hrt1 : 1 ≤ dtot → stride 0 dtot rt = some rt') :
    (c.subst m lt rt).lift -[M]->* (c'.subst m lt rt').lift := by
  induction n generalizing c dtot rt with
  | zero =>
    simp only [hetSteps, Option.some.injEq] at h
    injection h with h1 h2
    subst h1
    rw [hrt0 h2.symm]
    exact Machine.EvStep.refl
  | succ n IH =>
    simp only [hetSteps] at h
    rw [Option.bind_eq_some_iff] at h
    obtain ⟨⟨c1, d⟩, he, h⟩ := h
    rw [Option.map_eq_some_iff] at h
    obtain ⟨⟨c2, d'⟩, hrest, heq⟩ := h
    injection heq with h1 h2
    subst h1; subst h2
    rcases Nat.eq_zero_or_pos d with hd | hd
    · -- simple step: tape family unchanged at this step
      subst hd
      rcases Nat.eq_zero_or_pos d' with hd' | hd'
      · subst hd'
        have hrteq := hrt0 rfl
        subst hrteq
        exact (stepH_sound he m lt (fun _ => rfl) (fun hk => by omega)).trans
          (IH hrest (fun _ => rfl) (fun hk => by omega))
      · refine (stepH_sound he m lt (fun _ => rfl) (fun hk => by omega)).trans ?_
        exact IH hrest (fun h0 => by omega) (fun _ => by simpa using hrt1 (by omega))
    · rcases Nat.eq_zero_or_pos d' with hd' | hd'
      · -- final stride: the whole remaining budget is consumed here
        subst hd'
        have hstr : stride 0 d rt = some rt' := by simpa using hrt1 (by omega)
        refine (stepH_sound he m lt (fun h0 => by omega) (fun _ => hstr)).trans ?_
        exact IH hrest (fun _ => rfl) (fun hk => by omega)
      · -- middle stride: split the budget via stride_add
        have hstr : stride 0 (d + d') rt = some rt' := hrt1 (by omega)
        obtain ⟨rmid, hsplit1, hsplit2⟩ := stride_add rt rt' 0 d d' hstr
        refine (stepH_sound he m lt (fun h0 => by omega) (fun _ => hsplit1)).trans ?_
        exact IH hrest (fun h0 => by omega) (fun _ => hsplit2)

/-! ## The `uni_cycle` certificate -/

/-- Embed a concrete left symbol. -/
def ofL : Lsym → HLsym
  | .xs n => .xs (.pure n) | .D => .D | .P => .P
  | .C0 => .C0 | .C1 => .C1 | .C2 => .C2 | .C3 => .C3
  | .F0 => .F0 | .F1 => .F1 | .F2 => .F2 | .F3 => .F3
  | .G0 => .G0 | .G1 => .G1 | .G2 => .G2
  | .Fs n => .Fs (.pure n) | .Gs n => .Gs (.pure n) | .Hs n => .Hs (.pure n)

/-- `Jconst` as a het tape segment. -/
def JH : List HLsym := Jconst.map ofL

/-- The `uni_cycle` LHS as a het configuration. -/
def startHet : HConf :=
  ⟨.right, .D :: .C1 :: .xs (.het (uni_P + 1)) :: JH ++ [.tailL], [.tailR]⟩

/-- The `uni_cycle` RHS as a het configuration (the raw shape the run
reaches: `J` followed by the spelled-out `Fl` block, `Gr` block spelled out
on the right). -/
def endHet : HConf :=
  ⟨.right,
    .D :: .C1 :: .xs (.het 1) :: JH ++
      [.xs (.pure 10344), .D, .xs (.pure 7640), .C2, .tailL],
    [.xs (.pure 300), .D, .xs (.pure 30826), .D, .xs (.pure 72142), .D,
      .xs (.pure 3076), .D, .xs (.pure 1538), .D, .tailR]⟩

set_option maxRecDepth 100000 in
/-- The decided universal-cycle certificate: 1,087 het meta-steps from the
LHS shape reach the RHS shape, consuming exactly `uni_T` abstract strides. -/
lemma hetCertificate : hetSteps 1087 startHet = some (endHet, uni_T) := by
  decide +kernel

/-- Substituting the start configuration. -/
lemma substL_start (m : ℕ) (lt : List Lsym) :
    substL m lt startHet.left =
      .D :: .C1 :: .xs (m + (uni_P + 1)) :: Jconst ++ lt := by
  show .D :: .C1 :: lxs (HN.subst m (.het (uni_P + 1))) (substL m lt (JH ++ [.tailL])) = _
  have hJ : substL m lt (JH ++ [.tailL]) = Jconst ++ lt := rfl
  rw [hJ, HN.subst_het]
  refine congrArg _ (congrArg _ ?_)
  show lxs (m + (uni_P + 1)) (Jconst ++ lt) = .xs (m + (uni_P + 1)) :: Jconst ++ lt
  unfold lxs
  rw [if_neg (by unfold uni_P; omega)]
  rfl

/-- Substituting the end configuration's left tape. -/
lemma substL_end (m : ℕ) (lt : List Lsym) :
    substL m lt endHet.left =
      .D :: .C1 :: .xs (m + 1) :: Jconst ++
        ([.xs 10344, .D, .xs 7640, .C2] ++ lt) := by
  show .D :: .C1 :: lxs (HN.subst m (.het 1)) (substL m lt (JH ++ _)) = _
  have hrest : substL m lt (JH ++
      [.xs (.pure 10344), .D, .xs (.pure 7640), .C2, .tailL]) =
      Jconst ++ ([.xs 10344, .D, .xs 7640, .C2] ++ lt) := rfl
  rw [hrest, HN.subst_het]
  refine congrArg _ (congrArg _ ?_)
  show lxs (m + 1) (Jconst ++ ([.xs 10344, .D, .xs 7640, .C2] ++ lt)) =
    .xs (m + 1) :: Jconst ++ ([.xs 10344, .D, .xs 7640, .C2] ++ lt)
  unfold lxs
  rw [if_neg (by omega)]
  rfl

/-- Lift congruence through a common prefix. -/
lemma liftLeft_congr_append (a : List Lsym) {x y : List Lsym}
    (h : liftLeft x = liftLeft y) : liftLeft (a ++ x) = liftLeft (a ++ y) := by
  induction a with
  | nil => exact h
  | cons s t IH => simp only [List.cons_append, liftLeft, IH]

/-- The end configuration's left tape lifts to the `Fls 1` form. -/
lemma lift_end_left (m : ℕ) (lt : List Lsym) :
    liftLeft (substL m lt endHet.left) =
      liftLeft (.D :: .C1 :: .xs (m + 1) :: Jconst ++ Fls 1 lt) := by
  rw [substL_end]
  simp only [liftLeft, List.cons_append]
  refine congrArg _ (congrArg _ (congrArg _ ?_))
  refine liftLeft_congr_append Jconst ?_
  rw [lift_Fls, blkPow_one]
  simp only [liftLeft, Lsym.block, FlB, List.append_assoc, List.nil_append,
    ListBlank.append_assoc']

/-- The end configuration's right tape lifts to the `Grs 1` form. -/
lemma lift_end_right (m : ℕ) (rt : List Rsym) :
    liftRight (substR m rt endHet.right) = liftRight (Grs 1 rt) := by
  show liftRight (rxs 300 (.D :: rxs 30826 (.D :: rxs 72142 (.D :: rxs 3076
    (.D :: rxs 1538 (.D :: rt)))))) = _
  rw [lift_Grs, blkPow_one, GrB]
  simp only [lift_rxs, liftRight, Rsym.block, List.append_assoc,
    ListBlank.append_assoc']

/-- The universal cycle, proven from the decided het certificate
(dev-file version of Coq `uni_cycle`). -/
lemma uni_cycle_het (l : List Lsym) (r r' : List Rsym) (xs : ℕ)
    (H : stride 0 uni_T r = some r') :
    dR (liftLeft (.D :: .C1 :: .xs (xs + (uni_P + 1)) :: Jconst ++ l)) (liftRight r)
      -[M]->*
    dR (liftLeft (.D :: .C1 :: .xs (xs + 1) :: Jconst ++ Fls 1 l))
      (liftRight (Grs 1 r')) := by
  have run := hetSteps_sound 1087 hetCertificate xs l
    (rt := r) (rt' := r')
    (fun h0 => absurd h0 (by unfold uni_T uni_P; omega))
    (fun _ => H)
  simp only [HConf.subst, SConf.lift] at run
  rw [substL_start] at run
  calc dR (liftLeft (.D :: .C1 :: .xs (xs + (uni_P + 1)) :: Jconst ++ l)) (liftRight r)
      = dR (liftLeft (.D :: .C1 :: .xs (xs + (uni_P + 1)) :: Jconst ++ l))
          (liftRight (substR xs r startHet.right)) := rfl
    _ -[M]->* dR (liftLeft (substL xs l endHet.left))
          (liftRight (substR xs r' endHet.right)) := run
    _ = dR (liftLeft (.D :: .C1 :: .xs (xs + 1) :: Jconst ++ Fls 1 l))
          (liftRight (Grs 1 r')) := by
        rw [lift_end_left, lift_end_right]

/-- Coq `uni_cycle` (merged with `uni_cycle'`: stated in the `Fls 1`/`Grs 1`
form so `uni_cycles` inducts directly).  One universal cycle consumes `uni_P`
of the leading `x`-run, appends one `Fl` block on the left and one `Gr` block on
the right, and applies a `uni_T`-stride to the right tape.  Proven via the
decided het-simulator certificate. -/
lemma uni_cycle (l : List Lsym) (r r' : List Rsym) (xs : ℕ)
    (H : stride 0 uni_T r = some r') :
    dR (liftLeft (.D :: .C1 :: .xs (xs + (uni_P + 1)) :: Jconst ++ l)) (liftRight r) -[M]->*
      dR (liftLeft (.D :: .C1 :: .xs (xs + 1) :: Jconst ++ Fls 1 l))
        (liftRight (Grs 1 r')) :=
  uni_cycle_het l r r' xs H

/-- Coq `uni_cycles`: `n+1` iterated universal cycles. -/
lemma uni_cycles (n : ℕ) (xs : ℕ) (l : List Lsym) (r r' : List Rsym)
    (H : stride 0 ((n + 1) * uni_T) r = some r') :
    dR (liftLeft (.D :: .C1 :: .xs (xs + ((n + 1) * uni_P + 1)) :: Jconst ++ l)) (liftRight r)
      -[M]->*
      dR (liftLeft (.D :: .C1 :: .xs (xs + 1) :: Jconst ++ Fls (n + 1) l))
        (liftRight (Grs (n + 1) r')) := by
  induction n generalizing xs l r r' with
  | zero => simpa using uni_cycle l r r' xs (by simpa using H)
  | succ n IH =>
    rw [show (n + 1 + 1) * uni_T = (n + 1) * uni_T + uni_T from Nat.succ_mul (n + 1) uni_T] at H
    obtain ⟨t1, H1, H2⟩ := stride_add r r' 0 ((n + 1) * uni_T) uni_T H
    rw [show xs + ((n + 1 + 1) * uni_P + 1) = (xs + uni_P) + ((n + 1) * uni_P + 1) from by
      rw [Nat.succ_mul (n + 1) uni_P]; omega]
    refine (IH (xs + uni_P) l r t1 H1).trans ?_
    rw [show xs + uni_P + 1 = xs + (uni_P + 1) from by omega]
    have Hstr : stride 0 uni_T (Grs (n + 1) t1) = some (Grs (n + 1) r') := by
      have h := stride_Grs t1 r' 0 (n + 1) uni_T H2
      exact h
    refine (uni_cycle (Fls (n + 1) l) (Grs (n + 1) t1) (Grs (n + 1) r') xs Hstr).trans ?_
    rw [Fls_Fls, Grs_Grs, show 1 + (n + 1) = n + 1 + 1 from by omega]
    exact Machine.EvStep.refl

/-- Coq `try_stride`: from a rightward config, accelerate by one full stride. -/
def tryStride (c : SConf) : Option SConf :=
  match c with
  | ⟨.left, _, _⟩ => none
  | ⟨.right, l, r⟩ => (stride 0 1 r).map (fun r' => ⟨.left, l, r'⟩)

/-- Coq `step`: try a stride, else fall back to one `simpleStep`. -/
def step (c : SConf) : Option SConf :=
  match tryStride c with
  | some c' => some c'
  | none => simpleStep c

/-- Coq `try_stride_spec`. -/
lemma tryStride_spec {c c' : SConf} (h : tryStride c = some c') :
    c.lift -[M]->* c'.lift := by
  obtain ⟨d, l, r⟩ := c
  cases d with
  | left => simp [tryStride] at h
  | right =>
    simp only [tryStride] at h
    cases hr : stride 0 1 r with
    | none => rw [hr] at h; simp at h
    | some r' =>
      rw [hr] at h
      simp only [Option.map_some, Option.some.injEq] at h
      subst h
      simp only [SConf.lift]
      exact stride_correct_0 r r' (liftLeft l) hr

/-- Coq `step_spec`. -/
lemma step_spec {c c' : SConf} (h : step c = some c') :
    c.lift -[M]->* c'.lift := by
  simp only [step] at h
  cases he : tryStride c with
  | some c0 => rw [he] at h; simp only [Option.some.injEq] at h; subst h; exact tryStride_spec he
  | none => rw [he] at h; exact simple_step_spec h

/-- Coq `uni_cycle_count`: how many universal cycles can safely be applied. -/
def uniCycleCount (xs : ℕ) (r : List Rsym) : ℕ :=
  let xsLimit := (xs - 1) / uni_P
  if xsLimit = 0 then 0
  else match maxStride 0 r with
    | some strides => min xsLimit (strides / uni_T)
    | none => xsLimit

/-- If the count is positive, `(n+1)·uni_P < xs` (Coq `uni_cycle_count_spec`). -/
lemma uniCycleCount_lt (xs : ℕ) (r : List Rsym) (n : ℕ)
    (h : uniCycleCount xs r = n + 1) : (n + 1) * uni_P < xs := by
  have hup : 0 < uni_P := by unfold uni_P; omega
  simp only [uniCycleCount] at h
  split at h
  · omega
  · have hle : n + 1 ≤ (xs - 1) / uni_P := by split at h <;> omega
    have hdvd : (xs - 1) / uni_P * uni_P ≤ xs - 1 := Nat.div_mul_le_self (xs - 1) uni_P
    have hpos : 0 < (n + 1) * uni_P := Nat.mul_pos (Nat.succ_pos n) hup
    have hchain : (n + 1) * uni_P ≤ xs - 1 :=
      le_trans (Nat.mul_le_mul_right uni_P hle) hdvd
    omega

/-- Coq `strip_prefix'`. -/
def stripPrefix [DecidableEq α] : List α → List α → Option (List α)
  | [], ys => some ys
  | _ :: _, [] => none
  | x :: xt, y :: yt => if x = y then stripPrefix xt yt else none

/-- Coq `strip_prefix'_spec`. -/
lemma stripPrefix_spec [DecidableEq α] (xs ys zs : List α)
    (h : stripPrefix xs ys = some zs) : ys = xs ++ zs := by
  induction xs generalizing ys with
  | nil => simp only [stripPrefix, Option.some.injEq] at h; subst h; rfl
  | cons x xt IH =>
    cases ys with
    | nil => simp [stripPrefix] at h
    | cons y yt =>
      simp only [stripPrefix] at h
      split at h
      · rename_i hxy; subst hxy
        rw [IH yt h]; rfl
      · simp at h

/-- Coq `try_uni_cycle`: apply as many universal cycles as safe. -/
def tryUniCycle (c : SConf) : Option SConf :=
  match c with
  | ⟨.right, .D :: .C1 :: .xs xs :: l, r⟩ =>
    match stripPrefix Jconst l with
    | some l =>
      match uniCycleCount xs r with
      | 0 => none
      | n + 1 =>
        match stride 0 ((n + 1) * uni_T) r with
        | some r' =>
          some ⟨.right, .D :: .C1 :: .xs (xs - (n + 1) * uni_P) :: Jconst ++ Fls (n + 1) l,
            Grs (n + 1) r'⟩
        | none => none
    | none => none
  | _ => none

/-- Coq `try_uni_cycle_spec`. -/
lemma tryUniCycle_spec {c c' : SConf} (h : tryUniCycle c = some c') :
    c.lift -[M]->* c'.lift := by
  unfold tryUniCycle at h
  split at h
  · -- config matches `⟨.right, .D :: .C1 :: .xs xs :: l3, r⟩`
    rename_i xs l3 r
    split at h
    · -- stripPrefix succeeds
      rename_i l hJ
      split at h
      · simp at h                                   -- count = 0
      · rename_i n hcount
        split at h
        · rename_i r' hstr                          -- stride succeeds
          simp only [Option.some.injEq] at h
          subst h
          have hlt : (n + 1) * uni_P < xs := uniCycleCount_lt xs r n hcount
          have hJeq : l3 = Jconst ++ l := stripPrefix_spec Jconst l3 l hJ
          subst hJeq
          set u := xs - (n + 1) * uni_P - 1 with hu
          have hxs : xs = u + ((n + 1) * uni_P + 1) := by omega
          have hsub : xs - (n + 1) * uni_P = u + 1 := by omega
          have key := uni_cycles n u l r r' hstr
          rw [hsub]
          simp only [SConf.lift]
          rw [hxs]
          exact key
        · simp at h                                 -- stride none
    · simp at h                                     -- stripPrefix none
  · simp at h                                       -- config mismatch

/-! ## Het universal-cycle shortcut (for the window chunks)

Mirror of `tryUniCycle` over het configurations with *pure* counts (window
chunks carry no het counts; only the abstract left tail `tailL`).  Soundness
follows `tryUniCycle_spec`'s proof through `uni_cycles`, so no `maxStride`
commutation is needed — the count lemma is pure arithmetic. -/

/-- Mirror of `maxStride` (pure counts only; `tailR`/het counts fail). -/
def maxStrideH : ℕ → List HRsym → Option ℕ
  | _, [.P] => none
  | _, .P :: _ => some 0
  | _, [] => some 0
  | xs, .xs (.pure k) :: t => maxStrideH (xs + k) t
  | _, .D :: t => maxStrideH 0 t
  | xs, .C :: t =>
      match maxStrideH 0 t with
      | some n' => some (min xs (n' >>> 2))
      | none => some xs
  | _, .Gs (.pure (_ + 1)) :: t => maxStrideH 0 t
  | _, _ => none

/-- Mirror of `uniCycleCount`. -/
def uniCycleCountH (xs : ℕ) (r : List HRsym) : ℕ :=
  let xsLimit := (xs - 1) / uni_P
  if xsLimit = 0 then 0
  else match maxStrideH 0 r with
    | some strides => min xsLimit (strides / uni_T)
    | none => xsLimit

/-- Mirror of `uniCycleCount_lt` (pure arithmetic). -/
lemma uniCycleCountH_lt (xs : ℕ) (r : List HRsym) (n : ℕ)
    (h : uniCycleCountH xs r = n + 1) : (n + 1) * uni_P < xs := by
  have hup : 0 < uni_P := by unfold uni_P; omega
  simp only [uniCycleCountH] at h
  split at h
  · omega
  · have hle : n + 1 ≤ (xs - 1) / uni_P := by split at h <;> omega
    have hdvd : (xs - 1) / uni_P * uni_P ≤ xs - 1 := Nat.div_mul_le_self (xs - 1) uni_P
    have hpos : 0 < (n + 1) * uni_P := Nat.mul_pos (Nat.succ_pos n) hup
    have hchain : (n + 1) * uni_P ≤ xs - 1 :=
      le_trans (Nat.mul_le_mul_right uni_P hle) hdvd
    omega

/-- Mirror of `tryUniCycle` (pure head count; the multi-stride must consume
no abstract strides, which holds exactly when the right tape is concrete). -/
def tryUniCycleH (c : HConf) : Option HConf :=
  match c with
  | ⟨.right, .D :: .C1 :: .xs (.pure xs) :: l, r⟩ =>
    (stripPrefix JH l).bind fun l =>
      let k := uniCycleCountH xs r
      if k = 0 then none else
      (strideH (.pure 0) (k * uni_T) r).bind fun p =>
        if p.2 = 0 then
          (FlsH (.pure k) l).bind fun l' =>
            (GrsH (.pure k) p.1).map fun r'' =>
              ⟨.right, .D :: .C1 :: .xs (.pure (xs - k * uni_P)) :: JH ++ l', r''⟩
        else none
  | _ => none

/-- `substL` through the concrete `JH` prefix. -/
lemma substL_JH (m : ℕ) (lt : List Lsym) (l : List HLsym) :
    substL m lt (JH ++ l) = Jconst ++ substL m lt l := rfl

/-- `lxs` pushes onto the concrete `Jconst` prefix (head `.D`). -/
lemma lxs_J (k : ℕ) (hk : k ≠ 0) (X : List Lsym) :
    lxs k (Jconst ++ X) = .xs k :: Jconst ++ X := by
  unfold lxs
  rw [if_neg hk]
  rfl

/-- `substL` through the uni-cycle head shape (definitional except the
`lxs` push). -/
lemma substL_head (m : ℕ) (lt : List Lsym) (k : ℕ) (hk : k ≠ 0)
    (l : List HLsym) :
    substL m lt (.D :: .C1 :: .xs (.pure k) :: JH ++ l) =
      .D :: .C1 :: .xs k :: Jconst ++ substL m lt l := by
  show .D :: .C1 :: lxs (HN.subst m (.pure k)) (substL m lt (JH ++ l)) = _
  rw [HN.subst_pure, substL_JH, lxs_J k hk]
  rfl

/-- `substL` through a positive pure `xs` cell on a `.D`-headed rest. -/
lemma substL_xs_pure (m : ℕ) (lt : List Lsym) (k : ℕ) (hk : k ≠ 0)
    (l : List HLsym) :
    substL m lt (.xs (.pure k) :: JH ++ l) =
      .xs k :: Jconst ++ substL m lt l := by
  show lxs (HN.subst m (.pure k)) (substL m lt (JH ++ l)) = _
  rw [HN.subst_pure, substL_JH]
  unfold lxs
  rw [if_neg hk]
  rfl

set_option maxHeartbeats 1000000 in
/-- Soundness of the het universal-cycle shortcut (mirror of
`tryUniCycle_spec`; the abstract right tape is untouched: `rt` unchanged). -/
lemma tryUniCycleH_sound {c c' : HConf} (h : tryUniCycleH c = some c')
    (m : ℕ) (lt : List Lsym) (rt : List Rsym) :
    (c.subst m lt rt).lift -[M]->* (c'.subst m lt rt).lift := by
  unfold tryUniCycleH at h
  split at h
  · rename_i xs l3 r
    rw [Option.bind_eq_some_iff] at h
    obtain ⟨l, hJ, h⟩ := h
    simp only at h
    by_cases hk0 : uniCycleCountH xs r = 0
    · rw [if_pos hk0] at h; exact absurd h (by simp)
    · rw [if_neg hk0] at h
      rw [Option.bind_eq_some_iff] at h
      obtain ⟨p, hstr, h⟩ := h
      obtain ⟨r', d⟩ := p
      by_cases hd0 : d = 0
      · subst hd0
        rw [if_pos rfl] at h
        rw [Option.bind_eq_some_iff] at h
        obtain ⟨l', hFls, h⟩ := h
        rw [Option.map_eq_some_iff] at h
        obtain ⟨r'', hGrs, h⟩ := h
        subst h
        obtain ⟨n, hn⟩ : ∃ n, uniCycleCountH xs r = n + 1 :=
          ⟨uniCycleCountH xs r - 1, by omega⟩
        rw [hn] at hstr hFls hGrs ⊢
        have hlt : (n + 1) * uni_P < xs := uniCycleCountH_lt xs r n hn
        have hJeq : l3 = JH ++ l := stripPrefix_spec JH l3 l hJ
        subst hJeq
        have hstr' : stride 0 ((n + 1) * uni_T) (substR m rt r) =
            some (substR m rt r') := by
          have hT : 1 ≤ (n + 1) * uni_T := by
            have : 0 < uni_T := by unfold uni_T uni_P; omega
            exact Nat.one_le_iff_ne_zero.mpr (Nat.mul_ne_zero (by omega) (by omega))
          exact strideH_subst m (rt := rt) (rt' := rt) (t := r) hstr hT
            (fun hd => absurd hd (by omega))
        set u := xs - (n + 1) * uni_P - 1 with hu
        have hxs : xs = u + ((n + 1) * uni_P + 1) := by omega
        have hsub : xs - (n + 1) * uni_P = u + 1 := by omega
        have key := uni_cycles n u (substL m lt l) (substR m rt r)
          (substR m rt r') hstr'
        simp only [HConf.subst, SConf.lift,
          substL_head m lt xs (by omega) l,
          substL_head m lt (xs - (n + 1) * uni_P) (by omega) l',
          substL_FlsH m lt hFls, substR_GrsH m rt hGrs, HN.subst_pure]
        rw [hsub, hxs]
        exact key
      · rw [if_neg hd0] at h; exact absurd h (by simp)
  · exact absurd h (by simp)

/-! ## Event-driven het runner (window chunks) -/

/-- One event on a het configuration: `0` = simple step, `1` = stride (must
consume no abstract strides, i.e. the right tape is concrete), `2+` = uni. -/
def stepEH (e : ℕ) (c : HConf) : Option HConf :=
  match e with
  | 0 => simpleStepH c
  | 1 => (tryStrideH c).bind fun p => if p.2 = 0 then some p.1 else none
  | _ => tryUniCycleH c

/-- Soundness of one event: the abstract tapes are untouched. -/
lemma stepEH_sound {e : ℕ} {c c' : HConf} (h : stepEH e c = some c')
    (m : ℕ) (lt : List Lsym) (rt : List Rsym) :
    (c.subst m lt rt).lift -[M]->* (c'.subst m lt rt).lift := by
  match e with
  | 0 => exact simpleStepH_sound h m lt rt
  | 1 =>
    have h' : ((tryStrideH c).bind fun p => if p.2 = 0 then some p.1 else none)
        = some c' := h
    rw [Option.bind_eq_some_iff] at h'
    obtain ⟨⟨c0, d⟩, hst, h'⟩ := h'
    by_cases hd : d = 0
    · subst hd
      rw [if_pos rfl] at h'
      injection h' with h'
      subst h'
      obtain ⟨dir, l, r⟩ := c
      cases dir with
      | left => simp [tryStrideH] at hst
      | right =>
        simp only [tryStrideH, Option.map_eq_some_iff] at hst
        obtain ⟨⟨res, d0⟩, hs, heq⟩ := hst
        injection heq with h1 h2
        subst h1; subst h2
        have key := strideH_subst m (rt := rt) (rt' := rt) (t := r) hs le_rfl
          (fun h1le => absurd h1le (by omega))
        simp only [HN.subst_pure] at key
        simp only [HConf.subst, SConf.lift]
        exact stride_correct_0 _ _ _ key
    · rw [if_neg hd] at h'; exact absurd h' (by simp)
  | n + 2 => exact tryUniCycleH_sound h m lt rt

/-- Run one packed group of `k ≤ 64` events (2 bits each, little-endian). -/
def stepsEH64 (k : ℕ) : ℕ → HConf → Option HConf :=
  Nat.rec (motive := fun _ => ℕ → HConf → Option HConf)
    (fun _ c => some c)
    (fun _ ih g c =>
      match stepEH (g % 4) c with
      | some c' => ih (g / 4) c'
      | none => none)
    k

/-- Run a list of full 64-event groups. -/
def stepsEH (fuel : ℕ) : List ℕ → HConf → Option HConf :=
  Nat.rec (motive := fun _ => List ℕ → HConf → Option HConf)
    (fun _ c => some c)
    (fun _ ih gs c =>
      match gs with
      | [] => some c
      | g :: gs =>
        match stepsEH64 64 g c with
        | some c' => ih gs c'
        | none => none)
    fuel

lemma stepsEH64_spec (k : ℕ) {g : ℕ} {c c' : HConf}
    (h : stepsEH64 k g c = some c') (m : ℕ) (lt : List Lsym) (rt : List Rsym) :
    (c.subst m lt rt).lift -[M]->* (c'.subst m lt rt).lift := by
  induction k generalizing g c with
  | zero =>
    have : some c = some c' := h
    injection this with h1
    subst h1
    exact Machine.EvStep.refl
  | succ k IH =>
    have h' : (match stepEH (g % 4) c with
      | some c' => stepsEH64 k (g / 4) c'
      | none => none) = some c' := h
    cases he : stepEH (g % 4) c with
    | none => rw [he] at h'; exact absurd h' (by simp)
    | some c0 =>
      rw [he] at h'
      exact (stepEH_sound he m lt rt).trans (IH h')

lemma stepsEH_spec (fuel : ℕ) {gs : List ℕ} {c c' : HConf}
    (h : stepsEH fuel gs c = some c') (m : ℕ) (lt : List Lsym) (rt : List Rsym) :
    (c.subst m lt rt).lift -[M]->* (c'.subst m lt rt).lift := by
  induction fuel generalizing gs c with
  | zero =>
    have : some c = some c' := h
    injection this with h1
    subst h1
    exact Machine.EvStep.refl
  | succ fuel IH =>
    match gs with
    | [] =>
      have h' : some c = some c' := h
      injection h' with h1
      subst h1
      exact Machine.EvStep.refl
    | g :: gs =>
      have h' : (match stepsEH64 64 g c with
        | some c' => stepsEH fuel gs c'
        | none => none) = some c' := h
      cases he : stepsEH64 64 g c with
      | none => rw [he] at h'; exact absurd h' (by simp)
      | some c0 =>
        rw [he] at h'
        exact (stepsEH64_spec 64 he m lt rt).trans (IH h')

/-- Coq `fullstep`: try the universal-cycle shortcut, else one `step`. -/
def fullstep (c : SConf) : Option SConf :=
  match tryUniCycle c with
  | some c' => some c'
  | none => step c

/-- Coq `fullstep_spec`. -/
lemma fullstep_spec {c c' : SConf} (h : fullstep c = some c') :
    c.lift -[M]->* c'.lift := by
  simp only [fullstep] at h
  cases he : tryUniCycle c with
  | some c0 => rw [he] at h; simp only [Option.some.injEq] at h; subst h; exact tryUniCycle_spec he
  | none => rw [he] at h; exact step_spec h

/-! ## Iterated stepping and the terminal cycle -/

/-- Coq `steps`: iterate `fullstep` `n` times. -/
def steps : ℕ → SConf → Option SConf
  | 0, c => some c
  | n + 1, c => match fullstep c with | some c' => steps n c' | none => none

/-- Coq `steps_spec`. -/
lemma steps_spec (n : ℕ) {c c' : SConf} (h : steps n c = some c') :
    c.lift -[M]->* c'.lift := by
  induction n generalizing c with
  | zero => simp only [steps, Option.some.injEq] at h; subst h; exact Machine.EvStep.refl
  | succ n IH =>
    simp only [steps] at h
    cases he : fullstep c with
    | none => rw [he] at h; simp at h
    | some c0 => rw [he] at h; exact (fullstep_spec he).trans (IH h)

/-- Fuel-recursion over `fullstep` via bare `Nat.rec`, so kernel reduction of
chunked certificates is head-iterative (the `brecOn` compilation of `steps`
builds a below-tower of depth = fuel, overflowing on large chunks). -/
def stepsK (fuel : ℕ) : SConf → Option SConf :=
  Nat.rec (motive := fun _ => SConf → Option SConf)
    (fun c => some c)
    (fun _ ih c => match fullstep c with | some c' => ih c' | none => none)
    fuel

/-- `stepsK` soundness (mirror of `steps_spec`). -/
lemma stepsK_spec (n : ℕ) {c c' : SConf} (h : stepsK n c = some c') :
    c.lift -[M]->* c'.lift := by
  induction n generalizing c with
  | zero =>
    have : some c = some c' := h
    injection this with h1
    subst h1
    exact Machine.EvStep.refl
  | succ n IH =>
    have h' : (match fullstep c with
        | some c0 => stepsK n c0 | none => none) = some c' := h
    cases he : fullstep c with
    | none => rw [he] at h'; simp at h'
    | some c0 => rw [he] at h'; exact (fullstep_spec he).trans (IH h')

/-! ## Packed boundary configurations

Chunked certificates state `stepsK K (decodeConf …) = some (decodeConf …)`
with boundaries packed into short lists of medium `ℕ` literals (≤ 512 symbols
per group: small enough for shallow kernel recursion, large enough to keep the
generated source compact).  The encoder lives in the untrusted profiling exe;
no decoder correctness proof is needed — the decoded VALUE is what the
certificate states.  Varints are little-endian base-8 nibbles with a
continuation bit; a symbol is a varint tag followed by a varint count for the
counted constructors. -/

/-- Decode a varint; returns `(value, rest)`. -/
def decodeVar : ℕ → ℕ → ℕ × ℕ
  | 0, n => (0, n)
  | fuel + 1, n =>
    let nib := n % 16
    if nib < 8 then (nib, n / 16)
    else
      let (v, r) := decodeVar fuel (n / 16)
      (nib - 8 + 8 * v, r)

/-- Decode one left symbol. -/
def decodeLsym (n : ℕ) : Lsym × ℕ :=
  let (t, n) := decodeVar 64 n
  match t with
  | 0 => let (k, n) := decodeVar 64 n; (.xs k, n)
  | 1 => (.D, n) | 2 => (.P, n)
  | 3 => (.C0, n) | 4 => (.C1, n) | 5 => (.C2, n) | 6 => (.C3, n)
  | 7 => (.F0, n) | 8 => (.F1, n) | 9 => (.F2, n) | 10 => (.F3, n)
  | 11 => (.G0, n) | 12 => (.G1, n) | 13 => (.G2, n)
  | 14 => let (k, n) := decodeVar 64 n; (.Fs k, n)
  | 15 => let (k, n) := decodeVar 64 n; (.Gs k, n)
  | _ => let (k, n) := decodeVar 64 n; (.Hs k, n)

/-- Decode one right symbol. -/
def decodeRsym (n : ℕ) : Rsym × ℕ :=
  let (t, n) := decodeVar 64 n
  match t with
  | 0 => let (k, n) := decodeVar 64 n; (.xs k, n)
  | 1 => (.D, n) | 2 => (.C, n) | 3 => (.P, n)
  | _ => let (k, n) := decodeVar 64 n; (.Gs k, n)

/-- Decode `k` left symbols. -/
def decodeLsyms : ℕ → ℕ → List Lsym × ℕ
  | 0, n => ([], n)
  | k + 1, n =>
    let (s, n) := decodeLsym n
    let (rest, n2) := decodeLsyms k n
    (s :: rest, n2)

/-- Decode `k` right symbols. -/
def decodeRsyms : ℕ → ℕ → List Rsym × ℕ
  | 0, n => ([], n)
  | k + 1, n =>
    let (s, n) := decodeRsym n
    let (rest, n2) := decodeRsyms k n
    (s :: rest, n2)

/-- Decode a list of packed groups (each: leading varint symbol count). -/
def decodeLGroups : List ℕ → List Lsym
  | [] => []
  | g :: gs =>
    let (k, g) := decodeVar 64 g
    (decodeLsyms k g).1 ++ decodeLGroups gs

def decodeRGroups : List ℕ → List Rsym
  | [] => []
  | g :: gs =>
    let (k, g) := decodeVar 64 g
    (decodeRsyms k g).1 ++ decodeRGroups gs

/-- Fuel-based group-list decoding (bare `Nat.rec`, head-iterative in the
kernel; the per-group recursions are ≤ 48 deep).  `fuel` = number of groups,
supplied as a literal by the generator. -/
def decodeLGroupsF (fuel : ℕ) : List ℕ → List Lsym :=
  Nat.rec (motive := fun _ => List ℕ → List Lsym)
    (fun _ => [])
    (fun _ ih gs =>
      match gs with
      | [] => []
      | g :: gs =>
        let p := decodeVar 64 g
        (decodeLsyms p.1 p.2).1 ++ ih gs)
    fuel

def decodeRGroupsF (fuel : ℕ) : List ℕ → List Rsym :=
  Nat.rec (motive := fun _ => List ℕ → List Rsym)
    (fun _ => [])
    (fun _ ih gs =>
      match gs with
      | [] => []
      | g :: gs =>
        let p := decodeVar 64 g
        (decodeRsyms p.1 p.2).1 ++ ih gs)
    fuel

/-- Fuel-based decoded configuration. -/
def decodeConfF (lf rf : ℕ) (dir : ℕ) (lg rg : List ℕ) : SConf :=
  ⟨if dir = 0 then .left else .right, decodeLGroupsF lf lg, decodeRGroupsF rf rg⟩

/-- Fuel-based list equality, head-iterative in the kernel (the derived
`List.decEq` builds a length-deep `brecOn` tower). -/
def eqListF [DecidableEq α] (fuel : ℕ) : List α → List α → Bool :=
  Nat.rec (motive := fun _ => List α → List α → Bool)
    (fun _ _ => false)
    (fun _ ih a b =>
      match a, b with
      | [], [] => true
      | x :: xs, y :: ys => decide (x = y) && ih xs ys
      | _, _ => false)
    fuel

lemma eqListF_eq [DecidableEq α] (fuel : ℕ) :
    ∀ {a b : List α}, eqListF fuel a b = true → a = b := by
  induction fuel with
  | zero => intro a b h; exact absurd h (by simp [eqListF])
  | succ n IH =>
    intro a b h
    match a, b with
    | [], [] => rfl
    | x :: xs, y :: ys =>
      have h' : (decide (x = y) && eqListF n xs ys) = true := h
      simp only [Bool.and_eq_true, decide_eq_true_eq] at h'
      rw [h'.1, IH h'.2]
    | [], _ :: _ => exact Bool.noConfusion (show false = true from h)
    | _ :: _, [] => exact Bool.noConfusion (show false = true from h)

/-- Fuel-based comparison of an optional configuration against a packed one. -/
def eqOConfF (lf rf : ℕ) (c : Option SConf) (dir : ℕ) (lg rg : List ℕ) : Bool :=
  match c with
  | none => false
  | some c =>
    decide (c.dir = (decodeConfF lf rf dir lg rg).dir) &&
    eqListF (lf * 48 + 49) c.left (decodeLGroupsF lf lg) &&
    eqListF (rf * 48 + 49) c.right (decodeRGroupsF rf rg)

lemma eqOConfF_eq {lf rf : ℕ} {c : Option SConf} {dir : ℕ} {lg rg : List ℕ}
    (h : eqOConfF lf rf c dir lg rg = true) :
    c = some (decodeConfF lf rf dir lg rg) := by
  match c with
  | none => exact absurd h (by simp [eqOConfF])
  | some c =>
    simp only [eqOConfF, Bool.and_eq_true, decide_eq_true_eq] at h
    obtain ⟨⟨hd, hl⟩, hr⟩ := h
    have hl' := eqListF_eq _ hl
    have hr' := eqListF_eq _ hr
    obtain ⟨cd, cl, cr⟩ := c
    simp only [decodeConfF] at hd hl' hr' ⊢
    rw [hd, hl', hr']

/-! ## Packed het-window boundaries

Window chunks materialize only the *active* left window (the deep inert tail
is the abstract `tailL`); counts are always pure.  Same varint scheme as the
concrete decoder; left tag `17` is the tail marker. -/

/-- Decode one het left symbol (pure counts; tag `17` = `tailL`). -/
def decodeHLsym (n : ℕ) : HLsym × ℕ :=
  let (t, n) := decodeVar 64 n
  match t with
  | 0 => let (k, n) := decodeVar 64 n; (.xs (.pure k), n)
  | 1 => (.D, n) | 2 => (.P, n)
  | 3 => (.C0, n) | 4 => (.C1, n) | 5 => (.C2, n) | 6 => (.C3, n)
  | 7 => (.F0, n) | 8 => (.F1, n) | 9 => (.F2, n) | 10 => (.F3, n)
  | 11 => (.G0, n) | 12 => (.G1, n) | 13 => (.G2, n)
  | 14 => let (k, n) := decodeVar 64 n; (.Fs (.pure k), n)
  | 15 => let (k, n) := decodeVar 64 n; (.Gs (.pure k), n)
  | 16 => let (k, n) := decodeVar 64 n; (.Hs (.pure k), n)
  | _ => (.tailL, n)

/-- Decode one het right symbol (pure counts). -/
def decodeHRsym (n : ℕ) : HRsym × ℕ :=
  let (t, n) := decodeVar 64 n
  match t with
  | 0 => let (k, n) := decodeVar 64 n; (.xs (.pure k), n)
  | 1 => (.D, n) | 2 => (.C, n) | 3 => (.P, n)
  | 4 => let (k, n) := decodeVar 64 n; (.Gs (.pure k), n)
  | _ => (.tailR, n)

def decodeHLsyms : ℕ → ℕ → List HLsym × ℕ
  | 0, n => ([], n)
  | k + 1, n =>
    let (s, n) := decodeHLsym n
    let (rest, n2) := decodeHLsyms k n
    (s :: rest, n2)

def decodeHRsyms : ℕ → ℕ → List HRsym × ℕ
  | 0, n => ([], n)
  | k + 1, n =>
    let (s, n) := decodeHRsym n
    let (rest, n2) := decodeHRsyms k n
    (s :: rest, n2)

def decodeHLGroupsF (fuel : ℕ) : List ℕ → List HLsym :=
  Nat.rec (motive := fun _ => List ℕ → List HLsym)
    (fun _ => [])
    (fun _ ih gs =>
      match gs with
      | [] => []
      | g :: gs =>
        let p := decodeVar 64 g
        (decodeHLsyms p.1 p.2).1 ++ ih gs)
    fuel

def decodeHRGroupsF (fuel : ℕ) : List ℕ → List HRsym :=
  Nat.rec (motive := fun _ => List ℕ → List HRsym)
    (fun _ => [])
    (fun _ ih gs =>
      match gs with
      | [] => []
      | g :: gs =>
        let p := decodeVar 64 g
        (decodeHRsyms p.1 p.2).1 ++ ih gs)
    fuel

/-- Decode a packed het configuration. -/
def decodeHConfF (lf rf : ℕ) (dir : ℕ) (lg rg : List ℕ) : HConf :=
  ⟨if dir = 0 then .left else .right, decodeHLGroupsF lf lg, decodeHRGroupsF rf rg⟩

/-- Fuel-based comparison of an optional het configuration against a packed
one. -/
def eqHOConfF (lf rf : ℕ) (c : Option HConf) (dir : ℕ) (lg rg : List ℕ) : Bool :=
  match c with
  | none => false
  | some c =>
    decide (c.dir = (decodeHConfF lf rf dir lg rg).dir) &&
    eqListF (lf * 48 + 49) c.left (decodeHLGroupsF lf lg) &&
    eqListF (rf * 48 + 49) c.right (decodeHRGroupsF rf rg)

lemma eqHOConfF_eq {lf rf : ℕ} {c : Option HConf} {dir : ℕ} {lg rg : List ℕ}
    (h : eqHOConfF lf rf c dir lg rg = true) :
    c = some (decodeHConfF lf rf dir lg rg) := by
  match c with
  | none => exact absurd h (by simp [eqHOConfF])
  | some c =>
    simp only [eqHOConfF, Bool.and_eq_true, decide_eq_true_eq] at h
    obtain ⟨⟨hd, hl⟩, hr⟩ := h
    have hl' := eqListF_eq _ hl
    have hr' := eqListF_eq _ hr
    obtain ⟨cd, cl, cr⟩ := c
    simp only [decodeHConfF] at hd hl' hr' ⊢
    rw [hd, hl', hr']


/-- Decode a packed configuration. -/
def decodeConf (dir : ℕ) (lg rg : List ℕ) : SConf :=
  ⟨if dir = 0 then .left else .right, decodeLGroups lg, decodeRGroups rg⟩

/-! ## Event-driven runner

Replaying `fullstep` re-runs its schedule *search* every step; at mid-run the
uni-shaped but budget-blocked configs pay `tryUniCycle`'s full `maxStride`
walk each time (~70x cost).  Here the untrusted generator supplies the branch
taken per step (2 bits, packed 64 per `ℕ`, little-endian): the kernel only
executes the chosen branch, and soundness is trivial since every branch is
individually sound. -/

/-- Run one packed group of `k ≤ 64` events (`0` = simpleStep, `1` = tryStride,
`2` = tryUniCycle). -/
def stepsE64 (k : ℕ) : ℕ → SConf → Option SConf :=
  Nat.rec (motive := fun _ => ℕ → SConf → Option SConf)
    (fun _ c => some c)
    (fun _ ih g c =>
      match (match g % 4 with
             | 0 => simpleStep c
             | 1 => tryStride c
             | _ => tryUniCycle c) with
      | some c' => ih (g / 4) c'
      | none => none)
    k

/-- Run a list of full 64-event groups (`fuel` = group count). -/
def stepsE (fuel : ℕ) : List ℕ → SConf → Option SConf :=
  Nat.rec (motive := fun _ => List ℕ → SConf → Option SConf)
    (fun _ c => some c)
    (fun _ ih gs c =>
      match gs with
      | [] => some c
      | g :: gs =>
        match stepsE64 64 g c with
        | some c' => ih gs c'
        | none => none)
    fuel

lemma stepsE64_spec (k : ℕ) {g : ℕ} {c c' : SConf}
    (h : stepsE64 k g c = some c') : c.lift -[M]->* c'.lift := by
  induction k generalizing g c with
  | zero =>
    have : some c = some c' := h
    injection this with h1
    subst h1
    exact Machine.EvStep.refl
  | succ k IH =>
    have h' : (match (match g % 4 with
        | 0 => simpleStep c
        | 1 => tryStride c
        | _ => tryUniCycle c) with
      | some c' => stepsE64 k (g / 4) c'
      | none => none) = some c' := h
    cases he : (match g % 4 with
        | 0 => simpleStep c
        | 1 => tryStride c
        | _ => tryUniCycle c) with
    | none => rw [he] at h'; exact absurd h' (by simp)
    | some c0 =>
      rw [he] at h'
      refine Machine.EvStep.trans ?_ (IH h')
      match hg : g % 4 with
      | 0 => rw [hg] at he; exact simple_step_spec he
      | 1 => rw [hg] at he; exact tryStride_spec he
      | 2 => rw [hg] at he; exact tryUniCycle_spec he
      | n + 3 => rw [hg] at he; exact tryUniCycle_spec he

lemma stepsE_spec (fuel : ℕ) {gs : List ℕ} {c c' : SConf}
    (h : stepsE fuel gs c = some c') : c.lift -[M]->* c'.lift := by
  induction fuel generalizing gs c with
  | zero =>
    have : some c = some c' := h
    injection this with h1
    subst h1
    exact Machine.EvStep.refl
  | succ fuel IH =>
    match gs with
    | [] =>
      have h' : some c = some c' := h
      injection h' with h1
      subst h1
      exact Machine.EvStep.refl
    | g :: gs =>
      have h' : (match stepsE64 64 g c with
        | some c' => stepsE fuel gs c'
        | none => none) = some c' := h
      cases he : stepsE64 64 g c with
      | none => rw [he] at h'; exact absurd h' (by simp)
      | some c0 =>
        rw [he] at h'
        exact (stepsE64_spec 64 he).trans (IH h')

/-- Coq `F` as an `Lsym` list. -/
def Fconst : List Lsym := [.xs 10344, .D, .xs 7640, .C2]

/-- The terminal cycling configuration family (Coq `C l = lift (right, C0 :: l, K)`). -/
def cycleConf (l : List Lsym) : Config 4 1 := SConf.lift ⟨.right, .C0 :: l, Kconst⟩

/-- Membership predicate for the terminal cycle. -/
def cyclingBase (C : Config 4 1) : Prop := ∃ l, C = cycleConf l

/-- An `EvStep` between distinct configs is a genuine `Progress`. -/
lemma evstep_progress_of_ne {A B : Config 4 1} (h : A -[M]->* B) (hne : A ≠ B) :
    A -[M]->+ B := by
  obtain ⟨n, hn⟩ := h.to_multistep
  cases n with
  | zero => cases hn; exact absurd rfl hne
  | succ n => exact Machine.Progress.from_multistep' (Nat.succ_pos n) hn

/-- The `.left` (state-2) config reached after 30 fullsteps of the terminal
cycle (Coq's `steps 30` waypoint, chosen so the head points the other way and
distinctness from the start is immediate). -/
def midL (l : List Lsym) : SConf :=
  ⟨.left,
   [.C0, .xs 7087, .D, .D, .xs 2179, .C0, .xs 13074, .D, .xs 6275, .C0, .xs 11026, .D,
    .xs 7299, .C0, .xs 10514, .D, .xs 7555, .C0, .xs 10386, .D, .xs 7619, .C0, .xs 10354, .D,
    .xs 7635, .C0, .xs 10346, .D, .xs 7639, .C0] ++ l,
   [.C, .xs 3851, .P]⟩

set_option maxRecDepth 4000 in
/-- Coq `infinite_cycle`: one pass of the terminal cycle prepends `F` and returns
to the same shape (a genuine `-[M]->+` progress).  The concrete `982`-fullstep
simulation reduces by `rfl` even with abstract far-left tape `l` (the head never
reaches it); the first `30` steps land in a `.left` config, distinct from the
`.right` start by machine state, upgrading the `EvStep` to a `Progress`. -/
lemma infinite_cycle (l : List Lsym) :
    cycleConf l -[M]->+ cycleConf (Fconst ++ l) := by
  have h30 : steps 30 (⟨.right, .C0 :: l, Kconst⟩ : SConf) = some (midL l) := by rfl
  have hne : (⟨.right, .C0 :: l, Kconst⟩ : SConf).lift ≠ (midL l).lift := by
    simp only [SConf.lift, midL, dR, dL, headL]
    intro h
    injection h with hstate _
    exact absurd hstate (by decide)
  have hprog : (⟨.right, .C0 :: l, Kconst⟩ : SConf).lift -[M]->+ (midL l).lift :=
    evstep_progress_of_ne (steps_spec 30 h30) hne
  have htail : (midL l).lift -[M]->* cycleConf (Fconst ++ l) :=
    steps_spec 952 (by rfl)
  exact Trans.trans hprog htail

/-- Coq `cycle_nonhalt`: the terminal cycle never halts (via `ClosedSet`). -/
lemma cycle_nonhalt (l : List Lsym) : ¬ M.halts (cycleConf l) := by
  have cs : ClosedSet M cyclingBase (cycleConf l) := by
    refine ⟨?_, ?_⟩
    · rintro ⟨C, l', rfl⟩
      exact ⟨⟨cycleConf (Fconst ++ l'), Fconst ++ l', rfl⟩, infinite_cycle l'⟩
    · exact ⟨⟨cycleConf l, l, rfl⟩, Machine.EvStep.refl⟩
  exact cs.nonHalting

/-- Coq `is_cycling`: detects a terminal-cycle configuration. -/
def isCycling (c : SConf) : Bool :=
  match c with
  | ⟨.right, .C0 :: _, r⟩ => decide (r = Kconst)
  | _ => false

/-- Coq `is_cycling_spec`. -/
lemma is_cycling_spec {c : SConf} (h : isCycling c = true) : ¬ M.halts c.lift := by
  unfold isCycling at h
  split at h
  · rename_i l r
    have hr : r = Kconst := by simpa using h
    subst hr
    exact cycle_nonhalt l
  · simp at h

/-- Coq `doit`: run up to `n` fullsteps, succeeding if a cycling config is hit. -/
def doit : ℕ → SConf → Bool
  | 0, _ => false
  | n + 1, c =>
    if isCycling c then true
    else match fullstep c with | some c' => doit n c' | none => false

/-- Coq `doit_spec`. -/
lemma doit_spec (n : ℕ) {c : SConf} (h : doit n c = true) : ¬ M.halts c.lift := by
  induction n generalizing c with
  | zero => simp [doit] at h
  | succ n IH =>
    simp only [doit] at h
    split at h
    · rename_i hcyc; exact is_cycling_spec hcyc
    · cases he : fullstep c with
      | none => rw [he] at h; simp at h
      | some c' => rw [he] at h; exact Machine.halts.skip_evstep (fullstep_spec he) (IH h)

/-- Coq `initial`. -/
def initial : SConf := ⟨.right, [.C1], [.P]⟩

/-- Coq `init'`: the blank tape reaches `lift initial`.  Concrete finite run. -/
lemma init' : (default : Config 4 1) -[M]->* initial.lift := by
  have hd : (default : Config 4 1) = dR ∅ ∅ := rfl
  rw [hd]
  simp only [initial, SConf.lift, liftLeft, liftRight, Lsym.block, Rsym.block, List.append_nil]
  unfoldBlocks; sim

end Deciders.Skelet.Skelet1
