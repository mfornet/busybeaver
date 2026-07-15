import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith
import Busybeaver.TM.Table.Parse
import Busybeaver.TM.Table.Reachability
import Busybeaver.TM.Table.ClosedSet
import Busybeaver.Deciders.Sweep
import Busybeaver.Deciders.Skelet.TapeCalc

/-!
# Skelet #17 — tape layer (levels 0–2)

Lean port of `Coq-BB5/CoqBB5/BB5/BB5_Skelet17.v` (ccz181078's proof that Skelet
machine #17, `1RB---_0LC1RE_0LD1LC_1RA1LB_0RB0RA`, does not halt) — the
tape-facing half.  This file covers the Coq development up to the abstract rule
inductives:

* the list-of-exponents tape encoding `lowerL`/`lowerR` (`(10)`-repeater blocks
  separated by `1`s),
* the level-1 sweep lemmas `goright_10`, `goleft_even10`, `goleft_odd10`,
* the level-2 rewrite rules `increment_*`, `overflow_*`, `zero_*`.

Configurations mirror busycoq notation: `l <| r` (head over the top cell of
`l`, state `C`) is `atC l r = headL 2 l r`, and `l |> r` (head over the top
cell of `r`, state `B`) is `atB l r`, both in `Turing.Tape.mk'` form.
-/

namespace Deciders.Skelet.Skelet17

open Turing
open TM.Table

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

/-- Skelet #17: `1RB---_0LC1RE_0LD1LC_1RA1LB_0RB0RA` (`sporadicMachine8`). -/
abbrev M : Machine 4 1 := mach["1RB---_0LC1RE_0LD1LC_1RA1LB_0RB0RA"]

-- Transitions (A=0, B=1, C=2, D=3, E=4).
lemma gA0 : M.get 0 0 = .next 1 .right 1 := by decide
lemma gB0 : M.get 1 0 = .next 0 .left 2 := by decide
lemma gB1 : M.get 1 1 = .next 1 .right 4 := by decide
lemma gC0 : M.get 2 0 = .next 0 .left 3 := by decide
lemma gC1 : M.get 2 1 = .next 1 .left 2 := by decide
lemma gD0 : M.get 3 0 = .next 1 .right 0 := by decide
lemma gD1 : M.get 3 1 = .next 1 .left 1 := by decide
lemma gE0 : M.get 4 0 = .next 0 .right 1 := by decide
lemma gE1 : M.get 4 1 = .next 0 .right 0 := by decide
-- blank-edge duplicates (`default = 0`)
lemma gA0d : M.get 0 default = .next 1 .right 1 := by decide
lemma gB0d : M.get 1 default = .next 0 .left 2 := by decide
lemma gC0d : M.get 2 default = .next 0 .left 3 := by decide
lemma gD0d : M.get 3 default = .next 1 .right 0 := by decide
lemma gE0d : M.get 4 default = .next 0 .right 1 := by decide

local notation "𝟙" => (1 : Symbol 1)
local notation "𝟘" => (0 : Symbol 1)

@[simp] lemma cons_zero_empty : ListBlank.cons 𝟘 ∅ = ∅ := ListBlank.cons_default_empty

/-! ## Side encodings

Busycoq sides are streams with the head-nearest cell first; our `ListBlank`s
are the same.  `l << b` is `ListBlank.cons b l`; pushing the two-symbol string
`<[1; 0]` is `cons 𝟘 (cons 𝟙 ·)` (the `0` ends up on top). -/

/-- Push `(10)^n` onto a left side (busycoq `l <* <[1; 0]^^n`): the tape reads
`… 1 0 1 0 ⌈head⌉` with the final `0` nearest the head. -/
def pow10L : ℕ → ListBlank (Symbol 1) → ListBlank (Symbol 1)
  | 0, l => l
  | n + 1, l => ListBlank.cons 𝟘 (ListBlank.cons 𝟙 (pow10L n l))

/-- Prepend `(10)^n` onto a right side (busycoq `[1; 0]^^n *> r`): the tape
reads `⌈head⌉ 1 0 1 0 …` with the leading `1` nearest the head. -/
def pow10R : ℕ → ListBlank (Symbol 1) → ListBlank (Symbol 1)
  | 0, r => r
  | n + 1, r => ListBlank.cons 𝟙 (ListBlank.cons 𝟘 (pow10R n r))

/-- Coq `lowerL'`: encode exponents with a separator `1` on top, assuming a
`(10)^x` block will be pushed above. -/
def lowerL' : List ℕ → ListBlank (Symbol 1)
  | [] => ∅
  | x :: xs => ListBlank.cons 𝟙 (pow10L x (lowerL' xs))

/-- Coq `lowerL`: the left side `10^x(l-1) 1 … 1 10^x(1) 1 10^x(0)`, head-side
block first in the list. -/
def lowerL : List ℕ → ListBlank (Symbol 1)
  | [] => ∅
  | x :: xs => pow10L x (lowerL' xs)

/-- Coq `lowerR'`: right-side encoding with a leading separator `1`. -/
def lowerR' : List ℕ → ListBlank (Symbol 1)
  | [] => ∅
  | x :: xs => ListBlank.cons 𝟙 (pow10R x (lowerR' xs))

/-- Coq `lowerR`: right-side encoding, head-side block first. -/
def lowerR : List ℕ → ListBlank (Symbol 1)
  | [] => ∅
  | x :: xs => pow10R x (lowerR' xs)

/-- Busycoq `l <{{C}} r` (written `l <| r`): state `C`, head over the top cell
of `l`. -/
abbrev atC (l r : ListBlank (Symbol 1)) : Config 4 1 := headL 2 l r

/-- Busycoq `l {{B}}> r` (written `l |> r`): state `B`, head over the top cell
of `r`. -/
def atB (l r : ListBlank (Symbol 1)) : Config 4 1 :=
  ⟨1, Tape.mk' l r⟩

/-- Coq `lower xs = lowerL xs <| const 0`. -/
def lower (xs : List ℕ) : Config 4 1 := atC (lowerL xs) ∅

/-- Coq `lower' xs = lowerL xs |> const 0`. -/
def lower' (xs : List ℕ) : Config 4 1 := atB (lowerL xs) ∅

/-! ### Structural lemmas on the encodings -/

lemma pow10L_add (m n : ℕ) (l : ListBlank (Symbol 1)) :
    pow10L (m + n) l = pow10L m (pow10L n l) := by
  induction m with
  | zero => simp [pow10L]
  | succ m ih => simp only [pow10L, Nat.succ_add, ih]

lemma pow10R_add (m n : ℕ) (r : ListBlank (Symbol 1)) :
    pow10R (m + n) r = pow10R m (pow10R n r) := by
  induction m with
  | zero => simp [pow10R]
  | succ m ih => simp only [pow10R, Nat.succ_add, ih]

@[simp] lemma pow10L_zero (l : ListBlank (Symbol 1)) : pow10L 0 l = l := rfl
@[simp] lemma pow10R_zero (r : ListBlank (Symbol 1)) : pow10R 0 r = r := rfl

lemma pow10L_one (l : ListBlank (Symbol 1)) :
    pow10L 1 l = ListBlank.cons 𝟘 (ListBlank.cons 𝟙 l) := rfl
lemma pow10R_one (r : ListBlank (Symbol 1)) :
    pow10R 1 r = ListBlank.cons 𝟙 (ListBlank.cons 𝟘 r) := rfl

lemma pow10L_succ (n : ℕ) (l : ListBlank (Symbol 1)) :
    pow10L (n + 1) l = ListBlank.cons 𝟘 (ListBlank.cons 𝟙 (pow10L n l)) := rfl
lemma pow10R_succ (n : ℕ) (r : ListBlank (Symbol 1)) :
    pow10R (n + 1) r = ListBlank.cons 𝟙 (ListBlank.cons 𝟘 (pow10R n r)) := rfl

/-- Split one block off the *bottom* of a left power block. -/
lemma pow10L_succ_inner (n : ℕ) (l : ListBlank (Symbol 1)) :
    pow10L (n + 1) l = pow10L n (ListBlank.cons 𝟘 (ListBlank.cons 𝟙 l)) := by
  rw [pow10L_add n 1]; rfl

/-- Coq `lowerL_merge`: two adjacent blocks with no separator merge. -/
lemma lowerL_merge (x y : ℕ) (ys : List ℕ) :
    pow10L x (lowerL (y :: ys)) = lowerL ((x + y) :: ys) := by
  simp only [lowerL, pow10L_add]

/-- Coq `lowerL_nonempty`: on a nonempty list, `lowerL'` is `lowerL` with the
separator `1` on top. -/
lemma lowerL_nonempty {xs : List ℕ} (h : xs ≠ []) :
    lowerL' xs = ListBlank.cons 𝟙 (lowerL xs) := by
  cases xs with
  | nil => exact absurd rfl h
  | cons x xs => rfl

/-! ## Level 1: sweep lemmas -/

/-- Coq `goright_10`: `l |> (10)^n r -->* (10)^n l |> r` (state `B` crosses a
`(10)^n` block rightwards, two steps per block: `B1 → E0 → B`). -/
lemma goright_10 : ∀ (n : ℕ) (l r : ListBlank (Symbol 1)),
    atB l (pow10R n r) -[M]->* atB (pow10L n l) r
  | 0, _, _ => Machine.EvStep.refl
  | n + 1, l, r => by
      rw [pow10R_succ, pow10L_add n 1]
      show (⟨1, Tape.mk' l (ListBlank.cons 𝟙 (ListBlank.cons 𝟘 (pow10R n r)))⟩ : Config 4 1)
        -[M]->* atB (pow10L n (pow10L 1 l)) r
      evchain step_right_mk' gB1 _ _, step_right_mk' gE0 _ _
      exact goright_10 n (pow10L 1 l) r

/-- One `(10)(10)` pair crossed leftwards by state `C` in four steps
(`C0 → D1 → B0 → C1 → C`); the level-0 "go left (pass 10^2)" trace. -/
lemma goleft_pair (l r : ListBlank (Symbol 1)) :
    atC (pow10L 2 l) r -[M]->* atC l (pow10R 2 r) := by
  show headL 2 (ListBlank.cons 𝟘 (ListBlank.cons 𝟙 (ListBlank.cons 𝟘 (ListBlank.cons 𝟙 l)))) r
    -[M]->* atC l (ListBlank.cons 𝟙 (ListBlank.cons 𝟘 (ListBlank.cons 𝟙 (ListBlank.cons 𝟘 r))))
  rw [headL_cons]
  evsteps step_left_mk' gC0 _ _, step_left_mk' gD1 _ _, step_left_mk' gB0 _ _,
    step_left_head gC1 _ _

/-- Even-length pair sweep: `(10)^(2t) l <| r -->* l <| (10)^(2t) r`. -/
lemma goleft_pairs : ∀ (t : ℕ) (l r : ListBlank (Symbol 1)),
    atC (pow10L (2 * t) l) r -[M]->* atC l (pow10R (2 * t) r)
  | 0, _, _ => Machine.EvStep.refl
  | t + 1, l, r => by
      have h2 : 2 * (t + 1) = 2 + 2 * t := by ring
      have hr : pow10R 2 (pow10R (2 * t) r) = pow10R (2 * t) (pow10R 2 r) := by
        rw [← pow10R_add, ← pow10R_add, Nat.add_comm]
      rw [h2, pow10L_add 2 (2 * t), pow10R_add 2 (2 * t), hr]
      exact (goleft_pair _ r).trans (goleft_pairs t l _)

/-- Coq `goleft_even10`: for even `n`, `(10)^n l <| r -->* l <| (10)^n r`. -/
lemma goleft_even10 {n : ℕ} (hn : Even n) (l r : ListBlank (Symbol 1)) :
    atC (pow10L n l) r -[M]->* atC l (pow10R n r) := by
  obtain ⟨t, ht⟩ := hn
  rw [ht, show t + t = 2 * t by ring]
  exact goleft_pairs t l r

/-- Coq `goleft_odd10`: for even `n`,
`l 1 (10)^(n+1) <| r -->* l 1 0 1 (10)^n |> r` — the head passes the `n` even
blocks, turns around at the last block using the `1` separator
(`C0 → D1 → B1 → E1 → A0 → B`), and crosses back right. -/
lemma goleft_odd10 {n : ℕ} (hn : Even n) (l r : ListBlank (Symbol 1)) :
    atC (pow10L (n + 1) (ListBlank.cons 𝟙 l)) r -[M]->*
      atB (pow10L n (ListBlank.cons 𝟙 (ListBlank.cons 𝟘 (ListBlank.cons 𝟙 l)))) r := by
  rw [pow10L_succ_inner]
  refine (goleft_even10 hn _ r).trans ?_
  refine Machine.EvStep.trans ?_ (goright_10 n _ r)
  show headL 2 (ListBlank.cons 𝟘 (ListBlank.cons 𝟙 (ListBlank.cons 𝟙 l))) (pow10R n r)
    -[M]->* atB (ListBlank.cons 𝟙 (ListBlank.cons 𝟘 (ListBlank.cons 𝟙 l))) (pow10R n r)
  rw [headL_cons]
  evsteps step_left_mk' gC0 _ _, step_left_mk' gD1 _ _, step_right_mk' gB1 _ _,
    step_right_mk' gE1 _ _, step_right_mk' gA0 _ _

/-! ## Level-0 connectives -/

/-- Passing a `1` separator leftwards in state `C` (level-0 "go left (pass 1)"). -/
lemma pass_sep (x r : ListBlank (Symbol 1)) :
    atC (ListBlank.cons 𝟙 x) r -[M]-> atC x (ListBlank.cons 𝟙 r) := by
  rw [atC, headL_cons]
  exact step_left_head gC1 x r

/-- Turning around at the blank right edge (level-0 "go right (turn back)"):
`l |> 0∞ → l <| 0∞`. -/
lemma turn_blank (l : ListBlank (Symbol 1)) :
    atB l ∅ -[M]-> atC l ∅ := by
  have h := step_left_head (M := M) gB0d l (∅ : ListBlank (Symbol 1))
  rw [cons_zero_empty] at h
  exact h

/-! ## Level 2: rewriting `lower` lists -/

/-- Coq `goright_nonzero_step`:
`lowerL (y :: ys) |> lowerR' ((x+1) :: xs) -->* lowerL (x :: (y+1) :: ys) |> lowerR' xs`
(cross the separator and one `10`, converting them into `1 0 1` on the left,
then sweep the remaining `(10)^x`). -/
lemma goright_nonzero_step (x y : ℕ) (ys xs : List ℕ) :
    atB (lowerL (y :: ys)) (lowerR' ((x + 1) :: xs)) -[M]->*
      atB (lowerL (x :: (y + 1) :: ys)) (lowerR' xs) := by
  show atB (lowerL (y :: ys))
      (ListBlank.cons 𝟙 (ListBlank.cons 𝟙 (ListBlank.cons 𝟘 (pow10R x (lowerR' xs)))))
    -[M]->* _
  rw [atB]
  evchain step_right_mk' gB1 _ _, step_right_mk' gE1 _ _, step_right_mk' gA0 _ _
  have h := goright_10 x
    (ListBlank.cons 𝟙 (ListBlank.cons 𝟘 (ListBlank.cons 𝟙 (lowerL (y :: ys))))) (lowerR' xs)
  have hL : pow10L x (ListBlank.cons 𝟙 (ListBlank.cons 𝟘 (ListBlank.cons 𝟙 (lowerL (y :: ys)))))
      = lowerL (x :: (y + 1) :: ys) := by
    simp only [lowerL, lowerL', pow10L]
  rw [hL] at h
  exact h

/-- Coq `goright_nonzero_steps`: cross a whole run of nonzero exponents. -/
lemma goright_nonzero_steps : ∀ (xs : List ℕ), (∀ a ∈ xs, a ≠ 0) →
    ∀ (x y : ℕ) (ys zs : List ℕ),
    atB (lowerL (y :: ys)) (lowerR' (xs ++ (x + 1) :: zs)) -[M]->*
      atB (lowerL (x :: xs.reverse ++ (y + 1) :: ys)) (lowerR' zs)
  | [], _, x, y, ys, zs => by
      simpa using goright_nonzero_step x y ys zs
  | a :: xs, hnz, x, y, ys, zs => by
      obtain ⟨a', rfl⟩ : ∃ a', a = a' + 1 := by
        have := hnz a (by simp)
        exact ⟨a - 1, by omega⟩
      have h1 := goright_nonzero_step a' y ys (xs ++ (x + 1) :: zs)
      refine (by simpa using h1 :
        atB (lowerL (y :: ys)) (lowerR' ((a' + 1) :: xs ++ (x + 1) :: zs)) -[M]->* _).trans ?_
      have h2 := goright_nonzero_steps xs (fun b hb => hnz b (by simp [hb])) x a'
        ((y + 1) :: ys) zs
      refine h2.trans ?_
      have : x :: xs.reverse ++ (a' + 1) :: (y + 1) :: ys
          = x :: ((a' + 1) :: xs).reverse ++ (y + 1) :: ys := by
        simp
      rw [this]
      exact Machine.EvStep.refl

/-- Coq `goright_nonzero'`: ending at the blank right edge. -/
lemma goright_nonzero' {xs : List ℕ} (hxs : ∀ a ∈ xs, a ≠ 0) (x y : ℕ) (ys : List ℕ) :
    atB (lowerL (y :: ys)) (lowerR' (xs ++ [x + 1])) -[M]->*
      atB (lowerL (x :: xs.reverse ++ (y + 1) :: ys)) ∅ := by
  simpa [lowerR'] using goright_nonzero_steps xs hxs x y ys []

/-- Coq `goleft_even`: the head crosses a run of even exponents leftwards,
transferring them (reversed) onto the right side. -/
lemma goleft_even : ∀ (xs : List ℕ), (∀ a ∈ xs, Even a) →
    ∀ (l : List ℕ), l ≠ [] → ∀ (r : List ℕ),
    atC (lowerL (xs ++ l)) (lowerR' r) -[M]->*
      atC (lowerL l) (lowerR' (xs.reverse ++ r))
  | [], _, l, _, r => by simpa using Machine.EvStep.refl
  | x :: xs, hev, l, hl, r => by
      have hx : Even x := hev x (by simp)
      show atC (pow10L x (lowerL' (xs ++ l))) (lowerR' r) -[M]->* _
      refine (goleft_even10 hx _ _).trans ?_
      rw [lowerL_nonempty (by simp [hl] : xs ++ l ≠ [])]
      refine Machine.EvStep.step (pass_sep _ _) ?_
      have h2 := goleft_even xs (fun b hb => hev b (by simp [hb])) l hl (x :: r)
      have hR : ListBlank.cons 𝟙 (pow10R x (lowerR' r)) = lowerR' (x :: r) := rfl
      rw [hR]
      refine h2.trans ?_
      have : xs.reverse ++ x :: r = (x :: xs).reverse ++ r := by simp
      rw [this]
      exact Machine.EvStep.refl


/-! ### Small unfolding equalities -/

/-- Normalize list expressions to right-associated cons-normal form. -/
local syntax "list_norm" (Lean.Parser.Tactic.location)? : tactic
local macro_rules
  | `(tactic| list_norm $[$loc:location]?) =>
      `(tactic| simp only [List.cons_append, List.nil_append, List.append_nil,
          List.append_assoc, List.reverse_cons, List.reverse_reverse, List.reverse_nil,
          List.singleton_append] $[$loc:location]?)

@[simp] lemma lowerR'_nil : lowerR' [] = ∅ := rfl
lemma lowerR'_cons (x : ℕ) (xs : List ℕ) :
    lowerR' (x :: xs) = ListBlank.cons 𝟙 (pow10R x (lowerR' xs)) := rfl
lemma lowerL_cons (x : ℕ) (xs : List ℕ) : lowerL (x :: xs) = pow10L x (lowerL' xs) := rfl
lemma lowerL_zero_cons (xs : List ℕ) : lowerL (0 :: xs) = lowerL' xs := rfl
lemma lowerR_cons (x : ℕ) (xs : List ℕ) : lowerR (x :: xs) = pow10R x (lowerR' xs) := rfl

/-- The head block of `lowerL` splits off a separator (nonempty tail). -/
lemma lowerL_cons_cons (x y : ℕ) (ys : List ℕ) :
    lowerL (x :: y :: ys) = pow10L x (ListBlank.cons 𝟙 (lowerL (y :: ys))) := rfl

/-- The `1 0 1`-prefix regroups as a separator plus an incremented block. -/
lemma sep_block (z : ℕ) (zs : List ℕ) :
    ListBlank.cons 𝟙 (ListBlank.cons 𝟘 (ListBlank.cons 𝟙 (lowerL (z :: zs))))
      = lowerL' ((z + 1) :: zs) := rfl

/-- Absorbing a fresh `0 1` pair increments the head exponent. -/
lemma absorb_block (x : ℕ) (xs : List ℕ) :
    ListBlank.cons 𝟘 (ListBlank.cons 𝟙 (lowerL (x :: xs))) = lowerL ((x + 1) :: xs) := rfl

/-- An odd number splits as an even predecessor plus one. -/
private lemma odd_split {y : ℕ} (hy : Odd y) : ∃ y', Even y' ∧ y = y' + 1 := by
  obtain ⟨k, rfl⟩ := hy
  exact ⟨2 * k, ⟨k, by ring⟩, rfl⟩

/-! ### Level-0 turnaround segments (traces generated by `gen17.py`) -/

/-- `zero_*` turnaround at the left tape edge (3 steps: `C0 → D0 → A0`). -/
lemma zero_turn (r : ListBlank (Symbol 1)) :
    atC ∅ r -[M]->* atB (ListBlank.cons 𝟙 (ListBlank.cons 𝟙 ∅)) r := by
  show (⟨2, Tape.mk' ∅ (ListBlank.cons 𝟘 r)⟩ : Config 4 1) -[M]->* _
  evsteps step_left_edge gC0 _, step_right_mk' gD0 _ _, step_right_mk' gA0 _ _

/-- `overflow_*` turnaround at the left tape edge (17 steps), leaving
`lowerL [1, 1, 0, 0]` behind. -/
lemma overflow_turn (r : ListBlank (Symbol 1)) :
    atC (pow10L 1 ∅) r -[M]->* atB (lowerL [1, 1, 0, 0]) r := by
  show (⟨2, Tape.mk' (ListBlank.cons 𝟙 ∅) (ListBlank.cons 𝟘 r)⟩ : Config 4 1) -[M]->* _
  evsteps step_left_mk' gC0 _ _, step_left_edge gD1 _, step_left_edge gB0 _,
    step_left_edge gC0 _, step_right_mk' gD0 _ _, step_right_mk' gA0 _ _,
    step_left_mk' gB0 _ _, step_left_mk' gC1 _ _, step_left_edge gC1 _,
    step_left_edge gC0 _, step_right_mk' gD0 _ _, step_right_mk' gA0 _ _,
    step_right_mk' gB1 _ _, step_right_mk' gE1 _ _, step_right_mk' gA0 _ _,
    step_right_mk' gB1 _ _, step_right_mk' gE0 _ _

/-- Ending segment when the right side holds a lone `lowerR' [0]` separator
(3 steps: `B1 → E0 → B0`): the separator becomes a fresh `10` block on the
left, incrementing the head exponent. -/
lemma inc_O_end (l : ListBlank (Symbol 1)) :
    atB l (lowerR' [0]) -[M]->* atC (ListBlank.cons 𝟘 (ListBlank.cons 𝟙 l)) ∅ := by
  rw [show atC (ListBlank.cons 𝟘 (ListBlank.cons 𝟙 l)) ∅
      = (⟨2, Tape.mk' (ListBlank.cons 𝟙 l) (ListBlank.cons 𝟘 ∅)⟩ : Config 4 1) from
    headL_cons 2 𝟘 (ListBlank.cons 𝟙 l) ∅]
  show (⟨1, Tape.mk' l (ListBlank.cons 𝟙 ∅)⟩ : Config 4 1) -[M]->* _
  evchain step_right_mk' gB1 _ _, step_right_blank gE0d _, step_left_blank gB0d _
  simp only [cons_zero_empty]
  exact Machine.EvStep.refl

/-- Coq `goright_nonzero`: like `goright_nonzero'` but with a leading
separator-free block that merges into the first left exponent. -/
lemma goright_nonzero {ws : List ℕ} (hws : ∀ a ∈ ws, a ≠ 0) (x₀ w y : ℕ) (ys : List ℕ) :
    atB (lowerL (y :: ys)) (lowerR (x₀ :: (ws ++ [w + 1]))) -[M]->*
      atB (lowerL (w :: (ws.reverse ++ (x₀ + y + 1) :: ys))) ∅ := by
  rw [lowerR_cons]
  refine (goright_10 x₀ _ _).trans ?_
  rw [lowerL_merge]
  have h := goright_nonzero' (xs := ws) hws w (x₀ + y) ys
  simpa using h

/-! ### Level 2: the `increment`/`overflow`/`zero` moves -/

/-- Coq `increment_S_even`. -/
lemma increment_S_even {x : ℕ} {xs : List ℕ} {y z : ℕ} {zs : List ℕ}
    (hnz : ∀ a ∈ xs, a ≠ 0) (hev : ∀ a ∈ xs, Even a) (hx : Even (x + 1)) (hy : Odd y) :
    lower ((x + 1) :: (xs ++ y :: z :: zs)) -[M]->*
      lower (x :: (xs ++ y :: (z + 1) :: zs)) := by
  obtain ⟨y', hy', rfl⟩ := odd_split hy
  have h1 := goleft_even ((x + 1) :: xs)
    (by intro a ha; rcases List.mem_cons.1 ha with rfl | ha; exacts [hx, hev a ha])
    ((y' + 1) :: z :: zs) (by simp) []
  refine (by list_norm at h1 ⊢; exact h1 :
    lower ((x + 1) :: (xs ++ (y' + 1) :: z :: zs)) -[M]->*
      atC (lowerL ((y' + 1) :: z :: zs)) (lowerR' (xs.reverse ++ [x + 1]))).trans ?_
  rw [lowerL_cons_cons]
  refine (goleft_odd10 hy' _ _).trans ?_
  rw [sep_block, show pow10L y' (lowerL' ((z + 1) :: zs)) = lowerL (y' :: (z + 1) :: zs) from rfl]
  refine ((goright_nonzero' (xs := xs.reverse) (by simpa using hnz) x y'
    ((z + 1) :: zs)).trans ?_)
  list_norm
  exact Machine.EvStep.step (turn_blank _) Machine.EvStep.refl

/-- Coq `increment_S_odd`. -/
lemma increment_S_odd {x y : ℕ} {xs : List ℕ} (hx : Odd (x + 1)) :
    lower ((x + 1) :: y :: xs) -[M]->* lower (x :: (y + 1) :: xs) := by
  have hx' : Even x := by rcases hx with ⟨k, hk⟩; exact ⟨k, by omega⟩
  show atC (pow10L (x + 1) (ListBlank.cons 𝟙 (lowerL (y :: xs)))) ∅ -[M]->* _
  refine (goleft_odd10 hx' _ _).trans ?_
  rw [sep_block, show pow10L x (lowerL' ((y + 1) :: xs)) = lowerL (x :: (y + 1) :: xs) from rfl]
  exact Machine.EvStep.step (turn_blank _) Machine.EvStep.refl

/-- Coq `increment_O_odd`. -/
lemma increment_O_odd {x y : ℕ} {xs : List ℕ} (hx : Odd (x + 1)) :
    lower (0 :: (x + 1) :: y :: xs) -[M]->* lower ((x + 1) :: (y + 1) :: xs) := by
  have hx' : Even x := by rcases hx with ⟨k, hk⟩; exact ⟨k, by omega⟩
  show atC (ListBlank.cons 𝟙 (lowerL ((x + 1) :: y :: xs))) ∅ -[M]->* _
  refine Machine.EvStep.step (pass_sep _ _) ?_
  rw [show (ListBlank.cons 𝟙 ∅ : ListBlank (Symbol 1)) = lowerR' [0] from rfl,
    lowerL_cons_cons]
  refine (goleft_odd10 hx' _ _).trans ?_
  rw [sep_block, show pow10L x (lowerL' ((y + 1) :: xs)) = lowerL (x :: (y + 1) :: xs) from rfl]
  refine (inc_O_end _).trans ?_
  rw [absorb_block]
  exact Machine.EvStep.refl

/-- Coq `increment_O_even`. -/
lemma increment_O_even {x : ℕ} {xs : List ℕ} {y z : ℕ} {zs : List ℕ}
    (hnz : ∀ a ∈ xs, a ≠ 0) (hev : ∀ a ∈ xs, Even a) (hx : Even (x + 1)) (hy : Odd y) :
    lower (0 :: (x + 1) :: (xs ++ y :: z :: zs)) -[M]->*
      lower ((x + 1) :: (xs ++ y :: (z + 1) :: zs)) := by
  obtain ⟨y', hy', rfl⟩ := odd_split hy
  show atC (ListBlank.cons 𝟙 (lowerL ((x + 1) :: (xs ++ (y' + 1) :: z :: zs)))) ∅ -[M]->* _
  refine Machine.EvStep.step (pass_sep _ _) ?_
  rw [show (ListBlank.cons 𝟙 ∅ : ListBlank (Symbol 1)) = lowerR' [0] from rfl]
  have h1 := goleft_even ((x + 1) :: xs)
    (by intro a ha; rcases List.mem_cons.1 ha with rfl | ha; exacts [hx, hev a ha])
    ((y' + 1) :: z :: zs) (by simp) [0]
  refine (by list_norm at h1 ⊢; exact h1 :
    atC (lowerL ((x + 1) :: (xs ++ (y' + 1) :: z :: zs))) (lowerR' [0]) -[M]->*
      atC (lowerL ((y' + 1) :: z :: zs)) (lowerR' (xs.reverse ++ (x + 1) :: [0]))).trans ?_
  rw [lowerL_cons_cons]
  refine (goleft_odd10 hy' _ _).trans ?_
  rw [sep_block, show pow10L y' (lowerL' ((z + 1) :: zs)) = lowerL (y' :: (z + 1) :: zs) from rfl]
  refine (goright_nonzero_steps xs.reverse (by simpa using hnz) x y'
    ((z + 1) :: zs) [0]).trans ?_
  list_norm
  refine (inc_O_end _).trans ?_
  rw [absorb_block]
  exact Machine.EvStep.refl

/-- Coq `increment_O`. -/
lemma increment_O {xs : List ℕ} {y z : ℕ} {zs : List ℕ}
    (hnz : ∀ a ∈ xs, a ≠ 0) (hev : ∀ a ∈ xs, Even a) (hy : Odd y) :
    lower (0 :: (xs ++ y :: z :: zs)) -[M]->* lower (xs ++ y :: (z + 1) :: zs) := by
  match xs with
  | [] =>
      obtain ⟨y', _, rfl⟩ := odd_split hy
      simpa using increment_O_odd (x := y') (y := z) (xs := zs) (by omega)
  | x :: xs =>
      obtain ⟨x', rfl⟩ : ∃ x', x = x' + 1 := ⟨x - 1, by have := hnz x (by simp); omega⟩
      have h := increment_O_even (x := x') (xs := xs) (z := z) (zs := zs)
        (fun a ha => hnz a (List.mem_cons_of_mem _ ha))
        (fun a ha => hev a (List.mem_cons_of_mem _ ha)) (hev (x' + 1) List.mem_cons_self) hy
      list_norm at h ⊢
      exact h

/-- Coq `overflow_S`. -/
lemma overflow_S {x : ℕ} {xs : List ℕ} {y : ℕ}
    (hnz : ∀ a ∈ xs, a ≠ 0) (hev : ∀ a ∈ xs, Even a) (hx : Even (x + 1)) (hy : Odd y) :
    lower ((x + 1) :: (xs ++ [y])) -[M]->* lower (x :: (xs ++ [y + 1, 1, 0, 0])) := by
  obtain ⟨y', hy', rfl⟩ := odd_split hy
  have h1 := goleft_even ((x + 1) :: xs)
    (by intro a ha; rcases List.mem_cons.1 ha with rfl | ha; exacts [hx, hev a ha])
    [y' + 1] (by simp) []
  refine (by list_norm at h1 ⊢; exact h1 :
    lower ((x + 1) :: (xs ++ [y' + 1])) -[M]->*
      atC (lowerL [y' + 1]) (lowerR' (xs.reverse ++ [x + 1]))).trans ?_
  rw [show lowerL [y' + 1] = pow10L (y' + 1) ∅ from rfl, pow10L_succ_inner,
    show (ListBlank.cons 𝟘 (ListBlank.cons 𝟙 ∅) : ListBlank (Symbol 1)) = pow10L 1 ∅ from rfl]
  refine (goleft_even10 hy' _ _).trans ?_
  refine (overflow_turn _).trans ?_
  rw [show pow10R y' (lowerR' (xs.reverse ++ [x + 1]))
      = lowerR (y' :: (xs.reverse ++ [x + 1])) from rfl]
  have h2 := goright_nonzero (ws := xs.reverse) (by simpa using hnz) y' x 1 [1, 0, 0]
  refine (by list_norm at h2 ⊢; exact h2 :
    atB (lowerL [1, 1, 0, 0]) (lowerR (y' :: (xs.reverse ++ [x + 1]))) -[M]->*
      atB (lowerL (x :: (xs ++ (y' + 1 + 1) :: [1, 0, 0]))) ∅).trans ?_
  exact Machine.EvStep.step (turn_blank _) Machine.EvStep.refl

/-- Coq `overflow_O`. -/
lemma overflow_O {xs : List ℕ} {y : ℕ}
    (hnz : ∀ a ∈ xs, a ≠ 0) (hev : ∀ a ∈ xs, Even a) (hy : Odd y) :
    lower (0 :: (xs ++ [y])) -[M]->* lower (xs ++ [y + 1, 1, 0, 0]) := by
  obtain ⟨y', hy', rfl⟩ := odd_split hy
  have h1 := goleft_even (0 :: xs)
    (by intro a ha; rcases List.mem_cons.1 ha with rfl | ha; exacts [⟨0, rfl⟩, hev a ha])
    [y' + 1] (by simp) []
  refine (by list_norm at h1 ⊢; exact h1 :
    lower (0 :: (xs ++ [y' + 1])) -[M]->*
      atC (lowerL [y' + 1]) (lowerR' (xs.reverse ++ [0]))).trans ?_
  rw [show lowerL [y' + 1] = pow10L (y' + 1) ∅ from rfl, pow10L_succ_inner,
    show (ListBlank.cons 𝟘 (ListBlank.cons 𝟙 ∅) : ListBlank (Symbol 1)) = pow10L 1 ∅ from rfl]
  refine (goleft_even10 hy' _ _).trans ?_
  refine (overflow_turn _).trans ?_
  match xs with
  | [] =>
      show atB (lowerL (1 :: [1, 0, 0])) (pow10R y' (lowerR' [0])) -[M]->* _
      refine (goright_10 y' _ _).trans ?_
      rw [lowerL_merge]
      refine (inc_O_end _).trans ?_
      rw [absorb_block]
      show lower ((y' + 1 + 1) :: [1, 0, 0]) -[M]->* lower [y' + 1 + 1, 1, 0, 0]
      exact Machine.EvStep.refl
  | x :: xs =>
      obtain ⟨x', rfl⟩ : ∃ x', x = x' + 1 := ⟨x - 1, by have := hnz x (by simp); omega⟩
      have hrev : ((x' + 1) :: xs).reverse ++ [0] = xs.reverse ++ (x' + 1) :: [0] := by
        list_norm
      rw [hrev]
      show atB (lowerL (1 :: [1, 0, 0]))
        (pow10R y' (lowerR' (xs.reverse ++ (x' + 1) :: [0]))) -[M]->* _
      refine (goright_10 y' _ _).trans ?_
      rw [lowerL_merge]
      refine (goright_nonzero_steps xs.reverse
        (by simpa using fun a ha => hnz a (List.mem_cons_of_mem _ ha)) x' (y' + 1)
        [1, 0, 0] [0]).trans ?_
      list_norm
      refine (inc_O_end _).trans ?_
      rw [absorb_block]
      exact Machine.EvStep.refl

/-- Coq `zero_S`. -/
lemma zero_S {x : ℕ} {xs : List ℕ} {y : ℕ}
    (hnz : ∀ a ∈ xs, a ≠ 0) (hev : ∀ a ∈ xs, Even a) (hx : Even (x + 1)) (hy : Even y) :
    lower ((x + 1) :: (xs ++ [y])) -[M]->* lower (x :: (xs ++ [y + 1, 0, 0])) := by
  have h1 := goleft_even ((x + 1) :: xs)
    (by intro a ha; rcases List.mem_cons.1 ha with rfl | ha; exacts [hx, hev a ha])
    [y] (by simp) []
  refine (by list_norm at h1 ⊢; exact h1 :
    lower ((x + 1) :: (xs ++ [y])) -[M]->*
      atC (lowerL [y]) (lowerR' (xs.reverse ++ [x + 1]))).trans ?_
  rw [show lowerL [y] = pow10L y ∅ from rfl]
  refine (goleft_even10 hy _ _).trans ?_
  refine (zero_turn _).trans ?_
  refine (goright_10 y _ _).trans ?_
  rw [show pow10L y (ListBlank.cons 𝟙 (ListBlank.cons 𝟙 ∅)) = lowerL (y :: [0, 0]) from rfl]
  refine (goright_nonzero' (xs := xs.reverse) (by simpa using hnz) x y [0, 0]).trans ?_
  list_norm
  exact Machine.EvStep.step (turn_blank _) Machine.EvStep.refl

/-- Coq `zero_O`. -/
lemma zero_O {xs : List ℕ} {y : ℕ}
    (hnz : ∀ a ∈ xs, a ≠ 0) (hev : ∀ a ∈ xs, Even a) (hy : Even y) :
    lower (0 :: (xs ++ [y])) -[M]->* lower (xs ++ [y + 1, 0, 0]) := by
  have h1 := goleft_even (0 :: xs)
    (by intro a ha; rcases List.mem_cons.1 ha with rfl | ha; exacts [⟨0, rfl⟩, hev a ha])
    [y] (by simp) []
  refine (by list_norm at h1 ⊢; exact h1 :
    lower (0 :: (xs ++ [y])) -[M]->*
      atC (lowerL [y]) (lowerR' (xs.reverse ++ [0]))).trans ?_
  rw [show lowerL [y] = pow10L y ∅ from rfl]
  refine (goleft_even10 hy _ _).trans ?_
  refine (zero_turn _).trans ?_
  refine (goright_10 y _ _).trans ?_
  rw [show pow10L y (ListBlank.cons 𝟙 (ListBlank.cons 𝟙 ∅)) = lowerL (y :: [0, 0]) from rfl]
  match xs with
  | [] =>
      refine (inc_O_end _).trans ?_
      rw [absorb_block]
      exact Machine.EvStep.refl
  | x :: xs =>
      obtain ⟨x', rfl⟩ : ∃ x', x = x' + 1 := ⟨x - 1, by have := hnz x (by simp); omega⟩
      have hrev : ((x' + 1) :: xs).reverse ++ [0] = xs.reverse ++ (x' + 1) :: [0] := by
        list_norm
      rw [hrev]
      refine (goright_nonzero_steps xs.reverse
        (by simpa using fun a ha => hnz a (List.mem_cons_of_mem _ ha)) x' y
        [0, 0] [0]).trans ?_
      list_norm
      refine (inc_O_end _).trans ?_
      rw [absorb_block]
      exact Machine.EvStep.refl

end Deciders.Skelet.Skelet17
