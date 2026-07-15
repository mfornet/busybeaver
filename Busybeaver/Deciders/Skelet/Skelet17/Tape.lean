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

end Deciders.Skelet.Skelet17
