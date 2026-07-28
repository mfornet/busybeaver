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
import Busybeaver.Deciders.Skelet.Skelet10
import Busybeaver.Deciders.Skelet.Skelet15
import Busybeaver.Deciders.Skelet.Skelet17
import Busybeaver.Deciders.Skelet.Skelet26
import Busybeaver.Deciders.Skelet.Skelet33
import Busybeaver.Deciders.Skelet.Skelet34
import Busybeaver.Deciders.Skelet.Skelet35
import Busybeaver.Deciders.Skelet.Skelet1Backend
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

These theorems carry the real mathematical content. Unlike a single
`∀ M, ¬M.halts` placeholder (which is *false* as stated, since halting BB(5)
machines exist), each proves a statement about one specific machine. The proofs
are imported from the individual `Deciders.Skelet` modules.
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
theorem sporadicMachine5_nonHalting
    (backend : Deciders.Skelet.Skelet1.ProofBackend) :
    ¬ sporadicMachine5.halts init := by
  have hM : sporadicMachine5 = Deciders.Skelet.Skelet1.M := by
    apply Machine.ext
    intro lab sym
    decide +revert
  rw [hM]
  simpa only [init] using backend.nonhalt

def sporadicMachine6 : Machine 4 1 := Deciders.Skelet.Skelet10.M
theorem sporadicMachine6_nonHalting : ¬ sporadicMachine6.halts init :=
  Deciders.Skelet.Skelet10.nonHalting

def sporadicMachine7 : Machine 4 1 := Deciders.Skelet.Skelet15.M
theorem sporadicMachine7_nonHalting : ¬ sporadicMachine7.halts init :=
  Deciders.Skelet.Skelet15.nonHalting

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

/-- Backend-independent identifiers for the sporadic registry.  Table keys and
proof-carrying certificates are both derived from this one ordered list. -/
inductive SporadicId where
  | s0 | s1 | s2 | s3 | s4 | s5 | s6 | s7 | s8 | s9 | s10 | s11 | s12
deriving DecidableEq, Repr

def SporadicId.all : List SporadicId :=
  [.s0, .s1, .s2, .s3, .s4, .s5, .s6, .s7, .s8, .s9, .s10, .s11, .s12]

def SporadicId.machine : SporadicId → Machine 4 1
  | .s0 => sporadicMachine0
  | .s1 => sporadicMachine1
  | .s2 => sporadicMachine2
  | .s3 => sporadicMachine3
  | .s4 => sporadicMachine4
  | .s5 => sporadicMachine5
  | .s6 => sporadicMachine6
  | .s7 => sporadicMachine7
  | .s8 => sporadicMachine8
  | .s9 => sporadicMachine9
  | .s10 => sporadicMachine10
  | .s11 => sporadicMachine11
  | .s12 => sporadicMachine12

theorem SporadicId.nonHalting
    (backend : Deciders.Skelet.Skelet1.ProofBackend) :
    (id : SporadicId) → ¬ id.machine.halts init
  | .s0 => sporadicMachine0_nonHalting
  | .s1 => sporadicMachine1_nonHalting
  | .s2 => sporadicMachine2_nonHalting
  | .s3 => sporadicMachine3_nonHalting
  | .s4 => sporadicMachine4_nonHalting
  | .s5 => sporadicMachine5_nonHalting backend
  | .s6 => sporadicMachine6_nonHalting
  | .s7 => sporadicMachine7_nonHalting
  | .s8 => sporadicMachine8_nonHalting
  | .s9 => sporadicMachine9_nonHalting
  | .s10 => sporadicMachine10_nonHalting
  | .s11 => sporadicMachine11_nonHalting
  | .s12 => sporadicMachine12_nonHalting

def SporadicId.cert
    (backend : Deciders.Skelet.Skelet1.ProofBackend)
    (id : SporadicId) : SporadicCert :=
  ⟨id.machine, id.nonHalting backend⟩

/-- The certified sporadic holdouts for a selected Skelet #1 backend. -/
def sporadicCerts
    (backend : Deciders.Skelet.Skelet1.ProofBackend) : List SporadicCert :=
  SporadicId.all.map (SporadicId.cert backend)

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

def EntryDecider.run
    (backend : Deciders.Skelet.Skelet1.ProofBackend)
    (d : EntryDecider) (M : Machine 4 1) : HaltM M Unit :=
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
      sporadicResult (sporadicCerts backend) M
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

def decider
    (backend : Deciders.Skelet.Skelet1.ProofBackend)
    (entries : List Entry) (M : Machine 4 1) : HaltM M Unit :=
  match findEntry? entries M with
  | none => .unknown ()
  | some d => d.run backend M

def tableDecider
    (backend : Deciders.Skelet.Skelet1.ProofBackend)
    (table : Table) (M : Machine 4 1) : HaltM M Unit :=
  match findInTable? table M with
  | none => .unknown ()
  | some d => d.run backend M

def emptyEntries : List Entry := []

def sporadicEntries : List Entry :=
  SporadicId.all.map fun id => (machineCode id.machine, .sporadic)

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

The transform preserves non-halting, so a non-halting verdict for `toNF M`
transfers to `M`; `toNF_equiv` and `toNF_nonHalting` below establish that
transfer.
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
def nfTableDecider
    (backend : Deciders.Skelet.Skelet1.ProofBackend)
    (table : Table) (M : Machine 4 1) : HaltM M Unit :=
  match findInTable? table (toNF M) with
  | some (.halt _) => .unknown ()
  | some d =>
      match d.run backend (toNF M) with
      | .loops_prf hnh => .loops_prf (toNF_nonHalting hnh)
      | _ => .unknown ()
  | none => .unknown ()

end Deciders.BB5Table
