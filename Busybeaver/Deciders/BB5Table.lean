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
theorem sporadicMachine1_nonHalting : ¬ sporadicMachine1.halts init := by
  sorry

def sporadicMachine2 : Machine 4 1 := mach["1RB1RE_1LC1RB_0RA0LD_1LB1LD_---0RA"]
theorem sporadicMachine2_nonHalting : ¬ sporadicMachine2.halts init := by
  sorry

def sporadicMachine3 : Machine 4 1 := mach["1RB1LA_0LC0RE_---1LD_1RA0LC_1RA1RE"]
theorem sporadicMachine3_nonHalting : ¬ sporadicMachine3.halts init := by
  sorry

def sporadicMachine4 : Machine 4 1 := mach["1RB1LA_0LC0RE_---1LD_1LA0LC_1RA1RE"]
theorem sporadicMachine4_nonHalting : ¬ sporadicMachine4.halts init := by
  sorry

def sporadicMachine5 : Machine 4 1 := mach["1RB1RD_1LC0RC_1RA1LD_0RE0LB_---1RC"]
theorem sporadicMachine5_nonHalting : ¬ sporadicMachine5.halts init := by
  sorry

def sporadicMachine6 : Machine 4 1 := mach["1RB0RA_0LC1RA_1RE1LD_1LC0LD_---0RB"]
theorem sporadicMachine6_nonHalting : ¬ sporadicMachine6.halts init := by
  sorry

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
