import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Cases
import Busybeaver.Deciders.Skelet.EvStepTactics
import Busybeaver.TM.Table.Parse
import Busybeaver.TM.Table.ClosedSet
import Busybeaver.Deciders.Skelet.ShiftOverflowBins
import Busybeaver.Deciders.Skelet.TapeCalc

open TM.Table

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
(mirroring the Coq `destruct`) are all discharged.
-/
namespace Deciders.Skelet.Skelet10
open Turing

/-- Skelet #10's transition table. -/
abbrev M : Machine 4 1 := mach["1RB0RA_0LC1RA_1RE1LD_1LC0LD_---0RB"]

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

end Deciders.Skelet.Skelet10
