import Busybeaver.Deciders.TranslatedCyclers.Geometry

namespace Deciders.TranslatedCyclers

open TM.Model

variable {BM : Type _} [TM.Model BM]

abbrev PartialTape (BM : Type _) [TM.Model BM] := Int → Option (TickSymbol BM)

namespace PartialTape

/-- A tape models a partial tape when it agrees on every known offset. -/
def Models (T : Turing.Tape (TickSymbol BM)) (P : PartialTape BM) : Prop :=
  ∀ i s, P i = some s → T.nth i = s

/-- Reindex a partial tape after shifting the head by `k`. -/
def shift (k : Int) (P : PartialTape BM) : PartialTape BM :=
  fun i => P (i + k)

/-- Right-biased union of partial tape information. -/
def merge (P Q : PartialTape BM) : PartialTape BM :=
  fun i => match Q i with | some s => some s | none => P i

def singleton (i : Int) (s : TickSymbol BM) : PartialTape BM :=
  fun j => if j = i then some s else none

/-- Drop any information about the current head position. -/
def eraseHead (P : PartialTape BM) : PartialTape BM :=
  fun i => if i = 0 then none else P i

/--
Pull back a next-step partial tape through one wrapped ticking step.

Cells away from the current head are reindexed across the move. Information about the current head
cell is dropped because that cell is overwritten by the step itself.
-/
def preStep (m : TickingMachine BM) (t : Tick BM) (P : PartialTape BM) : PartialTape BM :=
  eraseHead (shift (-shiftDelta (dirOfTick m t)) P)

lemma models_shift {T : Turing.Tape (TickSymbol BM)} {P : PartialTape BM}
    (h : Models T P) :
    Models T (shift 0 P) := by
  intro i s hs
  exact h i s (by simpa [shift] using hs)

lemma models_merge_left {T : Turing.Tape (TickSymbol BM)} {P Q : PartialTape BM}
    (hP : Models T P) (hQ : Models T Q) :
    Models T (merge P Q) := by
  intro i s hs
  unfold merge at hs
  cases hqi : Q i with
  | none =>
      exact hP i s (by simpa [hqi] using hs)
  | some t =>
      have hts : t = s := by
        have : some t = some s := by simpa [hqi] using hs
        injection this with hts
      subst hts
      exact hQ i t hqi

lemma models_singleton {T : Turing.Tape (TickSymbol BM)} {i : Int} {s : TickSymbol BM}
    (h : T.nth i = s) :
    Models T (singleton (BM := BM) i s) := by
  intro j s' hs
  unfold singleton at hs
  by_cases hij : j = i
  · simp [hij] at hs
    subst hij
    subst hs
    simpa using h
  · simp [hij] at hs

lemma shift_apply (k : Int) (P : PartialTape BM) (i : Int) :
    shift k P i = P (i + k) := rfl

lemma eraseHead_apply (P : PartialTape BM) (i : Int) :
    eraseHead P i = (if i = 0 then none else P i) := rfl

lemma preStep_apply (m : TickingMachine BM) (t : Tick BM) (P : PartialTape BM) (i : Int) :
    preStep m t P i =
      if i = 0 then none else P (i - shiftDelta (dirOfTick m t)) := by
  unfold preStep eraseHead shift
  by_cases hi : i = 0
  · simp [hi]
  · simp [hi, sub_eq_add_neg]

lemma merge_eq_none {P Q : PartialTape BM} {i : Int} :
    merge P Q i = none ↔ Q i = none ∧ P i = none := by
  unfold merge
  cases Q i <;> simp

lemma merge_eq_some {P Q : PartialTape BM} {i : Int} {w : TickSymbol BM} :
    merge P Q i = some w ↔ Q i = some w ∨ (Q i = none ∧ P i = some w) := by
  unfold merge
  cases Q i <;> simp

lemma singleton_eq_none {i j : Int} {s : TickSymbol BM} :
    singleton i s j = none ↔ j ≠ i := by
  unfold singleton
  by_cases h : j = i <;> simp [h]

end PartialTape

-- TODO: Reverse notation and signature of Models, the partial tape models the full tape, not the other way around.
--       Change this notation to be P ⊨ T and use PartialTape.Models P T
notation T " ⊨ " P => PartialTape.Models T P

end Deciders.TranslatedCyclers
