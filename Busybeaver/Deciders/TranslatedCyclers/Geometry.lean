/-
Transcript geometry for translated cyclers.

This file computes the head movement determined by a transcript together with the wrapped machine.
The transcript only stores `(state, symbol)`, so directions and writes are recovered from the
machine statement determined by that pair.
-/
import Busybeaver.Deciders.TranslatedCyclers.Basic

namespace Deciders.TranslatedCyclers

open TM.Model

variable {BM : Type _} [TM.Model BM]

/-- A dummy config whose state/head match the transcript tick. -/
def configOfTick (t : Tick BM) : TickingConfig BM := {
  state := t.1
  tape := (default : Turing.Tape (TickSymbol BM)).write t.2
}

/-- The wrapped statement determined by a transcript tick. -/
def stmtOfTick (m : TickingMachine BM) (t : Tick BM) :
    Nat × GStmt (TM.Model.State BM) (TickSymbol BM) :=
  TM.Model.stmt m (configOfTick t)

/-- The move direction determined by a non-halting transcript tick. -/
def dirOfTick (m : TickingMachine BM) (t : Tick BM) : Turing.Dir :=
  match stmtOfTick m t with
  | (_, .halt) => .right
  | (_, .next _ dir _) => dir

/-- The written symbol determined by a non-halting transcript tick. -/
def writeOfTick (m : TickingMachine BM) (t : Tick BM) : TickSymbol BM :=
  match stmtOfTick m t with
  | (_, .halt) => t.2
  | (_, .next sym _ _) => sym

def shiftDelta : Turing.Dir → Int
  | .left => -1
  | .right => 1

/-- Head positions before each step, relative to the initial head position. -/
def headPosBefore (m : TickingMachine BM) : List (Tick BM) → List Int
  | [] => []
  | t :: L => 0 :: (headPosBefore m L).map (fun i => shiftDelta (dirOfTick m t) + i)

/-- Net head displacement after executing the transcript. -/
def netShift (m : TickingMachine BM) : List (Tick BM) → Int
  | [] => 0
  | t :: L => shiftDelta (dirOfTick m t) + netShift m L

abbrev finalOffset (m : TickingMachine BM) (L : List (Tick BM)) : Int := netShift m L

def visitedOffsets (m : TickingMachine BM) (L : List (Tick BM)) : Finset Int :=
  (headPosBefore m L).toFinset

lemma headPosBefore_length (m : TickingMachine BM) (L : List (Tick BM)) :
    (headPosBefore m L).length = L.length := by
  induction L with
  | nil =>
      simp [headPosBefore]
  | cons t L IH =>
      simp [headPosBefore, IH]

lemma mem_visitedOffsets_iff {m : TickingMachine BM} {L : List (Tick BM)} {i : Int} :
    i ∈ visitedOffsets m L ↔ i ∈ headPosBefore m L := by
  simp [visitedOffsets]

lemma visitedOffsets_finite (m : TickingMachine BM) (L : List (Tick BM)) :
    (visitedOffsets m L : Set Int).Finite := by
  exact Finset.finite_toSet (visitedOffsets m L)

lemma netShift_append (m : TickingMachine BM) (L L' : List (Tick BM)) :
    netShift m (L ++ L') = netShift m L + netShift m L' := by
  induction L with
  | nil =>
      simp [netShift]
  | cons t L IH =>
      simp [netShift, IH, add_assoc]

lemma headPosBefore_append (m : TickingMachine BM) (L L' : List (Tick BM)) :
    headPosBefore m (L ++ L') =
      headPosBefore m L ++ (headPosBefore m L').map (fun i => netShift m L + i) := by
  induction L with
  | nil =>
      simp [headPosBefore, netShift]
  | cons t L IH =>
      simp [headPosBefore, IH, netShift, List.map_map, add_comm]

lemma headPosBefore_getLast?_eq_netShift {m : TickingMachine BM} {L : List (Tick BM)} {t : Tick BM} :
    (headPosBefore m (L ++ [t])).getLast? = some (netShift m L) := by
  rw [headPosBefore_append]
  simp [headPosBefore]

/--
Offsets revisited by the next copy of `L` are exactly those whose `netShift`-translate was visited
by the previous copy.
-/
lemma visitedOffsets_shifted_overlap {m : TickingMachine BM} {L : List (Tick BM)} {i : Int} :
    i ∈ visitedOffsets m L ∧ i - netShift m L ∈ visitedOffsets m L ↔
      i ∈ visitedOffsets m L ∧ ∃ j ∈ visitedOffsets m L, i = netShift m L + j := by
  constructor
  · intro h
    refine ⟨h.1, i - netShift m L, h.2, ?_⟩
    omega
  · intro h
    rcases h with ⟨hi, j, hj, rfl⟩
    constructor
    · exact hi
    · simpa using hj

end Deciders.TranslatedCyclers
