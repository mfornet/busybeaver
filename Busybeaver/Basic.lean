import Mathlib.Computability.TuringMachine.StackTuringMachine
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Sort
import Busybeaver.TuringExt

class InitialState (State : Type _) where
  initial : State

export InitialState (initial)

class BlankSymbol (Symbol : Type _) where
  blank : Symbol

export BlankSymbol (blank)

instance {Symbol : Type _} [BlankSymbol Symbol] : Inhabited Symbol := ⟨blank⟩

inductive GStmt (State Symbol : Type _)
| halt
| next : Symbol → Turing.Dir → State → GStmt State Symbol
deriving DecidableEq

instance : Inhabited (GStmt State Symbol) := ⟨.halt⟩

namespace TM

namespace Generic

structure Config (State Symbol : Type _) [BlankSymbol Symbol] where
  state : State
  tape : Turing.Tape Symbol

instance [BlankSymbol Symbol] [DecidableEq State] [DecidableEq Symbol] :
    DecidableEq (Config State Symbol) := by
  unfold DecidableEq
  intro a b
  obtain ⟨sa, ta⟩ := a
  obtain ⟨sb, tb⟩ := b
  simp_all
  apply instDecidableAnd

end Generic

inductive StepOutcome (Cfg : Type _)
| continue : Cfg → StepOutcome Cfg
| halted : Cfg → StepOutcome Cfg
deriving DecidableEq

structure StepResult (Cfg : Type _) where
  baseSteps : Nat
  outcome : StepOutcome Cfg

end TM

universe u v w

namespace TM

-- TODO: Move to Busybeaver/Model/Basic.lean and still import it from

class Model (Machine : Type u) where
  State : Type v
  Symbol : Type w
  instDecEqState : DecidableEq State
  instDecEqSymbol : DecidableEq Symbol
  instBlankSymbol : BlankSymbol Symbol
  instInitialState : InitialState State
  step : Machine → TM.Generic.Config State Symbol → TM.StepResult (TM.Generic.Config State Symbol)
  step_zero_iff :
    ∀ M C, (step M C).baseSteps = 0 ↔ (step M C).outcome = .halted C

attribute [reducible, instance] Model.instDecEqState Model.instDecEqSymbol
attribute [reducible, instance] Model.instBlankSymbol Model.instInitialState

namespace Model

abbrev Config (M : Type _) [TM.Model M] :=
  TM.Generic.Config (TM.Model.State M) (TM.Model.Symbol M)

def init (M : Type _) [TM.Model M] : Config M :=
  ⟨initial, default⟩

def eval (M : Type _) [TM.Model M] (m : M) (bound : Nat) (orig : Config M) :
    Option (Config M) :=
  match bound with
  | 0 => orig
  | n + 1 =>
      match TM.Model.step m orig with
      | ⟨_, .continue next⟩ => eval M m n next
      | ⟨_, .halted _⟩ => none

def LastState {M : Type _} [TM.Model M] (m : M) (C : Config M) : Bool :=
  match TM.Model.step m C with
  | ⟨_, .halted _⟩ => true
  | ⟨_, .continue _⟩ => false

end Model

end TM

abbrev Label (l: ℕ) := Fin (l + 1)
instance: Fintype (Label l) := inferInstance
instance: LE (Label l) := inferInstance
instance: Repr (Label l) := inferInstance
instance: Inhabited (Label l) := inferInstance
instance : InitialState (Label l) := ⟨default⟩

abbrev Symbol (s: ℕ) := Fin (s + 1)
instance: Fintype (Symbol s) := inferInstance
instance: LE (Symbol s) := inferInstance
instance: Repr (Symbol s) := inferInstance
instance: Inhabited (Symbol s) := inferInstance
instance : BlankSymbol (Symbol s) := ⟨default⟩

@[simp]
lemma Finset.mem_fold_union [DecidableEq α] [DecidableEq β] {f: α → Finset β} {S: Finset α} {b : β}:
  b ∈ Finset.fold Union.union ∅ f S ↔ ∃ a ∈ S, b ∈ f a :=
by induction S using Finset.induction with
| empty => simp
| @insert A S _ IH => simp [IH]
