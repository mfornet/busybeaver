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

universe u v

namespace TM

-- TODO: Move to Busybeaver/Model/Basic.lean and still import it from here

class Model (Machine : Type u) where
  /-- Type of control states of the machine. -/
  State : Type v
  /-- Type of tape symbols of the machine. -/
  Symbol : Type v
  /-- Decidable equality on states, used throughout executable and proof code. -/
  instDecEqState : DecidableEq State
  /-- Decidable equality on symbols, used throughout executable and proof code. -/
  instDecEqSymbol : DecidableEq Symbol
  /-- Distinguished blank symbol used to build default tapes/configurations. -/
  instBlankSymbol : BlankSymbol Symbol
  /-- Distinguished initial state used to build the default starting configuration. -/
  instInitialState : InitialState State
  /--
  One-step machine semantics in "statement form".

  This is the proof-friendly interface: given the current state and head symbol, return:
  - the number of underlying base steps accounted for by this transition, and
  - either `halt` or the next write/move/jump action.

  Most model instances define this directly from their transition function.
  -/
  stmt : Machine → TM.Generic.Config State Symbol → Nat × GStmt State Symbol
  /--
  Extensionality principle for `stmt`: it depends only on the current control state and head symbol.

  This is the key determinism fact used by transcript-style proofs and wrapper machines. In most
  concrete machines it is proved by `rw` on the equalities and reflexivity.
  -/
  stmt_eq_of_state_head_eq :
    ∀ M A B,
      A.state = B.state →
      A.tape.head = B.tape.head →
      stmt M A = stmt M B
  /--
  Executable one-step semantics of the machine.

  This is what evaluation-oriented code runs. It may be defined directly, but most instances keep it
  definitionally aligned with `stmt` so proofs can move easily between computation and statement form.
  -/
  step : Machine → TM.Generic.Config State Symbol → TM.StepResult (TM.Generic.Config State Symbol)
  /--
  Compatibility between `step` and `stmt`.

  This states that `step` is exactly the operational interpretation of `stmt`: `halt` stops in the
  current configuration, while `next sym dir state` writes, moves, and updates the control state.
  Most proofs about reachability reduce `step` using this lemma.
  -/
  step_stmt :
    ∀ M C, step M C =
      match stmt M C with
      | (dn, .halt) => ⟨dn, .halted C⟩
      | (dn, .next sym dir state) => ⟨dn, .continue { state, tape := C.tape.write sym |>.move dir }⟩
  /--
  Zero base steps occur exactly on halting transitions.

  This rules out "silent" non-halting transitions and is used in bounded-step arguments and
  conversions between high-level and base-step reachability.
  -/
  step_zero_iff :
    ∀ M C, (step M C).baseSteps = 0 ↔ (step M C).outcome = .halted C

attribute [reducible, instance] Model.instDecEqState Model.instDecEqSymbol
attribute [reducible, instance] Model.instBlankSymbol Model.instInitialState

namespace Model

abbrev Config (M : Type _) [TM.Model M] :=
  TM.Generic.Config (TM.Model.State M) (TM.Model.Symbol M)

variable {M : Type _} [TM.Model M]

instance Config.Inhabited : Inhabited (Config M) := ⟨⟨initial, default⟩⟩

def eval (m : M) (bound : Nat) (orig : Config M) :
    Option (Config M) :=
  match bound with
  | 0 => orig
  | n + 1 =>
      match TM.Model.step m orig with
      | ⟨_, .continue next⟩ => eval m n next
      | ⟨_, .halted _⟩ => none

def LastState (m : M) (C : Config M) : Bool :=
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
