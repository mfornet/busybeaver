/-
Translated cycler decider based on [transcripts](https://www.sligocki.com/2024/06/12/tm-transcripts.html)
-/
import Busybeaver.Basic
import Busybeaver.Reachability

namespace TM

abbrev TickingTape s := Turing.Tape (WithBot (Symbol s))

instance TickingTape.inhabited: Inhabited (TickingTape s) :=
  ⟨{ head := (default : Symbol s), left := default, right := default }⟩

structure TickingConfig (l s) where
  state : Label l
  tape : TickingTape s

instance TickingConfig.inhabited: Inhabited (TickingConfig l s) :=
  ⟨{state := default, tape := default}⟩

abbrev Tick (l s) := Label l × (WithBot (Symbol s))

section ToBase

/-
To convert a ticking tape to a normal tape, with use Turing.Tape.map with a "forgetting" operation.

We thus leverage the lemmas of Turing.Tape.move this way
-/

/- The "forgetting" pointed map -/
def unbot_pointed [Inhabited α]: Turing.PointedMap (WithBot α) α := {
  f := WithBot.unbot' default
  map_pt' := rfl
}

def TickingTape.forget (T: TickingTape s): Turing.Tape (Symbol s) :=
  T.map unbot_pointed

def TickingConfig.toConfig (C: TickingConfig l s): Config l s := {
  state := C.state,
  tape := C.tape.forget
}

variable {C: TickingConfig l s}

@[simp]
lemma TickingConfig.toConfig.state: C.toConfig.state = C.state := rfl

@[simp]
lemma TickingConfig.toConfig.head: C.toConfig.tape.head = WithBot.unbot' default C.tape.head := rfl

end ToBase

section PrettyPrint
open Std.Format Lean

private def right_repr [Repr α] [Inhabited α] (l: Turing.ListBlank α) (bound: ℕ): List Format := match bound with
| 0 => []
| n + 1 => repr l.head :: (right_repr l.tail n)

private def left_repr [Repr α] [Inhabited α] (l: Turing.ListBlank α) (bound: ℕ): List Format := match bound with
| 0 => []
| n + 1 => left_repr l.tail n ++ [repr l.head]

instance: Repr (TickingConfig l s) := ⟨λ cfg _ ↦
  Std.Format.joinSep (left_repr cfg.tape.left 10) " " ++ s!" {cfg.state}>{repr cfg.tape.head} " ++ Std.Format.joinSep (right_repr cfg.tape.right 10) " "⟩

end PrettyPrint


def step_tick (M: Machine l s) (C: TickingConfig l s): Option (TickingConfig l s × Tick l s) :=
  let unboted: Symbol s := (WithBot.unbot' default C.tape.head)
  match M C.state unboted with
  | .halt => .none
  | .next sym' dir lab' =>
    .some ({state := lab', tape := (C.tape.write ↑sym').move dir }, (C.state, unboted))

namespace TReach

notation A " t-[" M ":" T "]-> " B => step_tick M A = Option.some (B, T)

inductive MultiTStep (M: Machine l s): TickingConfig l s → TickingConfig l s → List (Tick l s) → Prop
| refl C : MultiTStep M C C []
| step A B C t L : (A t-[M:t]-> B) → MultiTStep M B C L → MultiTStep M A C (t :: L)

notation A " t-[" M ":" L "]->> " B => MultiTStep M A B L

lemma single_step {A B: TickingConfig l s} (h: A t-[M : t]-> B): A.toConfig -[M]-> B.toConfig :=
by {
  simp [step_tick] at h
  split at h
  · simp_all
  rename_i heq
  simp at h
  obtain ⟨hB, _⟩ := h
  simp [Machine.step]
  split
  · rename_i heq'
    rw [heq] at heq'
    cases heq'
  rename_i heq'
  rw [heq] at heq'
  cases heq'
  simp
  rw [← hB]
  simp [TickingConfig.toConfig, TickingTape.forget, Turing.Tape.map_move]
  congr
}

lemma MultiTStep.to_multistep (h: A t-[M : L]->> B): A.toConfig -[M]{L.length}-> B.toConfig :=
by induction h with
| refl => exact .refl
| step A B C t L hAB _ IH => exact Machine.Multistep.succ (single_step hAB) IH
