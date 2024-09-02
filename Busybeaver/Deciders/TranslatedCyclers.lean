/-
Translated cycler decider based on [transcripts](https://www.sligocki.com/2024/06/12/tm-transcripts.html)
-/
import Busybeaver.Basic
import Busybeaver.Reachability

namespace TM

abbrev TickingTape s := Turing.Tape (WithBot (Symbol s))

instance TickingTape.inhabited: Inhabited (TickingTape s) :=
  ⟨{ head := (default : Symbol s), left := default, right := default }⟩

abbrev LawfulTT s := { T: TickingTape s // T.head ≠ ⊥ }

instance LawfulTT.inhabited: Inhabited (LawfulTT s) :=
  ⟨default, by simp [default]⟩

structure TickingConfig (l s) where
  state : Label l
  tape : LawfulTT s

instance TickingConfig.inhabited: Inhabited (TickingConfig l s) :=
  ⟨{state := default, tape := default}⟩

abbrev Tick (l s) := Label l × (WithBot (Symbol s))

def TickingTape.toLawful (T: TickingTape s): LawfulTT s := match h: T.head with
| ⊥ => ⟨{T with head := (default: Symbol s)}, by simp⟩
| some sym => ⟨T, by simp [h]⟩


section PrettyPrint
open Std.Format Lean

private def right_repr [Repr α] [Inhabited α] (l: Turing.ListBlank α) (bound: ℕ): List Format := match bound with
| 0 => []
| n + 1 => repr l.head :: (right_repr l.tail n)

private def left_repr [Repr α] [Inhabited α] (l: Turing.ListBlank α) (bound: ℕ): List Format := match bound with
| 0 => []
| n + 1 => left_repr l.tail n ++ [repr l.head]

instance: Repr (TickingConfig l s) := ⟨λ cfg _ ↦
  Std.Format.joinSep (left_repr cfg.tape.val.left 10) " " ++ s!" {cfg.state}>{repr cfg.tape.val.head} " ++ Std.Format.joinSep (right_repr cfg.tape.val.right 10) " "⟩

end PrettyPrint


def step_tick (M: Machine l s) (C: TickingConfig l s): Option (TickingConfig l s × Tick l s) :=
  match hM: C.tape.val.head with
  | none => by {
    obtain ⟨Cs, Ct, CtH⟩ := C
    simp at hM
    contradiction
  }
  | some sym => match M C.state sym with
    | .halt => .none
    | .next sym' dir lab' =>
      let t := (C.tape.val.write ↑sym').move dir
      .some ({state := lab', tape := TickingTape.toLawful t }, (C.state, t.head))
