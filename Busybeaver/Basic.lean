import Mathlib.Computability.TuringMachine
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Sort
import Busybeaver.TuringExt

abbrev Label (l: ℕ) := Fin (l + 1)
instance: Fintype (Label l) := inferInstance
instance: LE (Label l) := inferInstance
instance: Repr (Label l) := inferInstance
instance: Inhabited (Label l) := inferInstance

abbrev Symbol (s: ℕ) := Fin (s + 1)
instance: Fintype (Symbol s) := inferInstance
instance: LE (Symbol s) := inferInstance
instance: Repr (Symbol s) := inferInstance
instance: Inhabited (Symbol s) := inferInstance

namespace TM

section Defs
inductive Stmt (l s: ℕ)
| halt
| next: Symbol s → Turing.Dir → Label l → Stmt l s
deriving DecidableEq

instance: Inhabited $ Stmt l s := ⟨.halt⟩

def Machine (l s: ℕ):= Label l → Symbol s → Stmt l s

structure Config (l s: ℕ) [Inhabited $ Symbol s] where
  state: Label l
  tape: Turing.Tape (Symbol s)

end Defs

instance: DecidableEq (Config l s) := by {
  unfold DecidableEq
  intro a b
  obtain ⟨sa, ta⟩ := a
  obtain ⟨sb, tb⟩ := b
  simp_all
  apply instDecidableAnd
}

variable {l s: ℕ }

section PrettyPrint
open Std.Format Lean

private def right_repr (l: Turing.ListBlank (Symbol s)) (bound: ℕ): List Format := match bound with
| 0 => []
| n + 1 => repr l.head :: (right_repr l.tail n)

private def left_repr (l: Turing.ListBlank (Symbol s)) (bound: ℕ): List Format := match bound with
| 0 => []
| n + 1 => left_repr l.tail n ++ [repr l.head]

-- TODO: maybe a smarter way to define it will be needed
instance: Repr (Config l s) := ⟨λ cfg _ ↦
  Std.Format.joinSep (left_repr cfg.tape.left 10) " " ++ s!" {cfg.state}>{cfg.tape.head} " ++ Std.Format.joinSep (right_repr cfg.tape.right 10) " "⟩

instance: Repr Turing.Dir where
  reprPrec := λ d _ ↦ match d with
    | .left => "L"
    | .right => "R"

instance: Repr (Stmt l s) where
  reprPrec := λ s _ ↦ match s with
    | .halt => "---"
    | .next s d l => repr s ++ repr d ++ repr l

instance: Repr (Machine l s) := ⟨λ M _ ↦
  joinSep (Finset.univ (α:=Label l) |>.sort (· ≤ ·) |>.map (λ lab ↦
    join (Finset.univ (α:=Symbol s) |>.sort (· ≤ ·) |>.map (λ sym ↦ repr $ M lab sym))
  )) "_"⟩

end PrettyPrint

instance Machine.inhabited: Inhabited $ Machine l s := ⟨λ _ _ ↦ .halt⟩

instance Stmt.fintype: Fintype $ Stmt l s := by {
  suffices equiv: Option (Symbol s × Turing.Dir × Label l) ≃ Stmt l s by {
    have hOfin : Fintype $ Option (Symbol s × Turing.Dir × Label l) := by {
      suffices Fintype $ (Symbol s × Turing.Dir × Label l) from fintypeOfOption
      exact instFintypeProd (Symbol s) (Turing.Dir × Label l)
    }
    apply Fintype.ofEquiv (Option (Symbol s × Turing.Dir × Label l)) equiv
  }
  exact {
    toFun := λ o ↦ match o with
    | .none => .halt
    | .some (s, d, l) => .next s d l,
    invFun := λ s ↦ match s with
    | .halt => .none
    | .next s d l => .some (s, d, l),
    left_inv := by {
      unfold Function.LeftInverse
      intro v
      cases v <;> simp
    }
    right_inv := by {
      simp [Function.LeftInverse, Function.RightInverse]
      intro v
      cases v <;> simp
    }
  }
}

instance Machine.finite: Fintype $ Machine l s := by {
  unfold Machine
  refine @Pi.fintype (Label l) _ _ _ ?_
  intro _

  refine @Pi.fintype (Symbol s) _ _ _ ?_
  intro _
  apply inferInstance
}

instance Machine.decEq: DecidableEq (Machine l s) := by {
  intro A B
  refine @decidable_of_decidable_of_iff (∀ lab sym, A lab sym = B lab sym) _ ?_ ?_
  · apply Fintype.decidableForallFintype

  constructor
  · intro h
    apply funext
    intro lab
    apply funext
    intro sym
    exact h lab sym
  · intro h lab sym
    rw [h]
}

instance Config.inhabited: Inhabited $ Config l s := ⟨⟨default, default⟩⟩

def Machine.step (M: Machine l s) (orig: Config l s): Option (Config l s) := match M orig.state orig.tape.head with
| .halt => none
| .next sym dir state => some { state, tape := orig.tape.write sym |>.move dir}

def Machine.eval (M: Machine l s) (bound: ℕ) (orig: Config l s): Option (Config l s) := match bound with
| 0 => orig
| n + 1 => M.step orig >>= M.eval n

def Machine.LastState (M: Machine l s) (σ: Config l s): Bool := M.step σ |>.isNone


def Machine.halting_trans (M: Machine l s) := (Finset.univ (α:=Label l × Symbol s)).filter (λ pair ↦ M pair.1 pair.2 = .halt)

lemma Machine.halting_trans.mem_iff {M: Machine l s}: (lab, sym) ∈ M.halting_trans ↔ M lab sym = .halt :=
by simp [Machine.halting_trans]

def Machine.n_halting_trans (M: Machine l s) := M.halting_trans.card


def init: Config l s := default

end TM
