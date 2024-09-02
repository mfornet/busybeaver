import Busybeaver.Basic
import Busybeaver.Reachability

namespace TM.Machine

/--
Holds when the machine cannot take the transition.
-/
def unreachable_trans (M: Machine l s) (lab: Label l) (sym: Symbol s) (A: Config l s) :=
  ∀ (n: ℕ) (C: Config l s), C.state = lab → C.tape.head = sym → ¬(A -[M]{n}-> C)

/--
If none of the halting transitions are reachable, then the machine does not halt.
-/
theorem halting_trans.all_unreachable {M: Machine l s} (h: ∀T ∈ M.halting_trans, M.unreachable_trans T.1 T.2 default):
  ¬(M.halts default) :=
by {
  intro ⟨n, C, Clast, Creach⟩
  unfold unreachable_trans at h
  apply absurd Creach
  apply h (C.state, C.tape.head)
  · simp [halting_trans]
    simp [LastState] at Clast
    exact Clast
  · rfl
  · rfl
}

/-- Underspecified tape for backward steps -/
abbrev SymbolicTape s := Turing.Tape (WithTop (Symbol s))

/-- Config for backward steps -/
structure SymbolicConfig (l s) where
  state: Label l
  tape: SymbolicTape s
deriving DecidableEq, Inhabited

section PrettyPrint
open Std.Format Lean

private def right_repr [Repr α] [Inhabited α] (l: Turing.ListBlank α) (bound: ℕ): List Format := match bound with
| 0 => []
| n + 1 => repr l.head :: (right_repr l.tail n)

private def left_repr [Repr α] [Inhabited α] (l: Turing.ListBlank α) (bound: ℕ): List Format := match bound with
| 0 => []
| n + 1 => left_repr l.tail n ++ [repr l.head]

instance: Repr (SymbolicConfig l s) := ⟨λ cfg _ ↦
  Std.Format.joinSep (left_repr cfg.tape.left 10) " " ++ s!" {cfg.state}>{repr cfg.tape.head} " ++ Std.Format.joinSep (right_repr cfg.tape.right 10) " "⟩

end PrettyPrint

def SymbolicConfig.from_trans (lab: Label l) (sym: Symbol s): SymbolicConfig l s := {
  state := lab,
  tape := { head := sym, left := default, right := default }
}

def sym_step (M: Machine l s) (C: SymbolicConfig l s) (sym: Symbol s) (h: M C.state sym ≠ .halt): SymbolicConfig l s :=
match hM: M C.state sym with
| .halt => by contradiction
| .next sym' dir lab' => { state := lab', tape := (C.tape.write ↑sym').move dir }


def sym_eval (M: Machine l s) (C: SymbolicConfig l s): Finset (SymbolicConfig l s) := match C.tape.head with
| ⊤ =>
  Finset.univ (α:=Symbol s) |>.filter (λ S ↦ M C.state S ≠ .halt) |>.attach.image
  λ ⟨S, hS⟩ ↦ sym_step M C S (by {
    simp at hS
    exact hS
  })
| some sym => match hM : M C.state sym with
  | .halt => {}
  | .next sym' dir lab' => {
    sym_step M C sym (by {
      rw [hM]
      simp
    })
  }

def symbolic_halting (M: Machine l s): Finset (SymbolicConfig l s) :=
  M.halting_trans.image λ ⟨lab, sym⟩ ↦ SymbolicConfig.from_trans lab sym

def m1RB (l s): Machine l s := λ lab sym ↦ if lab = 0 ∧ sym = 0 then .next 1 .right 1 else .halt

def sym_eval_bw (M: Machine l s) (C: SymbolicConfig l s) (lab: Label l) (sym: Symbol s): Option
(SymbolicConfig l s) := match M lab sym with
| .halt => .none
| .next _ dir lab' =>
  if lab' ≠ lab then
    .none
  else
    let bw_moved := C.tape.move dir.other
    match bw_moved.head with
    | ⊤ => .some { state := lab, tape := bw_moved.write sym }
    | some sym'' =>
      if sym'' = sym then
        .some { state := lab, tape := bw_moved }
      else
        .none

def backward_step (M: Machine l s) (C: SymbolicConfig l s): Finset { S: SymbolicConfig l s // C ∈ M.sym_eval S }:=
  Finset.univ (α:=Label l × Symbol s)
    |>.filter (λ ⟨L, S⟩ ↦ ∃ sym' dir, M L S = .next sym' dir C.state ∧ (C.tape.move dir.other).head = sym')
    |>.attach.image λ ⟨⟨L, S⟩, hS⟩ ↦ match hM: M L S with
    | .halt => by simp_all
    | .next sym' dir lab' => by {
      simp_all
      use { state := L, tape := (C.tape.move dir.other).write S }
      obtain ⟨sym'', dir', hDefs, hlink⟩ := hS
      cases hDefs.1
      cases hDefs.2.1
      cases hDefs.2.2
      simp_all
      simp [sym_eval]
      simp [Turing.Tape.write]
      split
      · simp_all
      rename_i heq
      rw [hM] at heq
      cases heq
      simp [sym_step]
      split
      · rename_i heq
        rw [hM] at heq
        cases heq
      rename_i heq
      rw [hM] at heq
      cases heq
      obtain ⟨Cs, Ch, Cl, Cr⟩ := C
      simp_all
      cases dir <;> {
        simp [Turing.Tape.move, Turing.Tape.write, Turing.Dir.other]
        simp [Turing.Tape.move, Turing.Dir.other] at hlink
        rw [← hlink]
        exact (Turing.ListBlank.cons_head_tail _).symm
      }
    }

def sym_matches (tS: WithTop (Symbol s)) (S: Symbol s): Bool := match tS with
| ⊤ => True
| .some S' => S' == S

def SymbolicConfig.matches (C: SymbolicConfig l s) (C': Config l s): Prop :=
  C.state == C'.state ∧ (∀i, sym_matches (C.tape.nth i) (C'.tape.nth i))

lemma backward_step.empty_step {C: SymbolicConfig l s} (h: backward_step M C = ∅) (hCC': C.matches C'): ¬(A -[M]-> C') :=
by {
  intro hAC'
  obtain ⟨sym', dir, hM, hC't⟩ := Machine.step.some_rev hAC'
  simp [backward_step, Finset.filter_eq_empty_iff] at h

  obtain ⟨hCC's, hCC't⟩ := hCC'
  simp at hCC's

  rw [← hCC's] at hM

  specialize h A.state A.tape.head sym' dir hM
  apply h
  rw [← Turing.Tape.nth_zero]
  cases dir
  · simp [Turing.Dir.other, -Turing.Tape.nth_zero] at *
    rw [hC't] at hCC't
    specialize hCC't 1
    simp [Turing.Tape.write] at hCC't
    simp [sym_matches] at hCC't
    split at hCC't
    · rename_i heq
      rw [heq]
      sorry
    · simp at hCC't
      rename_i heq
      rw [hCC't] at heq
      exact heq
  · simp [Turing.Dir.other, -Turing.Tape.nth_zero] at *
    rw [hC't] at hCC't
    specialize hCC't (-1)
    simp [Turing.Tape.write] at hCC't
    sorry
}

lemma halting_trans.empty_loops {M: Machine l s} (h: M.halting_trans = ∅): ¬(M.halts default) :=
by {
  apply all_unreachable
  simp [h]
}
