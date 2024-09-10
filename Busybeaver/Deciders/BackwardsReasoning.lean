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
  absurd Creach
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

unsafe instance: Repr (SymbolicConfig l s) := ⟨λ cfg _ ↦
  let leftrepr := (Quot.unquot cfg.tape.left).reverse.map repr
  let rightrepr := (Quot.unquot cfg.tape.right).map repr
  Std.Format.joinSep leftrepr " " ++ s!" {cfg.state}>{repr cfg.tape.head} " ++ Std.Format.joinSep rightrepr " "⟩

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

lemma symbolic_halting.empty_step {C: SymbolicConfig l s} (h: C ∈ symbolic_halting M): sym_eval M C = ∅ :=
by {
  simp [symbolic_halting] at h
  obtain ⟨a, b, hAB, hCdef⟩ := h
  simp [halting_trans] at hAB
  rw [← hCdef] at *
  cases hCdef
  simp [SymbolicConfig.from_trans] at *
  simp [sym_eval]
  split <;> simp_all
}

def m1RB (l s): Machine l s := λ lab sym ↦ if lab = 0 ∧ sym = 0 then .next 1 .right 1 else .halt

def sym_eval_bw (M: Machine l s) (C: SymbolicConfig l s) (lab: Label l) (sym: Symbol s):
  Option (SymbolicConfig l s) :=
match M lab sym with
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

def matchingConfig? (M: Machine l s) (C: SymbolicConfig l s) (L: Label l) (S: Symbol s): Option (SymbolicConfig l s) :=
  match M L S with
  | .halt => .none
  | .next sym' dir lab' =>
    let Cm := (C.tape.move dir.other)
    if lab' = C.state ∧ (Cm.head = sym' ∨ Cm.head = ⊤) then
      .some { state := L, tape := Cm.write S }
    else
      .none

def backward_step (M: Machine l s) (C: SymbolicConfig l s): Finset (SymbolicConfig l s):=
  Finset.eraseNone.toFun <|
    Finset.univ (α:=Label l × Symbol s) |>.image (λ ⟨L, S⟩ ↦ matchingConfig? M C L S)

def backward_step.correct (hC: C ∈ backward_step M C'): C' ∈ M.sym_eval C :=
by {
  simp [backward_step] at hC
  obtain ⟨L, S, hLS⟩ := hC
  simp [matchingConfig?] at hLS
  split at hLS
  · cases hLS
  rename_i sym dir lab heq
  split at hLS
  swap
  · cases hLS
  rename_i heq'
  obtain ⟨hCs, hChmatch⟩ := heq'
  simp at hLS
  symm at hLS
  cases hLS

  simp [sym_eval]
  simp [Turing.Tape.write]
  split
  · rename_i heq'
    rw [heq] at heq'
    cases heq'

  rename_i heq'
  rw [heq] at heq'
  cases heq'
  simp

  simp [sym_step]
  split
  · rename_i heq'
    rw [heq] at heq'
    cases heq'

  rename_i heq'
  rw [heq] at heq'
  cases heq'

  rcases hChmatch with hC | hC
  · simp [Turing.Tape.write, Turing.Tape.move]
    split <;> {
      simp only [Turing.Dir.other] at *
      rename_i heq'
      simp at heq'
      cases heq'.1
      cases heq'.2.1
      cases heq'.2.2
      simp at heq'
      cases heq'
      simp
      simp [Turing.Tape.move] at hC
      simp [← hC, hCs]
    }
  · simp [Turing.Tape.write, Turing.Tape.move]
    split <;> {
      simp only [Turing.Dir.other] at *
      rename_i heq'
      simp at heq'
      cases heq'.1
      cases heq'.2.1
      cases heq'.2.2
      simp at heq'
      cases heq'
      simp
      simp [Turing.Tape.move] at hC
      simp [← hC, hCs]
      sorry
    }
}
    /- |>.attach.image λ ⟨⟨L, S⟩, hS⟩ ↦ match hM: M L S with -/
    /- | .halt => by simp_all -/
    /- | .next sym' dir lab' => by { -/
    /-   simp_all -/
    /-   use { state := L, tape := (C.tape.move dir.other).write S } -/
    /-   obtain ⟨sym'', dir', hDefs, hlink⟩ := hS -/
    /-   cases hDefs.1 -/
    /-   cases hDefs.2.1 -/
    /-   cases hDefs.2.2 -/
    /-   simp_all -/
    /-   simp [sym_eval] -/
    /-   simp [Turing.Tape.write] -/
    /-   split -/
    /-   · simp_all -/
    /-   rename_i heq -/
    /-   rw [hM] at heq -/
    /-   cases heq -/
    /-   simp [sym_step] -/
    /-   split -/
    /-   · rename_i heq -/
    /-     rw [hM] at heq -/
    /-     cases heq -/
    /-   rename_i heq -/
    /-   rw [hM] at heq -/
    /-   cases heq -/
    /-   obtain ⟨Cs, Ch, Cl, Cr⟩ := C -/
    /-   simp_all -/
    /-   sorry -/
    /-   /- -/
    /-   cases dir <;> { -/
    /-     simp [Turing.Tape.move, Turing.Tape.write, Turing.Dir.other] -/
    /-     simp [Turing.Tape.move, Turing.Dir.other] at hlink -/
    /-     rw [← hlink] -/
    /-     exact (Turing.ListBlank.cons_head_tail _).symm -/
    /-   } -/
    /-   -/ -/
    /- } -/

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
  sorry

  /-
  apply h A.state A.tape.head sym' dir hM
  rw [← Turing.Tape.nth_zero]
  cases dir
  · simp [Turing.Dir.other, -Turing.Tape.nth_zero] at *
    rw [hC't] at hCC't
    specialize hCC't 1
    simp [Turing.Tape.write] at hCC't
    simp [sym_matches] at hCC't
    split at hCC't
    · rename_i heq -- TODO: this branch is a contradiction
      rw [heq]
      simp [WithTop.some]
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
  -/
}

def Multiset.all (S: Multiset α): (α → Bool) → Bool :=
  Quotient.liftOn S List.all (by {
    intro A B hAB
    ext f
    induction hAB using List.Perm.recOn with try simp
    | @cons head tail tail' _ IH => rw [IH]
    | @swap head head' l => rw [Bool.and_left_comm]
    | @trans _ _ _ _ _ IH₁ IH₂ => {
      rw [IH₁]
      exact IH₂
    }
  })

def Finset.all (S: Finset α): (α → Bool) → Bool := Multiset.all S.val

lemma halting_trans.empty_loops {M: Machine l s} (h: M.halting_trans = ∅): ¬(M.halts default) :=
by {
  apply all_unreachable
  simp [h]
}

lemma halting_trans.eq_zero_nonhalts {M: Machine l s} (hM: M.n_halting_trans = 0): ¬M.halts default := by {
  simp [Machine.n_halting_trans] at hM
  exact empty_loops hM
}

end Machine

open Machine

def backwardsReasoningDecider (bound: ℕ) (M: Machine l s): HaltM M Unit :=
  let rec loop (n: ℕ) (cfg: SymbolicConfig l s): Bool :=
    match n with
    | 0 => .false
    | n + 1 => Finset.all (backward_step M cfg) (λ C ↦ loop n C)
  if Finset.all M.symbolic_halting (loop bound) then
    .loops_prf sorry
  else
    .unknown ()
