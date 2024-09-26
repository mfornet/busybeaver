import Busybeaver.Basic
import Busybeaver.Reachability
import Busybeaver.Transition
import Busybeaver.Deciders.BoundExplore

-- TODO: remove
import Busybeaver.Parse

/-!
Backwards reasonning.

Here again, this is heavily inspired by busycoq.
https://github.com/meithecatte/busycoq/blob/master/verify/BackwardsReasoning.v
-/


namespace TM.Machine

/-- Underspecified tape for backward steps -/
abbrev SymbolicTape s := Turing.Tape (WithTop (Symbol s))

abbrev LawfulSymbolicTape s := { T: SymbolicTape s // T.head ≠ ⊤ }

section

variable (T: LawfulSymbolicTape s)

def LawfulSymbolicTape.left := T.val.left
def LawfulSymbolicTape.right := T.val.right

def LawfulSymbolicTape.head: Symbol s := WithTop.untop T.val.head T.prop

def LawfuleSymbolicTape.write (sym: Symbol s): LawfulSymbolicTape s :=
  ⟨T.val.write sym, by simp [Turing.Tape.write]⟩

end

def SymbolicTape.match (T T': SymbolicTape s): Prop :=
  ∀i, T.nth i = ⊤ ∨ T.nth i = T'.nth i

@[simp]
lemma SymbolicTape.match.refl {T: SymbolicTape s}: T.match T :=
by {
  intro _
  right
  rfl
}

local notation T " ⊨ " T' => SymbolicTape.match T T'

/-- Config for backward steps -/
structure SymbolicConfig (l s) where
  state: Label l
  tape: LawfulSymbolicTape s
deriving DecidableEq

instance: Inhabited (SymbolicConfig l s) := ⟨{
  state := default,
  tape := ⟨{ head := ↑(default: Symbol s), left := default, right := default }, by simp⟩
}⟩

section PrettyPrint
open Std.Format Lean

unsafe instance: Repr (SymbolicConfig l s) := ⟨λ cfg _ ↦
  let leftrepr := (Quot.unquot cfg.tape.left).reverse.map repr
  let rightrepr := (Quot.unquot cfg.tape.right).map repr
  Std.Format.joinSep leftrepr " " ++ s!" {Char.ofNat <| cfg.state + 'A'.toNat}>{repr cfg.tape.head} " ++ Std.Format.joinSep rightrepr " "⟩

end PrettyPrint

def SymbolicConfig.matchesConfig (C: SymbolicConfig l s) (C': Config l s): Prop :=
  C.state == C'.state ∧ (∀i, C.tape.val.nth i = ⊤ ∨ C.tape.val.nth i = C'.tape.nth i)

def SymbolicConfig.from_trans (lab: Label l) (sym: Symbol s): SymbolicConfig l s := {
  state := lab,
  tape := ⟨{ head := sym, left := default, right := default }, by simp⟩
}

def symbolic_halting (M: Machine l s): Finset (SymbolicConfig l s) :=
  M.halting_trans.image λ ⟨lab, sym⟩ ↦ SymbolicConfig.from_trans lab sym

lemma symbolic_halting.is_last_state {M: Machine l s} {C: Config l s} (hC: M.LastState C):
  (SymbolicConfig.from_trans C.state C.tape.head) ∈ symbolic_halting M :=
by {
  simp [symbolic_halting]
  use C.state, C.tape.head
  constructor
  · simp [LastState] at hC
    exact hC
  · rfl
}

@[simp]
lemma SymbolicConfig.from_trans.matches {C: Config l s}:
  SymbolicConfig.from_trans C.state C.tape.head |>.matchesConfig C :=
by {
  unfold from_trans
  constructor
  · simp only [beq_self_eq_true]
  · simp only
    intro i
    simp [Turing.Tape.nth]
    split <;> tauto
}

/--
Tries to apply `M L S` backwards if possible, returning the resulting symbolic configuration.
-/
def matchingConfig? (M: Machine l s) (C: SymbolicConfig l s) (L: Label l) (S: Symbol s): Option (SymbolicConfig l s) :=
  match M L S with
  | .halt => .none
  | .next sym' dir lab' =>
    /-
    We are in this configuration (assuming dir = .right wlog)
                C.tape
    ... Cm.head C.head ...

    For it to be consistent to have applied the M L S configuration, we need to do the following
    modification

        L                    lab'
    ... S _ ...  -> ... sym' ____ ...
    -/
    let Cm := (C.tape.val.move dir.other)
    if lab' = C.state ∧ (Cm.head = sym' ∨ Cm.head = ⊤) then
      .some { state := L, tape := ⟨Cm.write S, by simp [Turing.Tape.write]⟩}
    else
      -- This is BR contradiction case
      .none


lemma matchingConfig?.correct {C C': Config l s} {Cs: SymbolicConfig l s}
  (hC: C -[M]-> C') (hC': Cs.matchesConfig C'): ∃C₀ ∈ matchingConfig? M Cs C.state C.tape.head, C₀.matchesConfig C :=
by {
  obtain ⟨sym, dir, hM, hCt⟩ := Machine.step.some_rev hC
  obtain ⟨Csh, Cst⟩ := hC'
  simp at Csh
  simp [matchingConfig?, hM, Csh]
  conv =>
    pattern (_ ∧ _) ∧ _
    rw [
      and_assoc
    ]
  simp
  constructor
  · cases dir
    · simp [Turing.Dir.other, Turing.Tape.move]
      simp [Turing.Tape.move] at hCt
      specialize Cst 1
      simp [Turing.Tape.nth] at Cst
      rcases Cst with Cst | Cst
      · right
        exact Cst
      · left
        rw [hCt] at Cst
        simp [Turing.Tape.write] at Cst
        exact Cst
    · simp [Turing.Dir.other, Turing.Tape.move]
      simp [Turing.Tape.move] at hCt
      specialize Cst (.negSucc 0)
      simp [Turing.Tape.nth] at Cst
      rcases Cst with Cst | Cst
      · right
        exact Cst
      · left
        rw [hCt] at Cst
        simp [Turing.Tape.write] at Cst
        exact Cst
  · constructor
    · simp
    · simp
      intro i
      split
      · rename_i heq
        cases heq
        simp
      · rename_i heq
        cases dir
        · simp [Turing.Dir.other]
          rw [hCt] at Cst
          specialize Cst (i + 1)
          simp [hCt, heq] at Cst
          exact Cst
        · simp [Turing.Dir.other]
          rw [hCt] at Cst
          specialize Cst (i - 1)
          simp [hCt, heq] at Cst
          exact Cst
}

def backward_step (M: Machine l s) (C: SymbolicConfig l s): Finset (SymbolicConfig l s):=
  Finset.eraseNone.toFun <|
    Finset.univ (α:=Label l × Symbol s) |>.image (λ ⟨L, S⟩ ↦ matchingConfig? M C L S)

lemma backward_step.empty_step {C: SymbolicConfig l s} (h: backward_step M C = ∅) (hCC': C.matchesConfig C'): ¬(A -[M]-> C') :=
by {
  intro hAC'
  obtain ⟨sym', dir, hM, hC't⟩ := Machine.step.some_rev hAC'
  simp [backward_step, Finset.eraseNone, Finset.subtype, Finset.filter_eq_empty_iff] at h

  obtain ⟨hCC's, hCC't⟩ := hCC'
  simp at hCC's

  rw [← hCC's] at hM

  suffices (matchingConfig? M C A.state A.tape.head).isSome by {
    simp [Option.isSome] at this
    split at this
    swap
    · cases this

    rename_i heq
    specialize h A.state A.tape.head heq
    cases h
  }

  simp [matchingConfig?, hM]
  split
  · simp
  simp
  rename_i h
  simp at h
  cases dir
  · simp [Turing.Dir.other, Turing.Tape.move] at h
    specialize hCC't 1
    simp [Turing.Tape.nth] at hCC't
    rcases hCC't with heq | heq
    · absurd h.2
      exact heq
    · absurd h.1
      rw [heq, hC't]
      simp [Turing.Tape.move, Turing.Tape.write]
  · simp [Turing.Dir.other, Turing.Tape.move] at h
    specialize hCC't (.negSucc 0)
    simp [Turing.Tape.nth] at hCC't
    rcases hCC't with heq | heq
    · absurd h.2
      exact heq
    · absurd h.1
      rw [heq, hC't]
      simp [Turing.Tape.move, Turing.Tape.write]
}

lemma backward_step.correct {C C': Config l s} {Cs: SymbolicConfig l s}
  (hC: C -[M]-> C') (hC': Cs.matchesConfig C'): ∃C₀ ∈ backward_step M Cs, C₀.matchesConfig C :=
by {
  simp [backward_step]
  obtain ⟨C₀, hC₀⟩ := matchingConfig?.correct hC hC'
  use C₀
  constructor
  · use C.state, C.tape.head, hC₀.1
  · exact hC₀.2
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

@[simp]
def Multiset.all.empty: Multiset.all 0 f = true :=
  by rfl

@[simp]
def Multiset.all.cons {S: Multiset α}: Multiset.all (a ::ₘ S) f = true ↔ f a && Multiset.all S f :=
  Quotient.inductionOn S <| fun _ ↦ by rfl

@[simp]
def Multiset.all.true {S: Multiset α}: Multiset.all S f = true ↔ ∀ a ∈ S, f a = true :=
  Quotient.inductionOn S <| fun _ ↦ by simp [Multiset.all]

def Finset.all (S: Finset α): (α → Bool) → Bool := Multiset.all S.val

@[simp]
lemma Finset.all.true {S: Finset α}: Finset.all S f = true ↔ ∀ a ∈ S, f a = true :=
  by simp [Finset.all]

def backwardReason (bound: ℕ) (M: Machine l s) (C: SymbolicConfig l s): Bool :=
match bound with
| 0 => .false
| n + 1 => Finset.all (backward_step M C) (λ C ↦ backwardReason n M C)

theorem backwardReason.correct {C C': Config l s} {Cs: SymbolicConfig l s}
  (hCs: Cs.matchesConfig C') (hBw: backwardReason bound M Cs):
  ¬C -[M]{bound}-> C' :=
by {
  intro hC
  induction bound, M, Cs using backwardReason.induct generalizing C' with
  | case1 => {
    unfold backwardReason at hBw
    cases hBw
  }
  | case2 M Cs₀ n IH => {
    simp [backwardReason] at hBw
    simp at hC
    obtain ⟨C₀, hCC₀, hC₀⟩ := hC.split
    apply Multistep.single' at hC₀

    obtain ⟨Cbw, hCbwi, hCbwm⟩ := backward_step.correct hC₀ hCs

    specialize hBw Cbw hCbwi
    exact IH Cbw hCbwm hBw hCC₀
  }
}

end Machine

open Machine

def backwardsReasoningDecider (bound: ℕ) (M: Machine l s): HaltM M Unit := do
  let ⟨_, prf⟩ ← boundedExplore bound M
  if h: Finset.all M.symbolic_halting (backwardReason bound M) then
    .loops_prf (by {
      intro ⟨n, hCl⟩
      simp at h

      have hn: bound ≤ n := halts_in.within hCl prf

      obtain ⟨C, Cl, Cr⟩ := hCl

      rw [
        show n = (n - bound) + bound from
          (Nat.sub_eq_iff_eq_add hn).mp rfl
      ] at Cr

      obtain ⟨Cp, _, hCont⟩ := Cr.split

      let CsH := SymbolicConfig.from_trans C.state C.tape.head
      have hCsH: CsH ∈ M.symbolic_halting := symbolic_halting.is_last_state Cl

      specialize h CsH hCsH

      apply backwardReason.correct (C':=C) (Cs:=CsH)
      · exact SymbolicConfig.from_trans.matches
      · exact h
      · exact hCont
    })
  else
    .unknown ()
