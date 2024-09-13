import Busybeaver.Basic
import Busybeaver.Reachability

-- TODO: remove
import Busybeaver.Parse

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

def SymbolicConfig.from_trans (lab: Label l) (sym: Symbol s): SymbolicConfig l s := {
  state := lab,
  tape := ⟨{ head := sym, left := default, right := default }, by simp⟩
}

def symbolic_halting (M: Machine l s): Finset (SymbolicConfig l s) :=
  M.halting_trans.image λ ⟨lab, sym⟩ ↦ SymbolicConfig.from_trans lab sym

def tmpMach: Machine 4 1 := mach["1RB0LD_1LC0RE_---1LD_1LA1LD_1RA0RA"]

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

def backward_step (M: Machine l s) (C: SymbolicConfig l s): Finset (SymbolicConfig l s):=
  Finset.eraseNone.toFun <|
    Finset.univ (α:=Label l × Symbol s) |>.image (λ ⟨L, S⟩ ↦ matchingConfig? M C L S)

unsafe def startCfg := Quot.unquot tmpMach.symbolic_halting.val |>.get! 0
unsafe def nxtCfg := Quot.unquot (backward_step tmpMach startCfg).val |>.get! 0

#eval backward_step tmpMach nxtCfg

def SymbolicConfig.matchesConfig (C: SymbolicConfig l s) (C': Config l s): Prop :=
  C.state == C'.state ∧ (∀i, C.tape.val.nth i = ⊤ ∨ C.tape.val.nth i = C'.tape.nth i)

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
    rcases hCC't with _ | heq
    · refine absurd ?_ h.2
      trivial
    · refine absurd ?_ h.1
      rw [heq, hC't]
      simp [Turing.Tape.move, Turing.Tape.write]
  · simp [Turing.Dir.other, Turing.Tape.move] at h
    specialize hCC't (Int.negSucc 0)
    simp [Turing.Tape.nth] at hCC't
    rcases hCC't with _ | heq
    · refine absurd ?_ h.2
      trivial
    · refine absurd ?_ h.1
      rw [heq, hC't]
      simp [Turing.Tape.move, Turing.Tape.write]
}

theorem backward_step.unreachable {C: SymbolicConfig l s} {sym: Symbol s}
  (h: backward_step M C = ∅):
  unreachable_trans M C.state C.tape.head A :=
by {
  intro n C' hCs hCh hdC'
  sorry
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

lemma halting_trans.empty_loops {M: Machine l s} (h: M.halting_trans = ∅): ¬(M.halts default) :=
by {
  apply all_unreachable
  simp [h]
}

lemma halting_trans.eq_zero_nonhalts {M: Machine l s} (hM: M.n_halting_trans = 0): ¬M.halts default := by {
  simp [Machine.n_halting_trans] at hM
  exact empty_loops hM
}

def backwardReason (bound: ℕ) (M: Machine l s) (C: SymbolicConfig l s): Bool :=
match bound with
| 0 => .false
| n + 1 => Finset.all (backward_step M C) (λ C ↦ backwardReason n M C)

end Machine

open Machine

def backwardsReasoningDecider (bound: ℕ) (M: Machine l s): HaltM M Unit :=
  let rec loop (n: ℕ) (cfg: SymbolicConfig l s): Bool :=
    match n with
    | 0 => .false
    | n + 1 => Finset.all (backward_step M cfg) (λ C ↦ loop n C)
  if h: Finset.all M.symbolic_halting (loop bound) then
    .loops_prf (by {
      simp at h
      apply halting_trans.all_unreachable
      intro ⟨lab, sym⟩ hls
      simp
      simp [halting_trans] at hls

      sorry
    })
  else
    .unknown ()
