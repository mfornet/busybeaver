import Busybeaver.Basic
import Busybeaver.Reachability

import Busybeaver.Transition

import Busybeaver.ClosedSet
import Busybeaver.Enumerate.Child
import Busybeaver.Enumerate.Basic
import Busybeaver.Enumerate.Symmetry
import Busybeaver.Enumerate.Translate
import Busybeaver.Enumerate.Perm
import Busybeaver.Enumerate.Quotient

import Mathlib.Data.Finset.Defs

namespace TM.Busybeaver
open TM.Machine

variable {M: Machine l s}

/--
The busybeaver number with only one state is 1.

The numbers are slightly off because of the definitions of the various components.
-/
theorem one_state: Busybeaver 0 s = 0 :=
by {
  simp [symm.only_right]
  apply Nat.eq_zero_of_le_zero
  apply Nat.le_of_lt_add_one
  apply Busybeaver'.upper_bound_of_lt
  swap
  · simp

  intro ⟨M, n, term⟩ hM
  simp [symm.GoingTo] at *
  obtain ⟨sym, nlab, hnlab⟩ := hM

  have heqnlab: nlab = default := Fin.fin_one_eq_zero _
  simp [*] at *

  by_contra hn

  suffices ¬M.halts default by {
    apply this
    exists n
  }

  push_neg at hn
  obtain ⟨k, hk⟩ := Nat.exists_eq_succ_of_ne_zero hn
  simp_all
  obtain ⟨C, _, hCr⟩ := term
  cases hCr
  rename_i B Bstep hBC

  /-
  Proof sketch: machine is able to step once (from default to B) then it loops forever because of CTL
  -/
  closed_set (λ C ↦ C.state = default ∧ C.tape.head = default ∧ C.tape.right = default)
  · simp
    intro A' hAs hAt hAr
    cases hM : M.step A'
    · simp_all -- This is a contradiction
    rename_i A''
    exists A''
    constructor
    · obtain ⟨sym, dir, hA', hA''⟩ := Machine.step.some_rev hM
      have hA''s : A''.state = 0 := Fin.fin_one_eq_zero _
      simp [hAs, hAt, hA''s] at hA'
      rw [hnlab] at hA'
      cases hA'
      obtain ⟨A'h, A'l, A'r⟩ := A'
      simp_all
      simp [Turing.Tape.write, Turing.Tape.move]
      trivial
    · apply Machine.Progress.from_multistep (n:=0)
      simp
      exact Machine.Multistep.single hM
  · simp
    exists default
    constructor
    swap
    · exact Machine.EvStep.refl
    simp [default]
}

structure BBResult (l s: ℕ) where
  val : ℕ
  undec : Multiset (Machine l s)
deriving DecidableEq

def BBResult.join (t₁ t₂: BBResult l s): BBResult l s := {
  val := Max.max t₁.val t₂.val
  undec := t₁.undec + t₂.undec
}

instance BBResult.join.commutative: Std.Commutative (BBResult.join (l:=l) (s:=s)) :=
by {
  constructor
  intro A B
  simp [BBResult.join]
  constructor
  · exact Nat.max_comm _ _
  · exact AddCommMagma.add_comm A.undec B.undec
}

instance BBResult.join.associative: Std.Associative (BBResult.join (l:=l) (s:=s)) :=
by {
  constructor
  intro A B C
  simp [BBResult.join]
  constructor
  · exact Nat.max_assoc A.val B.val C.val
  · exact add_assoc A.undec B.undec C.undec
}

@[simp]
def BBResult.join.fold_max [DecidableEq α] {f: α → BBResult l s} {S: Finset α}:
  (Finset.fold BBResult.join B f S).val = Finset.fold Max.max B.val (λ a ↦ f a |>.val) S :=
by induction S using Finset.induction with
| empty => simp_all
| @insert a S' hA IH => simp [Finset.fold_insert hA, join, IH]

instance Multiset.add.associative {α}: Std.Associative (λ (A B: Multiset α) ↦ A + B):=
by {
  constructor
  intro A B C
  exact add_assoc A B C
}

instance Multiset.add.commutative {α}: Std.Commutative (λ (A B: Multiset α) ↦ A + B):=
by {
  constructor
  intro A B
  exact AddCommMagma.add_comm A B
}

@[simp]
def BBResult.join.fold_join [DecidableEq α] {f: α → BBResult l s} {S: Finset α}:
  (Finset.fold BBResult.join B f S).undec = B.undec + ∑ a ∈ S, (f a).undec
    /- Finset.fold (hc:=Multiset.add.commutative) B.undec (λ a ↦ f a |>.undec) S -/
  :=
by induction S using Finset.induction with
| empty => simp
| @insert a S' hA IH => {
  simp [Finset.fold_insert hA, join, Finset.sum_insert hA]
  conv_rhs =>
    rw [← add_assoc, AddCommMonoid.add_comm B.undec, add_assoc]
  simp [IH]
}

@[simp]
def Multiset.mem_sum [DecidableEq α] [DecidableEq β] {f: α → Multiset β} {S: Finset α}:
  e ∈ ∑ a ∈ S, f a
  ↔ ∃ R ∈ S.image f, e ∈ R
  :=
by induction S using Finset.induction with
| empty => simp
| @insert a S' hA IH => simp [Finset.fold_insert hA, IH]

@[simp]
def Multiset.add_empty [DecidableEq α] {A B: Multiset α}: A + B = 0 ↔ A = 0 ∧ B = 0 :=
by {
  constructor
  · intro h
    have hABc: ∀ a, (A + B).count a = 0 := by {
      rw [h]
      intro a
      rfl
    }
    constructor <;>
    · apply Multiset.le_zero.mp
      rw [Multiset.le_iff_count]
      intro a
      specialize hABc a
      rw [Multiset.count_add] at hABc
      conv_rhs => simp
      first
      | exact Nat.le.intro hABc
      | {
          conv_lhs at hABc => rw [AddCommMonoid.add_comm]
          exact Nat.le.intro hABc
        }
  · intro h
    rw [h.1, h.2]
    simp
}

@[simp]
def Multiset.sum_empty_iff_all_empty [DecidableEq α] [DecidableEq β] {f: α → Multiset β} {S: Finset α}:
  ∑ a ∈ S, f a = 0 ↔ ∀ a ∈ S, f a = 0 :=
by induction S using Finset.induction with
| empty => simp
| @insert A S hA IH => simp [Finset.sum_insert hA, IH]

def BBResult.from_haltm {M: Machine l s} (h: HaltM M α): BBResult l s := match h with
| .unknown _ => { val := 0, undec := {M}}
| .halts_prf n _ _ => { val := n, undec := {}}
| .loops_prf _ => {val := 0, undec := {}}

def used_states (M: Machine l s): (Finset (Label l)) :=
  Finset.univ (α:=Label l) |>.filter (λ l ↦ (∃sym, M.get l sym ≠ .halt) ∨ (∃ lab sym sym' dir, M.get lab sym = .next sym' dir l))

lemma used_states.mono (h: A.state ∈ used_states M) (hAB: A -[M]{n}-> B): B.state ∈ used_states M :=
by induction hAB with
| refl => exact h
| @succ A B _ _ hAB _ IH => {
  apply IH
  obtain ⟨sym, dir, hMA, _⟩ := Machine.step.some_rev hAB
  simp [used_states]
  right
  exists A.state
  exists A.tape.head
  exists sym
  exists dir
}

lemma used_states.mono_default (h: default ∈ used_states M) (hAB: default -[M]{n}-> B):
B.state ∈ used_states M :=
by {
  simp [default] at *
  refine used_states.mono ?_ hAB
  simp
  exact h
}

def used_symbols (M: Machine l s): Finset (Symbol s) :=
  Finset.univ (α:=Symbol s) |>.filter (λ s ↦ (∃lab, M.get lab s ≠ .halt) ∨ (∃lab sym dir lab', M.get lab sym = .next s dir lab'))

lemma used_symbols.mono (hA: ∀ i, A.tape.nth i ∈ used_symbols M) (hAB: A -[M]{n}-> B): ∀ j, B.tape.nth j ∈ used_symbols M :=
by induction hAB with
| refl => exact hA
| @succ A B _ _ hAB _ IH => {
  apply IH
  intro i
  obtain ⟨sym, dir, _, hBt⟩ := Machine.step.some_rev hAB
  rw [hBt]
  cases dir
  · simp
    split
    · simp [used_symbols]
      right
      use A.state, A.tape.head, .left, B.state
    · exact hA (i - 1)
  · simp
    split
    · simp [used_symbols]
      right
      use A.state, A.tape.head, .right, B.state
    · exact hA (i + 1)
}

lemma used_symbols.mono_default (h: default ∈ used_symbols M) (hB: default -[M]{n}-> B):
B.tape.head ∈ used_symbols M := by {
  simp [default] at *
  refine used_symbols.mono ?_ hB 0
  intro j
  simp [Turing.Tape.nth, Turing.ListBlank.nth]
  split <;> exact h
}

def usable_states (M: Machine l s): Finset (Label l) :=
  used_states M ∪ if hM: (Finset.univ \ used_states M).Nonempty then {(Finset.univ \ (used_states M)).min' hM} else ∅

def usable_symbols (M: Machine l s): Finset (Symbol s) :=
  used_symbols M ∪ if hM: (Finset.univ \ used_symbols M).Nonempty then {(Finset.univ \ (used_symbols M)).min' hM} else ∅

def possible_statements (M: Machine l s): Finset (Stmt l s) :=
  usable_symbols M ×ˢ Finset.univ (α:=Turing.Dir) ×ˢ usable_states M |>.image
    λ ⟨sym, dir, lab⟩ ↦ .next sym dir lab

lemma possible_statements.all_next {M: Machine l s}:
  ∀ S ∈ possible_statements M, ∃ sym dir lab, S = .next sym dir lab :=
by {
  intro S hS
  simp [possible_statements] at hS
  obtain ⟨sym, state, dir, hS⟩ := hS
  use sym, state, dir, hS.2.symm
}

/- def update_with (M: Machine l s) (lab: Label l) (sym: Symbol s) (S: Stmt l s): Machine l s := -/
/-   λ lab' sym' ↦ if lab' = lab ∧ sym' = sym then S else M.get lab' sym' -/

lemma update_with.le_halt_trans {M: Machine l s} {lab: Label l} {sym: Symbol s} (h: M.get lab sym = .halt):
  (M.update_with lab sym (.next sym' dir lab')).n_halting_trans = M.n_halting_trans - 1:=
by {
  simp [Machine.n_halting_trans]
  rw [← Finset.card_erase_of_mem (s:=M.halting_trans) (a:=(lab, sym)) (by {
    simp [halting_trans]
    exact h
  })]
  congr
  apply Finset.ext
  intro ⟨L, S⟩
  simp
  split
  · simp_all only [not_true_eq_false, imp_false, and_true, iff_false, ne_eq]
    simp only [reduceCtorEq, not_false_eq_true]
  · simp_all only [not_and, iff_and_self]
    intro _ hl hS
    cases hl
    cases hS
    simp_all only [not_true_eq_false, imp_false]
}

lemma update_with.le_halt_trans' {M: Machine l s} {lab: Label l} {sym: Symbol s} (h: M.get lab sym = .halt) (hS: S = .next sym' dir lab'):
  (update_with M lab sym S).n_halting_trans = M.n_halting_trans - 1:=
by {
  rw [hS]
  exact update_with.le_halt_trans h
}

def next_machines (M: Machine l s) (lab: Label l) (sym: Symbol s): Finset (Machine l s) :=
  usable_symbols M ×ˢ Finset.univ (α:=Turing.Dir) ×ˢ usable_states M |>.image
    λ ⟨S, D, L⟩ ↦ update_with M lab sym (.next S D L)

@[simp]
lemma next_machines.halttrans_le {M: Machine l s} {lab: Label l} {sym: Symbol s} (h: M.get lab sym = .halt):
  ∀ M' ∈ next_machines M lab sym, M'.n_halting_trans = M.n_halting_trans - 1 :=
by {
  intro M' hM'
  simp [next_machines] at hM'
  obtain ⟨S, D, L, _, hM⟩ := hM'
  rw [← hM]
  exact update_with.le_halt_trans h
}

set_option linter.unusedVariables false in
/--
TNF enumeration function.

This enumerates TMs in TNF form starting from M and tries to decide
them using the decider. It blocks the unwrapping at undecided TMs.
-/
def BBCompute (decider: (M': Machine l s) → HaltM M' Unit) (M: Machine l s): BBResult l s :=
match decider M with
| .loops_prf _ => { val := 0, undec := {} } -- If this one loops, then the descendents also loop
| .halts_prf n C hC =>
  if hMn: M.n_halting_trans > 1 then
    Finset.fold BBResult.join { val := n, undec := {} } (λ M' ↦ BBCompute decider M'.val) $
    (next_machines M C.state C.tape.head).attach
  else
    { val := n, undec := {}}
| .unknown _ => { val := 0, undec := {M} } -- This machine is undecided, no need to go further
termination_by M.n_halting_trans
decreasing_by {
  obtain ⟨M', hM'⟩ := M'
  obtain ⟨hCl, _⟩ := hC
  simp [Machine.LastState] at hCl
  have hMM' := next_machines.halttrans_le hCl M' hM'
  simp_wf
  rw [hMM']
  exact Nat.sub_one_lt_of_lt hMn
}

namespace BBCompute

lemma is_child.used_states_mono (h: M ≤c M'): used_states M ⊆ used_states M' :=
by {
  intro lab hlab
  simp [used_states] at *
  rcases hlab with ⟨sym, hM⟩ | ⟨lab', sym, sym', dir, hM⟩
  · left
    exists sym
    specialize h lab sym
    simp [hM] at h
    rw [← h]
    exact hM
  · right
    use lab', sym, sym', dir
    specialize h lab' sym
    simp [hM] at h
    exact h.symm
}

lemma is_child.used_symbols_mono (h: M ≤c M'): used_symbols M ⊆ used_symbols M' :=
by {
  intro sym hsym
  simp [TM.Busybeaver.used_symbols] at *
  rcases hsym with ⟨lab, hM⟩ | ⟨lab, sym', dir, lab', hM⟩
  · left
    exists lab
    specialize h lab sym
    simp [hM] at h
    rw [← h]
    exact hM
  · right
    use lab, sym', dir, lab'
    specialize h lab sym'
    simp [hM] at h
    exact h.symm
}

lemma update_with.is_child (hUpd: M.get sym lab = .halt): M ≤c (update_with M sym lab (.next sym' dir lab')) :=
by {
  intro nlab nsym
  simp
  split <;> simp_all
}

lemma next_machines.is_child (hM: M.get sym lab = .halt) (hMn: Mn ∈ next_machines M sym lab): M ≤c Mn :=
by {
  simp [next_machines] at hMn
  obtain ⟨S, D, L, _, hMn⟩ := hMn
  rw [← hMn]
  exact update_with.is_child hM
}

lemma undec_is_child (hM: M' ∈ (BBCompute decider M).undec): M ≤c M' :=
by induction M using BBCompute.induct decider with
| case1 M Mloops Mdec => {
  unfold BBCompute at hM
  simp [Mdec] at hM
}
| case4 M _ Mdec => {
  unfold BBCompute at hM
  simp [Mdec] at hM
  cases hM
  exact is_child.refl
}
| case3 M n C Clast Mdec h => {
  unfold BBCompute at hM
  simp [Mdec, h] at hM
}
| case2 M n C Clast Mdec Mntrans IH => {
  unfold BBCompute at hM
  simp [Mdec, Mntrans] at hM
  obtain ⟨Mc, hMc, hMc'⟩ := hM
  specialize IH ⟨Mc, hMc⟩
  simp at IH
  specialize IH hMc'
  simp [Machine.LastState] at Clast
  calc
    is_child M' Mc := IH
    is_child Mc M := next_machines.is_child Clast.1 hMc
}

lemma is_child.perm_unused_states {M M': Machine l s} (h: M ≤c M') (hq: q ∉ TM.Busybeaver.used_states M) (hq': q' ∉ TM.Busybeaver.used_states M): M ≤c M'.perm q q' :=
by {
  intro lab sym
  simp [TM.Busybeaver.used_states] at hq hq'
  obtain ⟨hq₁, hq₂⟩ := hq
  obtain ⟨hq'₁, hq'₂⟩ := hq'
  by_cases hlq: lab = q
  · left
    rw [hlq]
    exact hq₁ sym
  by_cases hlq': lab = q'
  · left
    rw [hlq']
    exact hq'₁ sym

  rcases h lab sym with h' | h'
  · left
    exact h'
  right
  simp [Machine.perm, Machine.swap.ne hlq hlq']
  split
  · simp_all
  simp_all
  rename_i nlab _
  suffices nlab ≠ q ∧ nlab ≠ q' by {
    simp [Machine.swap.ne this.1 this.2]
  }
  constructor
  · intro hnq
    apply hq₂
    rw [hnq] at h'
    exact h'
  · intro hnq'
    apply hq'₂
    rw [hnq'] at h'
    exact h'
}

lemma is_child.translate_unused_symbols {M M': Machine l s}
  (h: M ≤c M')
  (hs: S ∉ TM.Busybeaver.used_symbols M)
  (hs': S' ∉ TM.Busybeaver.used_symbols M): M ≤c M'.translated S S' :=
by {
  intro lab sym
  rcases h lab sym with h' | h'
  · left
    exact h'

  simp [TM.Busybeaver.used_symbols] at hs hs'
  obtain ⟨hs₁, hs₂⟩ := hs
  obtain ⟨hs'₁, hs'₂⟩ := hs'

  by_cases hsS: sym = S
  · left
    rw [hsS]
    exact hs₁ lab

  by_cases hsS': sym = S'
  · left
    rw [hsS']
    exact hs'₁ lab

  simp [Machine.translated, Machine.swap.ne hsS hsS']
  split
  · left
    simp_all
  simp_all
  rename_i sym' _ _ _
  suffices sym' ≠ S ∧ sym' ≠ S' by {
    simp [Machine.swap.ne this.1 this.2]
  }
  constructor
  · intro hsymS
    rw [hsymS] at h'
    apply hs₂
    exact h'
  · intro hsymS'
    rw [hsymS'] at h'
    apply hs'₂
    exact h'
}


lemma next_machines.terminates_children (hM': M ≤c M')
    (hlabz: default ∈ used_states M) (hsymz: default ∈ used_symbols M)
    (hlabC: C.state ∈ used_states M) (hheadC: C.tape.head ∈ used_symbols M):
    (M'.LastState C) ∨ (∃Mc ∈ next_machines M C.state C.tape.head, ∃Mh, (Mh ~m M') ∧ Mc ≤c Mh) :=
by match hM'C: M'.get C.state C.tape.head with
| .halt => {
  left
  simp [Machine.LastState]
  exact hM'C
}
| .next sym dir lab => {
  /-
  The tricky bit of the proof.

  Any child machine with a non-halting transition at C is equivalent to a next_machine':
  - if the transition uses already used states/symbols, then it is itself a child of a
    next_machine'
  - otherwise, "normalize" the machine into a machine using the successor of the sates/symbols
    this one is a next_machine'
  -/
  right

  wlog hsym: sym ∈ usable_symbols M generalizing M' sym
  · have hsymUnused : sym ∉ used_symbols M := by {
      simp [usable_symbols] at hsym
      exact hsym.1
    }

    have unused_symbols: (Finset.univ \ used_symbols M).Nonempty := by {
      exists sym
      simp
      exact hsymUnused
    }

    let newsym := (Finset.univ \ used_symbols M).min' unused_symbols

    have hnsym : newsym ∉ used_symbols M := by {
      have htmp := Finset.min'_mem _ unused_symbols
      simp [newsym]
      simp at htmp
      exact htmp
    }

    obtain ⟨Mc, hMc, Mh, hMhl, hMhr⟩ := @this
      (M'.translated sym newsym)
      (is_child.translate_unused_symbols hM' hsymUnused hnsym) newsym
      (by {
        suffices C.tape.head ≠ sym ∧ C.tape.head ≠ newsym by
          simp [Machine.translated, Machine.swap.ne this.1 this.2, hM'C]
        constructor
        · intro hlab
          cases hlab
          exact absurd hheadC hsymUnused
        · intro hlab
          rw [← hlab] at hnsym
          exact absurd hheadC hnsym
      }) (by simp [usable_symbols, hnsym, unused_symbols])

    use Mc, hMc, Mh
    constructor
    swap
    · exact hMhr
    · have hsym: sym ≠ default := by {
        intro hlab
        cases hlab
        simp only [usable_symbols, Finset.mem_union, not_or] at hsym
        exact absurd hsymz hsymUnused
      }
      have hnsymz: newsym ≠ default := by {
        intro hlab
        rw [hlab] at hnsym
        exact absurd hsymz hnsym
      }

      calc Mh
        _ ~m M'.translated sym newsym := hMhl
        _ ~m M' := Isomorph.symbols sym newsym M' hsym hnsymz |>.symm

  wlog hlab: lab ∈ usable_states M generalizing M' lab
  · have hlabUnused : lab ∉ used_states M := by {
      simp [usable_states] at hlab
      exact hlab.1
    }

    have unused_states: (Finset.univ \ used_states M).Nonempty := by {
      exists lab
      simp
      exact hlabUnused
    }

    let newlab := (Finset.univ \ used_states M).min' unused_states

    have hnlab : newlab ∉ used_states M := by {
      suffices newlab ∈ (Finset.univ \ used_states M) by {
        simp at this
        exact this
      }
      exact Finset.min'_mem _ unused_states
    }

    obtain ⟨Mc, hMc, Mh, hMhl, hMhr⟩ := @this
      newlab
      (M'.perm lab newlab)
      (is_child.perm_unused_states hM' hlabUnused hnlab)
      (by {
        suffices C.state ≠ lab ∧ C.state ≠ newlab by
          simp [perm, Machine.swap.ne this.1 this.2, hM'C]
        constructor
        · intro hlab
          cases hlab
          exact absurd hlabC hlabUnused
        · intro hlab
          rw [← hlab] at hnlab
          exact absurd hlabC hnlab
      })
      (by simp [usable_states, hnlab, unused_states])

    use Mc, hMc, Mh
    constructor
    swap
    · exact hMhr
    · have hlab: lab ≠ default := by {
        intro hlab
        cases hlab
        simp only [usable_states, Finset.mem_union, not_or] at hlab
        exact absurd hlabz hlab.1
      }
      have hnlabz: newlab ≠ default := by {
        intro hlab
        rw [hlab] at hnlab
        exact absurd hlabz hnlab
      }

      calc Mh
        _ ~m M'.perm lab newlab := hMhl
        _ ~m M' := Isomorph.states lab newlab M' hlab hnlabz |>.symm

  use update_with M C.state C.tape.head (.next sym dir lab)
  constructor
  · simp [next_machines]
    use sym, dir, lab

  use M'
  constructor
  · constructor
  · intro lab' sym'
    specialize hM' lab' sym'
    simp
    split
    · simp
      rename_i heq
      cases heq.1
      cases heq.2
      exact hM'C.symm
    · exact hM'
}

lemma Finset.fold_attach {S: Finset α} [DecidableEq α] [Std.Commutative op] [Std.Associative op]:
  Finset.fold op B (f ∘ Subtype.val) S.attach = Finset.fold op B f S :=
by induction S using Finset.induction with
| empty => simp
| @insert A S hA IH => {
  conv_rhs => rw [Finset.fold_insert hA]
  conv_lhs =>
    simp
    rw [Finset.fold_insert (by {
      simp
      exact hA
    })]
  congr 1
  simp at IH
  simp [IH]
}

/--
The BBCompute function is correct when called on a machine that uses the default symbol and state.

Some explanations about the hypotheses:
- h: there are no undecided machines
- hsym/hlab: the initial machine uses the default symbol/state (it defines a transition for the empty tape
-/
theorem correct
  (h: (BBCompute decider M).undec = ∅)
  (hsym: default ∈ used_symbols M)
  (hlab: default ∈ used_states M):

  (BBCompute decider M).val = Busybeaver' l s (terminating_children M) :=

by induction M using BBCompute.induct decider with
| case1 M' nonhalt h' => {
  -- The machine loops, thus the children also loop
  unfold BBCompute
  simp [h']
  suffices terminating_children M' = {} by simp [this]
  rw [← Finset.not_nonempty_iff_eq_empty]
  intro hM
  obtain ⟨⟨nMm,nMn, nMterm⟩, hnMm⟩ := hM.exists_mem
  simp [terminating_children] at hnMm
  have nMnothalts := hnMm.halt_of_halt_parent nonhalt
  exact absurd ⟨nMn, nMterm⟩ nMnothalts
}
| case4 M a dec => simp [BBCompute, dec] at h -- The machine is unknown, contradictory because undec = {}
| case3 M nh C Clast h' hntrans => { -- The machine halts but cannot be expanded
  unfold BBCompute at *
  simp [h', hntrans] at h
  simp [h', hntrans]
  simp at hntrans
  have hMn : M.n_halting_trans = 1 := by {
    by_contra hMne
    have hMnz: M.n_halting_trans = 0 := by {
      apply Nat.eq_zero_of_le_zero
      apply Nat.le_of_lt_succ
      conv_rhs =>
        simp
      exact Nat.lt_of_le_of_ne hntrans hMne
    }
    apply Machine.halting_trans.eq_zero_nonhalts hMnz
    use nh, C
  }

  simp [
    terminating_children.one_transition (by {
      use C
    }) hMn
  ]
}
| case2 M nh C Clast h' hntrans IH => { -- The machine halts in nh steps, in Clast the last state
  /-
  Proof sketch (thanks to @mei on discord)

  Each terminating child of M fits in either cases:
  - It has the same halting transition for configuration C -> halting time is the same
  - It has another transition from C -> halting time is one of ones of the next_machines's
  -/
  unfold BBCompute
  simp [h']

  -- Simplify hypotheses
  unfold BBCompute at h
  simp [h', hntrans] at h

  simp [Machine.LastState] at Clast

  /-
  A "simplified" version of the induction hypothesis.
  -/
  have hMn: ∀ Mn ∈ (next_machines M C.state C.tape.head), (BBCompute decider Mn).val = Busybeaver' l s (terminating_children Mn) :=
  by {
    intro Mn Hmn
    have hMchild := next_machines.is_child Clast.1 Hmn
    apply IH ⟨Mn, Hmn⟩
    · exact h Mn Hmn
    · exact is_child.used_symbols_mono hMchild hsym
    · exact is_child.used_states_mono hMchild hlab
  }

  /-
  This is the case disjunction mentionned above.
  -/
  have hTerm: terminating_children M =
    (terminating_children M).filter (λ M ↦ M.M.get C.state C.tape.head = .halt) ∪ (terminating_children M).filter (λ M ↦ M.M.get C.state C.tape.head ≠ .halt) := by {
    apply Finset.ext
    intro M
    cases hM: M.M.get C.state C.tape.head <;> simp_all
  }
  rw [hTerm]
  simp

  /-
  First case, the child machine has the same halting transition as M, that is, it halts.
  In this case in terminates in the same number of steps as M
  -/
  have hSameM : Busybeaver' l s ((terminating_children M).filter (λ M ↦ M.M.get C.state C.tape.head =
  .halt)) = nh := by {
    apply Busybeaver'.eq_of_all_eq
    · exists ⟨M, nh, by {
        exists C
      }⟩
      simp
      constructor
      swap
      · exact Clast.1
      simp [terminating_children]
    · intro ⟨M', n', M'term⟩ hM'
      simp at hM'
      simp
      apply M'term.deterministic
      exists C
      constructor
      · simp [LastState]
        exact hM'.2
      · simp [terminating_children] at hM'
        exact hM'.1.multistep Clast.2
  }
  rw [hSameM]
  simp [hntrans]

  /-
  Here starts a calculatory part of the proof where we simplify the goal
  to be only about the child machines.
  -/
  calc Finset.fold Max.max nh (λ M' ↦ (BBCompute decider M'.val).val) (next_machines M C.state C.tape.head).attach
    _ = Finset.fold Max.max nh (λ M' ↦ (BBCompute decider M').val) (next_machines M C.state
    C.tape.head) := by {
      rw [
        show (λ M' ↦ (BBCompute decider M'.val).val) = (λ M' ↦ (BBCompute decider M').val) ∘ Subtype.val by {
          funext M
          simp
        }
      ]
      exact Finset.fold_attach
    }
    _ = Finset.fold Max.max nh (λ M' ↦ Busybeaver' l s (terminating_children M')) (next_machines M C.state C.tape.head) := by {
      apply Finset.fold_congr
      intro M' hM'
      exact hMn M' hM'
    }
    _  = Finset.fold Max.max nh (Busybeaver' l s) (
      (next_machines M C.state C.tape.head).image terminating_children
    ) := by simp [Finset.fold_image_idem]
    _ = Max.max nh (Finset.fold Max.max 0 (Busybeaver' l s) (
      (next_machines M C.state C.tape.head).image terminating_children
    )) := by {
    suffices ∀ {α: Type} [DecidableEq α] (S: Finset α) (f: α → ℕ) (n: ℕ), Finset.fold Max.max n f S = Max.max n (Finset.fold Max.max 0 f S) from this _ _ nh
    intro _ _ S f n
    induction S using Finset.induction with
    | empty => simp
    | @insert A S _ IH => {
      simp [IH]
      conv =>
        rhs
        rw [Nat.max_comm, Nat.max_assoc]
        rhs
        rw [Nat.max_comm]
    }
  }
  congr 1

  rw [Busybeaver'.fold_max_eq_fold_union]
  /-
  We begin the second case mentionned above. We need to prove that the next_machines' of M are
  actually enough to consider to compute the busybeaver for all the other child machines.
  -/

  /-
  Before embarquing in this, lets proove some properties about C
  -/
  have hCs: C.state ∈ used_states M := used_states.mono_default hlab Clast.2
  have hCt: C.tape.head ∈ used_symbols M := used_symbols.mono_default hsym Clast.2

  apply Busybeaver'.biject_fold
  · intro M' hM'
    exists M'
    simp [Finset.mem_fold_union, Finset.mem_image, id] at hM'
    simp
    obtain ⟨childs, hchilds, hM'childs⟩ := hM'
    simp [terminating_children] at hM'childs
    constructor
    · simp [terminating_children]
      calc
        is_child M'.M childs := hM'childs
        is_child childs M := next_machines.is_child Clast.1 hchilds
    · simp [next_machines] at hchilds
      obtain ⟨S, D, L, _, hchilds⟩ := hchilds
      specialize hM'childs C.state C.tape.head
      rw [← hchilds] at hM'childs
      simp at hM'childs
      rw [← hM'childs]
      simp
  · intro M' hM'
    simp [terminating_children] at hM'
    simp

    obtain hMM' := next_machines.terminates_children hM'.1 hlab hsym hCs hCt

    rcases hMM' with hMM' | ⟨Mc, hMc, Mh, hMhh, hMhc⟩
    · simp [Machine.LastState] at hMM'
      exact absurd hMM' hM'.2

    simp [Finset.mem_fold_union, Finset.mem_image, id, terminating_children]
    lift Mh to {T: Terminating l s // T.n = M'.n}
    · exact hMhh.symm.same_halt_time M'.terminates

    obtain ⟨Mh, hMhn⟩ := Mh
    simp at hMhh hMhc
    use Mh
    constructor
    swap
    · exact hMhn.symm
    use Mc
}

def m1RB (l s): Machine l s := (default: Machine l s).update_with 0 0 (.next 1 .right 1)

lemma correct_1RB (h: (BBCompute decider (m1RB l s)).undec = ∅): (BBCompute decider (m1RB l s)).val = Busybeaver' l s
(terminating_children (m1RB l s)) :=
by {
  apply correct h <;> {
    simp [used_symbols, used_states]
    left
    exists 0
    simp [m1RB]
  }
}

def m0RB (l s): Machine l s := (default: Machine l s).update_with 0 0 (.next 0 .right 1)

lemma correct_0RB (h: (BBCompute decider (m0RB l s)).undec = ∅):
  (BBCompute decider (m0RB l s)).val = Busybeaver' l s (terminating_children (m0RB l s)) :=
by {
  apply correct h <;> {
    simp [used_symbols, used_states]
    left
    use 0
    simp [m0RB]
  }
}

lemma only_0RB_1RB (hl: l ≠ 0): Busybeaver l s = Busybeaver' l s (terminating_children (m0RB l s) ∪ terminating_children (m1RB l s)) :=
by {
  rw [symm.only_right]
  apply Busybeaver'.biject_fold
  swap
  · intro M' hM'
    simp at hM'
    rcases hM' with hM' | hM' <;> {
      simp [terminating_children] at hM'
      use M'
      specialize hM' 0 0
      simp [symm.GoingTo]
      simp [m1RB, m0RB] at hM'
      rw [← hM']
      simp
    }
  intro M' hM'
  simp [symm.GoingTo] at hM'
  obtain ⟨sym, lab, hsl⟩ := hM'

  by_cases labz: lab = 0
  · suffices ¬M'.M.halts default by {
      exfalso
      apply this
      use M'.n
      exact M'.terminates
    }
    cases labz
    closed_set λ C ↦ C.state = 0 ∧ C.tape.head = 0 ∧ C.tape.right = default
    · intro ⟨A, hAs, hAh, hAr⟩
      cases hM: M'.M.step A with
      | none => {
        simp at hM
        rw [hAs, hAh, hsl] at hM
        cases hM
      }
      | some B' => {
        simp
        use B'
        constructor
        swap
        · exact Progress.single hM
        obtain ⟨sym, dir, hMA, hMB⟩ := Machine.step.some_rev hM
        rw [hAs, hAh, hsl] at hMA
        simp at hMA
        cases hMA.1.symm
        cases hMA.2.1.symm
        use hMA.2.2.symm
        simp [Turing.Tape.write, Turing.Tape.move] at hMB
        rw [hMB]
        simp
        rw [hAr]
        constructor <;> rfl
      }
    · simp
      use default
      constructor
      · constructor
        · rfl
        · constructor <;> rfl
      · exact EvStep.refl

  wlog hlab : lab = 1 generalizing M' lab
  · let Mpermed := Transformation.lift_terminating (perm.isTransformation (q:=lab) (q':=1))
      (by {
        simp [default]
        rw [Machine.swap.ne]
        · symm
          exact labz
        · simp
          exact hl
      }) M'
    apply this Mpermed 1
    simp [Mpermed, Transformation.lift_terminating, Machine.perm]
    rw [Machine.swap.ne, hsl]
    simp
    all_goals aesop

  cases hlab
  cases s
  · rw [
      show m1RB l 0 = m0RB l 0 by rfl,
    ]
    simp
    use M'
    simp [terminating_children]
    intro lab sym
    simp [m0RB]
    simp_all only [ne_eq, Fin.one_eq_zero_iff, add_left_eq_self, not_false_eq_true, Fin.isValue]
    split
    · rename_i hls
      simp_all
      cases hls.2
      exact (Fin.fin_one_eq_zero sym).symm
    · rename_i hls
      simp_all

  rename_i s
  by_cases hsym: sym = default
  · use M'
    cases hsym
    simp
    left
    simp [terminating_children]
    intro lab sym
    simp [m0RB]
    simp_all only [Fin.default_eq_zero]
    split
    · simp_all only [not_true_eq_false, imp_false, or_true]
    · simp_all only [not_and, not_false_eq_true, implies_true, true_or]

  wlog hsym' : sym = 1 generalizing M' sym
  · let Mpermed := Transformation.lift_terminating (translated.transformation (S:=sym) (S':=1)
      (by {
        symm
        exact hsym
      })
      (by {
        simp
      }))
      (by {
        simp [Turing.Tape.translate]
        congr
        rw [show (default: Config l (s + 1)).tape = default by rfl]
        exact Turing.Tape.map_default
      }) M'
    apply this 1 Mpermed
    simp [Mpermed, Transformation.lift_terminating, Machine.translated]
    rw [Machine.swap.ne, hsl]

    all_goals aesop -- Maybe a bit too violent ?

  cases hsym'
  simp at hsym
  use M'
  simp
  right

  simp [terminating_children]
  intro lab sym
  simp [m1RB]
  split
  · simp_all only [not_true_eq_false, imp_false, or_true]
  · simp_all only [not_and, not_false_eq_true, implies_true, true_or]
}

theorem correct_complete (hl: l ≠ 0) (h: (BBResult.join (BBCompute decider (m0RB l s)) (BBCompute decider (m1RB l s))).undec = ∅):
  Busybeaver l s = (BBResult.join (BBCompute decider (m0RB l s)) (BBCompute decider (m1RB l s))).val :=
by {
  simp [BBResult.join, only_0RB_1RB hl]
  simp [BBResult.join, Finset.union_eq_empty] at h
  congr
  · symm
    exact correct_0RB h.1
  · symm
    exact correct_1RB h.2
}

end BBCompute
