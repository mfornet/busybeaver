import Busybeaver.Basic
import Busybeaver.Reachability
import Busybeaver.ClosedSet
import Busybeaver.Enumerate.Basic
import Busybeaver.Enumerate.Symmetry
import Busybeaver.Enumerate.Translate
import Busybeaver.Enumerate.Perm
import Busybeaver.Enumerate.Quotient
import Busybeaver.Deciders.NoHaltState

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
  undec : Finset (Machine l s)
deriving DecidableEq

def BBResult.join (t₁ t₂: BBResult l s): BBResult l s := {
  val := Max.max t₁.val t₂.val
  undec := t₁.undec.disjUnion t₂.undec sorry
  /- undec := t₁.undec ∪ t₂.undec -/
}

instance BBResult.join.commutative: Std.Commutative (BBResult.join (l:=l) (s:=s)) :=
by {
  constructor
  intro A B
  simp [BBResult.join]
  constructor
  · exact Nat.max_comm _ _
  · exact Finset.union_comm _ _
}

instance BBResult.join.associative: Std.Associative (BBResult.join (l:=l) (s:=s)) :=
by {
  constructor
  intro A B C
  simp [BBResult.join]
  exact Nat.max_assoc A.val B.val C.val
}

@[simp]
def BBResult.join.fold_max [DecidableEq α] {f: α → BBResult l s} {S: Finset α}:
  (Finset.fold BBResult.join B f S).val = Finset.fold Max.max B.val (λ a ↦ f a |>.val) S :=
by induction S using Finset.induction with
| empty => simp_all
| @insert a S' hA IH => simp [Finset.fold_insert hA, join, IH]

@[simp]
def BBResult.join.fold_union [DecidableEq α] {f: α → BBResult l s} {S: Finset α}:
  (Finset.fold BBResult.join B f S).undec = Finset.fold Union.union B.undec (λ a ↦ (f a).undec) S :=
by induction S using Finset.induction with
| empty => simp_all
| @insert a S' hA IH => simp [Finset.fold_insert hA, join, IH]

def BBResult.from_haltm {M: Machine l s} (h: HaltM M α): BBResult l s := match h with
| .unknown _ => { val := 0, undec := {M}}
| .halts_prf n _ _ => { val := n, undec := {}}
| .loops_prf _ => {val := 0, undec := {}}

private def used_states (M: Machine l s): (Finset (Label l)) :=
  Finset.univ (α:=Label l) |>.filter (λ l ↦ (∃sym, M l sym ≠ .halt) ∨ (∃ lab sym sym' dir, M lab sym = .next sym' dir l))

private lemma used_states.mono (h: A.state ∈ used_states M) (hAB: A -[M]{n}-> B): B.state ∈ used_states M :=
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

private lemma used_states.mono_default (h: default ∈ used_states M) (hAB: default -[M]{n}-> B):
B.state ∈ used_states M :=
by {
  simp [default] at *
  refine used_states.mono ?_ hAB
  simp
  exact h
}

private def used_symbols (M: Machine l s): Finset (Symbol s) :=
  Finset.univ (α:=Symbol s) |>.filter (λ s ↦ (∃lab, M lab s ≠ .halt) ∨ (∃lab sym dir lab', M lab sym = .next s dir lab'))

private lemma used_symbols.mono (hA: ∀ i, A.tape.nth i ∈ used_symbols M) (hAB: A -[M]{n}-> B): ∀ j, B.tape.nth j ∈ used_symbols M :=
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

private lemma used_symbols.mono_default (h: default ∈ used_symbols M) (hB: default -[M]{n}-> B):
B.tape.head ∈ used_symbols M := by {
  simp [default] at *
  refine used_symbols.mono ?_ hB 0
  intro j
  simp [Turing.Tape.nth, Turing.ListBlank.nth]
  split <;> exact h
}

private def usable_states (M: Machine l s): Finset (Label l) :=
  used_states M ∪ if hM: (Finset.univ \ used_states M).Nonempty then {(Finset.univ \ (used_states M)).min' hM} else ∅

private def usable_symbols (M: Machine l s): Finset (Symbol s) :=
  used_symbols M ∪ if hM: (Finset.univ \ used_symbols M).Nonempty then {(Finset.univ \ (used_symbols M)).min' hM} else ∅ 

private def possible_statements (M: Machine l s): Finset (Stmt l s) :=
  usable_symbols M ×ˢ Finset.univ (α:=Turing.Dir) ×ˢ usable_states M |>.image
    λ ⟨sym, dir, lab⟩ ↦ .next sym dir lab

private lemma possible_statements.all_next {M: Machine l s}:
  ∀ S ∈ possible_statements M, ∃ sym dir lab, S = .next sym dir lab :=
by {
  intro S hS
  simp [possible_statements] at hS
  obtain ⟨sym, state, dir, hS⟩ := hS
  use sym, state, dir, hS.2.symm
}

private def update_with (M: Machine l s) (lab: Label l) (sym: Symbol s) (S: Stmt l s): Machine l s :=
  λ lab' sym' ↦ if lab' = lab ∧ sym' = sym then S else M lab' sym'

private lemma update_with.le_halt_trans {M: Machine l s} {lab: Label l} {sym: Symbol s} (h: M lab sym = .halt):
  (update_with M lab sym (.next sym' dir lab')).n_halting_trans = M.n_halting_trans - 1:=
by {
  simp [Machine.n_halting_trans]
  rw [← Finset.card_erase_of_mem (s:=M.halting_trans) (a:=(lab, sym)) (by {
    simp [halting_trans]
    exact h
  })]
  simp [Machine.n_halting_trans, update_with, halting_trans]
  congr
  apply Finset.ext
  intro ⟨L, S⟩
  simp
  split
  · simp_all
  · simp_all
}

private lemma update_with.le_halt_trans' {M: Machine l s} {lab: Label l} {sym: Symbol s} (h: M lab sym = .halt) (hS: S = .next sym' dir lab'):
  (update_with M lab sym S).n_halting_trans = M.n_halting_trans - 1:=
by {
  rw [hS]
  exact update_with.le_halt_trans h
}

private def next_machines (M: Machine l s) (lab: Label l) (sym: Symbol s): Finset (Machine l s) :=
  usable_symbols M ×ˢ Finset.univ (α:=Turing.Dir) ×ˢ usable_states M |>.image
    λ ⟨S, D, L⟩ ↦ update_with M lab sym (.next S D L)

@[simp]
private lemma next_machines.halttrans_le {M: Machine l s} {lab: Label l} {sym: Symbol s} (h: M lab sym = .halt):
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

/--
Holds if the transitions of M are a superset of the transitions of M'
-/
def is_child (M M': Machine l s): Prop :=
  ∀ lab sym, M' lab sym = .halt ∨ M' lab sym = M lab sym

notation M' " ≤c " M => is_child M M'

instance is_child.decidable: DecidableRel (α:=Machine l s) is_child :=
by {
  intro M M'
  simp [is_child]
  refine @Fintype.decidableForallFintype _ _ ?_ _
  intro lab
  refine @Fintype.decidableForallFintype _ _ ?_ _
  intro sym
  simp
  apply inferInstance
}

instance is_child.isTrans: IsTrans (Machine l s) is_child :=
by {
  constructor
  intro A B C hA hB
  intro lab sym
  specialize hA lab sym
  specialize hB lab sym
  rcases hB with hB | hB
  · left
    exact hB
  rcases hA with hA | hA
  · left
    rw [← hA]
    exact hB
  right
  simp [*]
}

@[simp]
lemma is_child.refl: M ≤c M :=
by {
  intro lab sym
  right
  rfl
}

lemma is_child.step (h: M ≤c M') (hM: A -[M]-> B): A -[M']-> B :=
by {
  obtain ⟨sym, dir, hdef, hB⟩ := Machine.step.some_rev hM
  apply Machine.step.some' (sym:=A.tape.head) (sym':=sym) (dir:=dir)
  · have hMM := h A.state A.tape.head
    rcases hMM with hMM | hMM
    · rw [hdef] at hMM
      cases hMM
    · rw [hdef] at hMM
      exact hMM.symm
  · rfl
  · exact hB
}

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

lemma is_child.parent_step (h: M ≤c M') (hM': A -[M']-> B): (A -[M]-> B) ∨ M.LastState A :=
by {
  obtain ⟨sym, dir, hdef, hB⟩ := Machine.step.some_rev hM'
  rcases h A.state A.tape.head with hAs | hAs
  · right
    simp [Machine.LastState]
    exact hAs
  · left
    rw [hdef] at hAs
    exact Machine.step.some' hAs rfl hB
}

lemma is_child.multistep (h: M ≤c M') (hM: A -[M]{n}-> B): A -[M']{n}-> B :=
by induction hM with
| refl => exact .refl
| @succ A B C n' hAB _ IH => exact Multistep.succ (is_child.step h hAB) IH

lemma is_child.parent_multistep (h: M ≤c M') (hM': A -[M']{n}-> B): M.halts A ∨ (A -[M]{n}-> B) :=
by induction hM' with
| refl => {
  right
  exact .refl
}
| @succ A B C n hAB _ IH => {
  rcases h.parent_step hAB with hAB | hAB
  swap
  · left
    use 0, A
    exact ⟨hAB, Multistep.refl⟩

  rcases IH with hBh | hBC'
  · left
    apply hBh.mono (n:=1)
    exact Multistep.single hAB
  · right
    exact Multistep.succ hAB hBC'
}

lemma is_child.halt_of_halt_parent (h: M ≤c M') (hM: ¬M.halts default): ¬M'.halts default :=
by {
  intro ⟨n, C, hCl, hCr⟩
  apply hM
  simp [Machine.LastState] at hCl
  use n, C
  constructor
  · simp [Machine.LastState]
    have hC := h C.state C.tape.head
    simp [hCl] at hC
    exact hC
  · rcases h.parent_multistep hCr
    · contradiction
    · trivial
}

lemma update_with.is_child (hUpd: M sym lab = .halt): M ≤c (update_with M sym lab (.next sym' dir lab')) :=
by {
  intro nlab nsym
  simp [update_with]
  split <;> simp [*] at *
}

lemma next_machines.is_child (hM: M sym lab = .halt) (hMn: Mn ∈ next_machines M sym lab): M ≤c Mn :=
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

lemma next_machines.terminates_children (hCl: M.LastState C) (hCr: default -[M]{n}-> C) (hM': M ≤c M'):
    (M'.LastState C) ∨ (∃Mc ∈ next_machines M C.state C.tape.head, ∃Mh, (Mh ~m M') ∧ Mc ≤c Mh) :=
by match hM'C: M' C.state C.tape.head with
| .halt => {
  left
  simp [Machine.LastState]
  exact hM'C
}
| .next sym dir lab => {
  sorry
    /-
    The tricky bit of the proof.

    Any child machine with a non-halting transition at C is equivalent to a next_machine':
    - if the transition uses already used states/symbols, then it is itself a child of a
      next_machine'
    - otherwise, "normalize" the machine into a machine using the successor of the sates/symbols
      this one is a next_machine'

    This in turns creates 4 subcases, each of which need to be handled independently.
    intro M' hM'
    simp [terminating_children] at hM'
    cases hM's: M'.M C.state C.tape.head
    · simp [hM's] at hM'
    rename_i sym dir lab
    simp [hM's] at hM'
    simp only [id_eq, exists_exists_and_eq_and, terminating_children]
    by_cases hsym': sym ∈ used_symbols M <;> by_cases hlab': lab ∈ used_states M
    · /-
      First case, the new machine uses already used states and symbols.
      This is the "easy" case as it does not require any permuation.
      -/
      exists M'
      simp
      exists update_with M C.state C.tape.head (.next sym dir lab)
      constructor
      · constructor
        · simp [TM.Busybeaver.next_machines']
          exists sym
          exists dir
          exists lab
          simp [TM.Busybeaver.usable_symbols, TM.Busybeaver.usable_states, hsym', hlab']
        · exact TM.Busybeaver.update_with.le_halt_trans Clast.1
      · intro sym' lab'
        simp [TM.Busybeaver.update_with]
        split
        · rename_i heq
          simp
          rw [heq.1, heq.2]
          exact hM's.symm
        · exact hM' sym' lab'
    · /-
      Second case, the symbol is already used, but the label is not
      -/
      have unused_states: (Finset.univ \ used_states M).Nonempty := by {
        exists lab
        simp
        exact hlab'
      }
      let newlab := (Finset.univ \ used_states M).min' unused_states

      have hnlab : newlab ∉ used_states M := by {
        suffices newlab ∈ (Finset.univ \ used_states M) by {
          simp at this
          exact this
        }
        exact Finset.min'_mem _ unused_states
      }

      /-
      This is the "normalized machine".

      It uses the next usable state instead of any unused state
      -/
      exists (TM.Machine.perm.isTransformation (q:=lab) (q':=newlab)).lift_terminating (by {
        congr
        apply TM.Machine.swap.ne
        · simp [default]
          intro hlab''
          apply absurd hlab
          simp
          rw [hlab'']
          exact hlab'
        · simp [default]
          intro hlab''
          apply absurd hlab
          simp
          rw [hlab'']
          exact hnlab
      }) M'
      constructor
      swap
      · simp [Transformation.lift_terminating]

      /-
      This is the parent of the normalized machine, that is the machine that covers the normalized
      machine during its recursive call
      -/
      exists ⟨update_with M C.state C.tape.head (.next sym dir newlab), update_with.le_halt_trans Clast.1⟩
      constructor
      · simp [next_machines']
        exists sym
        exists dir
        exists newlab
        simp
        constructor
        · simp [usable_symbols, hsym']
        · simp [usable_states, unused_states]
      · simp [Transformation.lift_terminating]
        have hM'perm : M ≤c M'.M.perm lab newlab := is_child.perm_unused_states hM' hlab' hnlab
        have hUpd : M ≤c update_with M C.state C.tape.head (.next sym dir newlab) := update_with.is_child Clast.1
        intro lab' sym'
        simp [update_with]
        split
        · simp
          rename_i heq
          rw [heq.1, heq.2] at *
          suffices C.state ≠ lab ∧ C.state ≠ newlab by {
            simp [perm, Machine.swap.ne this.1 this.2]
            split
            · rename_i heq
              rw [hM's] at heq
              cases heq
            rename_i heq
            rw [hM's] at heq
            cases heq
            simp
          }
          constructor
          · intro hCslab
            rw [← hCslab] at hlab'
            exact hlab' hCs
          · intro hCsnlab
            rw [← hCsnlab] at hnlab
            exact hnlab hCs
        · exact hM'perm lab' sym'
    · sorry
    · sorry
    -/
}


lemma is_child.halt_trans_sub (h: M ≤c M'): M'.halting_trans ⊆ M.halting_trans :=
by {
  intro ⟨sym, lab⟩ hS
  simp [Machine.halting_trans] at *
  cases h sym lab <;> simp_all only
}

lemma is_child.ne_halt_trans_ssub (h: M ≤c M') (h': M ≠ M'): M'.halting_trans ⊂ M.halting_trans :=
by {
  apply ssubset_of_subset_not_subset
  · exact halt_trans_sub h
  intro hM
  apply h'
  funext lab sym
  rcases h lab sym with hsl | hsl
  swap
  · exact hsl
  have hls' : ⟨lab, sym⟩ ∈ M.halting_trans := by {
    simp [Machine.halting_trans]
    exact hsl
  }
  specialize hM hls'
  simp [Machine.halting_trans] at hM
  simp_all only
}

lemma is_child.ne_exists_halt_trans (h: M ≤c M') (h': M ≠ M'):
  ∃sym lab sym' dir lab', M sym lab = .halt ∧ M' sym lab = .next sym' dir lab' :=
by {
  suffices ∃t ∈ M.halting_trans, t ∉ M'.halting_trans by {
    simp [Machine.halting_trans] at this
    obtain ⟨sym, lab, hl, hne⟩ := this
    use sym, lab
    simp
    constructor
    · exact hl
    cases hM' : M' sym lab with
    | halt => contradiction
    | next sym' dir lab' => {
      exists sym'
      exists dir
      exists lab'
    }
  }
  apply Finset.exists_of_ssubset
  exact is_child.ne_halt_trans_ssub h h'
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

noncomputable def terminating_children (M: Machine l s): Finset (Terminating l s) :=
  Finset.univ.filter (λ M' ↦ M ≤c M'.M)

lemma n_halting_trans.eq_zero_nonhalts (hM: M.n_halting_trans = 0): ¬M.halts default := by {
  simp [Machine.n_halting_trans, halting_trans, Finset.filter_eq_empty_iff] at hM
  exact Machine.halts_of_no_halt hM
}

lemma terminating_children.zero_transitions (hM: M.n_halting_trans = 0): terminating_children M = ∅ :=
by {
  apply Finset.eq_empty_of_forall_not_mem
  intro M' hM'
  simp [terminating_children] at hM'
  have hMnohalts := n_halting_trans.eq_zero_nonhalts hM
  simp [init] at hMnohalts
  apply hM'.halt_of_halt_parent hMnohalts
  use M'.n
  exact M'.terminates
}

lemma terminating_children.one_transition (hMt: M.halts_in n default) (hM: M.n_halting_trans = 1): terminating_children M = {⟨M, n, hMt⟩} :=
by {
  sorry
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
    apply n_halting_trans.eq_zero_nonhalts hMnz
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
    (terminating_children M).filter (λ M ↦ M.M C.state C.tape.head = .halt) ∪ (terminating_children M).filter (λ M ↦ M.M C.state C.tape.head ≠ .halt) := by {
    apply Finset.ext
    intro M
    cases hM: M.M C.state C.tape.head <;> simp_all
  }
  rw [hTerm]
  simp

  /-
  First case, the child machine has the same halting transition as M, that is, it halts.
  In this case in terminates in the same number of steps as M
  -/
  have hSameM : Busybeaver' l s ((terminating_children M).filter (λ M ↦ M.M C.state C.tape.head =
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
    | @insert A S hA IH => {
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
      simp [update_with] at hM'childs
      rw [← hM'childs]
      simp
  · intro M' hM'
    simp [terminating_children] at hM'
    obtain hMM' := next_machines.terminates_children (by {
      simp [Machine.LastState]
      exact Clast.1
    }) Clast.2 hM'.1
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

def m1RB (l s): Machine l s := λ lab sym ↦ if lab = 0 ∧ sym = 0 then .next 1 .right 1 else .halt

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

def m0RB (l s): Machine l s := λ lab sym ↦ if lab = 0 ∧ sym = 0 then .next 0 .right 1 else .halt

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

lemma only_0RB_1RB: Busybeaver l s = Busybeaver' l s (terminating_children (m0RB l s) ∪ terminating_children (m1RB l s)) :=
by {
  rw [symm.only_right]
  apply Busybeaver'.biject_fold
  · sorry
  · sorry
}

theorem correct_complete (h: (BBResult.join (BBCompute decider (m0RB l s)) (BBCompute decider (m1RB l s))).undec = ∅):
  Busybeaver l s = (BBResult.join (BBCompute decider (m0RB l s)) (BBCompute decider (m1RB l s))).val :=
by {
  simp [BBResult.join, only_0RB_1RB]
  simp [BBResult.join, Finset.union_eq_empty] at h
  congr
  · symm
    exact correct_0RB h.1
  · symm
    exact correct_1RB h.2
}

end BBCompute
