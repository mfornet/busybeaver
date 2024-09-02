/-
Definition and lemmas about the Busy beaver problem
-/
import Busybeaver.Basic
import Busybeaver.Reachability
import Busybeaver.Enumerate.Perm
import Busybeaver.Enumerate.Basic
import Busybeaver.Enumerate.Symmetry
import Busybeaver.Enumerate.Quotient

namespace TM

open TM.Machine

variable {M: Machine l s}

structure Terminating (l s: ℕ) where
  M: Machine l s
  n: ℕ
  terminates: M.halts_in n default
deriving DecidableEq

noncomputable instance Terminating.fintype: Fintype (Terminating l s) := by {
  apply Fintype.ofInjective Terminating.M
  intro ⟨AM, An, At⟩ ⟨BM, Bn, Bt⟩ hABM
  simp_all
  rw [← hABM] at Bt
  exact Machine.halts_in.deterministic At Bt
}

instance Terminating.inhabited: Inhabited (Terminating l s) := ⟨default, 0, by {
  conv =>
    pattern default (α:=Machine l s)
    simp [default]
  exists default
  constructor
  swap
  · apply Machine.Multistep.refl
  unfold Machine.LastState
  simp
}⟩

def Busybeaver' (l s: ℕ) (S: Finset (Terminating l s)): ℕ :=
  S.image Terminating.n |>.fold max 0 id

namespace Busybeaver'

lemma max {M: Terminating l s} {S: Finset (Terminating l s)} (hM: M ∈ S) : M.n ≤ Busybeaver' l s S :=
by {
  unfold Busybeaver'
  induction S using Finset.induction with
  | empty => cases hM
  | @insert  M' S' _ IH => {
    simp at hM
    rcases hM with hM | hM <;> simp_all
  }
}

lemma cons {M: Terminating l s} (hM: M ∉ S): Busybeaver' l s (Finset.cons M S hM) = Max.max M.n (Busybeaver' l s S) :=
by {
  conv =>
    lhs
    unfold Busybeaver'
    simp
  rfl
}

@[simp]
lemma empty: Busybeaver' l s ∅ = 0 :=
  by simp [Busybeaver']

@[simp]
lemma singleton {M: Terminating l s}: Busybeaver' l s {M} = M.n :=
by simp [Busybeaver', Multiset.fold]

@[simp]
lemma insert {M: Terminating l s}: Busybeaver' l s (insert M S) = Max.max M.n (Busybeaver' l s S) :=
by {
  by_cases hM: M ∈ S
  · rw [Finset.insert_eq_of_mem hM]
    rw [Nat.max_eq_right (Busybeaver'.max hM)]
  rw [← Finset.cons_eq_insert M S hM]
  exact cons hM
}

lemma get (h: S.Nonempty): ∃M ∈ S, M.n = Busybeaver' l s S :=
by induction h using Finset.Nonempty.cons_induction with
| singleton a => {
  exists a
  simp [Busybeaver', Multiset.fold]
}
| cons M' S' hM' _ ex => {
  obtain ⟨MS, hMSin, hMSmax⟩ := ex
  by_cases hMSM': MS.n < M'.n
  · exists M'
    simp_all
    exact (max_eq_left_of_lt hMSM').symm

  simp at hMSM'

  rcases Nat.lt_or_eq_of_le hMSM' with _ | hMSM'
  · exists MS
    simp_all
  exists MS
  simp_all
}

@[simp]
lemma union_max : Busybeaver' l s (S ∪ S') = Max.max (Busybeaver' l s S) (Busybeaver' l s S') :=
by induction S' using Finset.induction with
| empty => simp
| @insert A S' _ IH => {
  conv =>
    lhs
    rw [Finset.union_comm, Finset.insert_union, Finset.union_comm]
    simp
  simp
  conv =>
    rhs
    rw [Max.left_comm]
  simp [IH]
}

lemma union_left : Busybeaver' l s S ≤ Busybeaver' l s (S ∪ S') :=
by simp

lemma union_right : Busybeaver' l s S' ≤ Busybeaver' l s (S ∪ S') :=
by simp

/-
If S can be "embedded" in S' in terms of termination, then the busybeaver' function on these sets is
monotonic.
-/
lemma fold_into {S S': Finset (Terminating l s)} (h: ∀M ∈ S, ∃M' ∈ S', M.n = M'.n): Busybeaver' l s S ≤ Busybeaver' l s S' :=
by induction S using Finset.induction with
| empty => simp
| @insert A S _ IH => {
  simp at h
  simp
  constructor
  swap
  · exact IH h.2
  obtain ⟨M', hM', hM'A⟩ := h.1
  rw [hM'A]
  exact Busybeaver'.max hM'
}

lemma biject_fold {S S': Finset (Terminating l s)} (hS: ∀M ∈ S, ∃M' ∈ S', M.n = M'.n) (hS': ∀M' ∈ S', ∃M ∈ S, M'.n = M.n):
  Busybeaver' l s S = Busybeaver' l s S' :=
by {
  apply Nat.le_antisymm
  · exact fold_into hS
  · exact fold_into hS'
}

lemma mono (hS: S ⊆ S') : Busybeaver' l s S ≤ Busybeaver' l s S' := by {
  conv_rhs =>
    rw [← Finset.sdiff_union_of_subset hS, Finset.union_comm]
  exact union_left
}

lemma upper_bound (hS: ∀ M ∈ S, M.n ≤ n): Busybeaver' l s S ≤ n :=
by induction S using Finset.induction with
| empty => simp
| @insert A S _ IH => {
  simp at hS
  obtain ⟨hAn, hIH⟩ := hS
  specialize IH hIH
  simp [*]
}

lemma upper_bound_of_lt (hS: ∀M ∈ S, M.n < n) (hn: 0 < n): Busybeaver' l s S < n :=
by induction S using Finset.induction with
| empty => exact hn
| @insert A S _ IH => {
  simp at hS
  obtain ⟨hAn, hIH⟩ := hS
  simp [IH hIH, hAn]
}

/-
Tiny lemma to show that is all the machines in a set have the same halting time then it is easy to
compute the Busybeaver' function
-/
lemma eq_of_all_eq (hSn: S.Nonempty) (hSa: ∀ M ∈ S, M.n = n) : Busybeaver' l s S = n :=
by induction hSn using Finset.Nonempty.cons_induction <;> simp_all

lemma fold_max_eq_fold_union {S: Finset (Finset (Terminating l s))}: Finset.fold Max.max 0 (Busybeaver' l
s) S = Busybeaver' l s (Finset.fold Union.union ∅ id S) :=
by induction S using Finset.induction with
| empty => simp
| @insert A S _ IH => simp [IH]

end Busybeaver'

noncomputable def Busybeaver (l s: ℕ) := Busybeaver' l s Finset.univ

namespace Busybeaver

/--
Any terminating machine runs for at most BB(l,s) steps
-/
lemma max {M: Terminating l s}: M.n ≤ Busybeaver l s :=
  Busybeaver'.max (Finset.mem_univ M)

lemma max' {M: Machine l s} (hM: M.halts_in n default): n ≤ Busybeaver l s :=
  @max l s { M := M, n := n, terminates := hM }

/--
If a machine runs for more than BB(l,s) steps, then it does not terminate
-/
lemma not_halts {M: Machine l s} (hM: default -[M]{k}-> B) (hk: Busybeaver l s < k): ¬(M.halts default) := by {
  intro ⟨n, hn⟩
  suffices k < k from (lt_self_iff_false k).mp this
  calc k
    _ ≤ n := hn.within hM
    _ ≤ Busybeaver l s := @max l s ⟨M, n, hn⟩
    _ < k := hk
}

/-
There exists a busy beaver machine
-/
lemma get_max: ∃(M: Terminating l s), M.n = Busybeaver l s :=
by {
  unfold Busybeaver
  obtain ⟨M, _, hMm⟩ := Busybeaver'.get (l:=l) (s:=s) (S:=Finset.univ) Finset.univ_nonempty
  exists M
}

/-
If we can prove that any machine running for more than n steps does not halt, then the busy beaver
number is smaller than that
-/
lemma upper_bound (h: ∀(M: Machine l s), (∃ B, (default -[M]{n}-> B)) → ¬(M.halts default)): Busybeaver
l s < n :=
by {
  obtain ⟨Mm, hMm⟩ := get_max (l:=l) (s:=s)
  by_contra hM
  simp at hM
  rw [← hMm] at hM
  specialize h Mm.M (Mm.terminates.split hM)
  unfold Machine.halts at h
  simp at h
  exact absurd Mm.terminates (h Mm.n)
}

end Busybeaver

namespace Machine.Transformation

/-
Some properties of transformations with regard to busy beavers.
-/

def lift_terminating [inst: Transformation (l:=l) (s:=s) fC fM] (hfC: fC default = default): Terminating l s → Terminating l s :=
  λ M ↦ {
    M := fM M.M,
    n := M.n,
    terminates := by {
      rw [← hfC]
      exact same_halt_time M.terminates
    }
  }

@[simp]
lemma lift_terminating.halt_steps [inst: Transformation (l:=l) (s:=s) fC fM] {M: Terminating l s}:
(inst.lift_terminating hfC M).n = M.n :=
by simp [lift_terminating]

theorem same_busybeaver [inst: Transformation fC fM] {S: Finset (Terminating l s)} (hfC: fC default = default): Busybeaver' l s
S = Busybeaver' l s (S.image (inst.lift_terminating hfC)) :=
by induction S using Finset.induction with
| empty => simp
| @insert A S _ IH => simp [IH]

lemma same_busybeaver' [inst: Transformation fC fM] {S: Finset (Terminating l s)}
(hfC: fC default = default) (hS': S' = (S.image (inst.lift_terminating hfC))): Busybeaver' l s S = Busybeaver' l s S' :=
by {
  rw [hS']
  exact same_busybeaver hfC
}

end Machine.Transformation

section Symmetry

noncomputable def GoingTo (l s : ℕ) (dir: Turing.Dir) :=
  Finset.univ (α:=Terminating l s) |>.filter (λ M ↦ ∃ sym nlab, M.M default default = .next sym dir nlab)

noncomputable def DirectHalts (l s: ℕ) :=
  Finset.univ (α:=Terminating l s) |>.filter (λ M ↦ M.M default default = .halt)

lemma right_eq_left: Busybeaver' l s (GoingTo l s .right) = Busybeaver' l s (GoingTo l s .left) :=
by {
  apply symm.transformation.same_busybeaver' symm.config_reverse.default
  apply Finset.ext
  intro M
  unfold GoingTo Transformation.lift_terminating
  simp
  constructor
  · intro ⟨sym, nlab, h⟩
    exists (symm.transformation.lift_terminating symm.config_reverse.default) M
    simp [Transformation.lift_terminating, symm.involutive M.M]
    exists sym
    exists nlab
    simp [Machine.symm, h, Turing.Dir.other]
  · intro ⟨M', ⟨sym, nlab, hsym⟩, hM'⟩
    exists sym
    exists nlab
    rw [show M.M = M'.M.symm by rw [← hM']]
    simp [Machine.symm, hsym, Turing.Dir.other]
}

theorem univ_eq_union: Finset.univ = (GoingTo l s .right) ∪ (GoingTo l s .left) ∪ (DirectHalts l s) :=
by {
  apply Finset.ext
  intro M
  simp [GoingTo, DirectHalts]
  cases M.M default default <;> simp_all [Turing.Dir.eq_left_or_eq_right.symm]
}

/-
To compute the busy beaver, it is enough to only consider machine going to the right
-/
theorem only_right: Busybeaver l s = Busybeaver' l s (GoingTo l s .right) :=
by {
  unfold Busybeaver
  conv =>
    lhs
    pattern Finset.univ
    rw [univ_eq_union]
  simp [right_eq_left]
  suffices Busybeaver' l s (DirectHalts l s) = 0 by {
    simp [this]
  }
  apply Nat.eq_zero_of_le_zero
  apply Busybeaver'.upper_bound
  intro ⟨M, n, term⟩ hHalts
  simp_all [DirectHalts]
  have hMh: M.halts_in 0 default := by {
    exists default
    constructor
    · unfold LastState
      simp [default]
      exact hHalts
    · exact Multistep.refl
  }
  exact term.deterministic hMh
}

end Symmetry

namespace Busybeaver

structure BBResult (l s: ℕ) where
  val : ℕ
  undec : Finset (Machine l s)
deriving DecidableEq

def BBResult.join (t₁ t₂: BBResult l s): BBResult l s := {
  val := Max.max t₁.val t₂.val
  undec := t₁.undec ∪ t₂.undec
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

instance Finset.instUnionComm [DecidableEq α]: Std.Commutative (α:=Finset α) Union.union :=
by {
  constructor
  intro a b
  exact Finset.union_comm _ _
}

instance Finset.instUnionAssoc [DecidableEq α]: Std.Associative (α:=Finset α) Union.union :=
by {
  constructor
  intro a b c
  exact Finset.union_assoc _ _ _
}

@[simp]
lemma Finset.fold_union_empty [DecidableEq α] [DecidableEq β] {f: α → Finset β} {S: Finset α}:
  Finset.fold Union.union ∅ f S = ∅ ↔ ∀ a ∈ S, f a = ∅ :=
by induction S using Finset.induction with
| empty => simp
| @insert A S _ IH => simp [Finset.union_eq_empty, IH]

@[simp]
lemma Finset.mem_fold_union [DecidableEq α] [DecidableEq β] {f: α → Finset β} {S: Finset α} {b : β}:
  b ∈ Finset.fold Union.union ∅ f S ↔ ∃ a ∈ S, b ∈ f a :=
by induction S using Finset.induction with
| empty => simp
| @insert A S _ IH => simp [IH]

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

private def used_symbols (M: Machine l s): Finset (Symbol s) :=
  Finset.univ (α:=Symbol s) |>.filter (λ s ↦ (∃lab, M lab s ≠ .halt) ∨ (∃lab sym dir lab', M lab sym = .next s dir lab'))

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
  exists sym
  exists state
  exists dir
  exact hS.2.symm
}

private def update_with (M: Machine l s) (lab: Label l) (sym: Symbol s) (S: Stmt l s): Machine l s :=
  λ lab' sym' ↦ if lab' = lab ∧ sym' = sym then S else M lab' sym'

private lemma update_with.le_halt_trans {M: Machine l s} {lab: Label l} {sym: Symbol s} (h: M lab sym = .halt):
  (update_with M lab sym (.next sym' dir lab')).n_halting_trans < M.n_halting_trans :=
by {
  simp [Machine.n_halting_trans, update_with, halting_trans]
  apply Finset.card_lt_card
  apply ssubset_of_subset_not_subset
  · intro trans htrans
    simp_all
    split at htrans <;> simp_all
  · rw [Finset.not_subset]
    exists (lab, sym)
    simp
    exact h
}

private lemma update_with.le_halt_trans' {M: Machine l s} {lab: Label l} {sym: Symbol s} (h: M lab sym = .halt) (hS: S = .next sym' dir lab'):
  (update_with M lab sym S).n_halting_trans < M.n_halting_trans :=
by {
  rw [hS]
  exact update_with.le_halt_trans h
}

private def next_machines (M: Machine l s) (lab: Label l) (sym: Symbol s): Finset (Machine l s) :=
  possible_statements M |>.image (update_with M lab sym)

@[simp]
private lemma halttrans_le {M: Machine l s} {lab: Label l} {sym: Symbol s} (h: M lab sym = .halt):
  ∀ M' ∈ next_machines M lab sym, M'.n_halting_trans < M.n_halting_trans :=
by {
  intro M' hM'
  simp [next_machines] at hM'
  obtain ⟨S, hSS, hSM'⟩ := hM'
  rw [← hSM']
  obtain ⟨sym', dir, lab', hS⟩ := possible_statements.all_next S hSS
  apply update_with.le_halt_trans' h hS
}

private def next_machines' (M: Machine l s) (lab: Label l) (sym: Symbol s) (hS: M lab sym = .halt): Finset { M': Machine l s // M'.n_halting_trans < M.n_halting_trans} :=
  usable_symbols M ×ˢ Finset.univ (α:=Turing.Dir) ×ˢ usable_states M |>.image (λ ⟨sym', dir, lab'⟩ ↦
  ⟨update_with M lab sym (.next sym' dir lab'), update_with.le_halt_trans hS⟩)

/--
TNF enumeration function.

This enumerates TMs in TNF form starting from M and tries to decide
them using the decider. It blocks the unwrapping at undecided TMs.
-/
def BBCompute (decider: (M': Machine l s) → HaltM M' Unit) (M: Machine l s): BBResult l s :=
match decider M with
| .loops_prf _ => { val := 0, undec := {} } -- If this one loops, then the descendents also loop
| .halts_prf n C hC =>
  Finset.fold BBResult.join { val := n, undec := {} } (λ M ↦ BBCompute decider M.val) $
  (next_machines' M C.state C.tape.head (by {
    obtain ⟨hC, _⟩ := hC
    simp [Machine.LastState] at hC
    exact hC
  }))
| .unknown _ => { val := 0, undec := {M} } -- This machine is undecided, no need to go further
termination_by M.n_halting_trans

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

lemma is_child.used_states (h: M ≤c M'): used_states M ⊆ used_states M' :=
by {
  intro lab hlab
  simp [TM.Busybeaver.used_states] at *
  rcases hlab with ⟨sym, hM⟩ | ⟨lab', sym, sym', dir, hM⟩
  · left
    exists sym
    specialize h lab sym
    simp [hM] at h
    rw [← h]
    exact hM
  · right
    exists lab'
    exists sym
    exists sym'
    exists dir
    specialize h lab' sym
    simp [hM] at h
    exact h.symm
}

lemma is_child.used_symbols (h: M ≤c M'): used_symbols M ⊆ used_symbols M' :=
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
    exists lab
    exists sym'
    exists dir
    exists lab'
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
    exists 0
    exists A
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
  exists n
  exists C
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

lemma next_machines.is_child (hMn: Mn ∈ next_machines' M sym lab hM): M ≤c Mn.val :=
by {
  obtain ⟨Mn, _⟩ := Mn
  simp [*] at *
  simp [next_machines'] at hMn
  obtain ⟨sym', dir, lab', _, hdMn⟩ := hMn
  rw [← hdMn]
  exact update_with.is_child hM
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

lemma next_machines'.is_child (h: M' ∈ next_machines' M lab sym hM): M ≤c M' :=
by {
  simp [next_machines'] at h
  obtain ⟨sym', dir, lab', _, hM'⟩ := h
  cases hM'
  simp
  exact update_with.is_child hM
}

lemma is_child.ne_exists_halt_trans (h: M ≤c M') (h': M ≠ M'):
  ∃sym lab sym' dir lab', M sym lab = .halt ∧ M' sym lab = .next sym' dir lab' :=
by {
  suffices ∃t ∈ M.halting_trans, t ∉ M'.halting_trans by {
    simp [Machine.halting_trans] at this
    obtain ⟨sym, lab, hl, hne⟩ := this
    exists sym
    exists lab
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

noncomputable def terminating_children (M: Machine l s): Finset (Terminating l s) :=
  Finset.univ.filter (λ M' ↦ M ≤c M'.M)

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
| case3 M a dec => simp [BBCompute, dec] at h -- The machine is unknown, contradictory because undec = {}
| case2 M nh C Clast h' IH => { -- The machine halts in nh steps, in Clast the last state
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
  simp only [h', BBResult.join.fold_union, Finset.fold_union_empty] at h

  simp [Machine.LastState] at Clast

  /-
  A "simplified" version of the induction hypothesis.
  -/
  have hMn: ∀ Mn ∈ (next_machines' M C.state C.tape.head Clast.1), (BBCompute decider Mn).val = Busybeaver' l s (terminating_children Mn) := by {
    intro Mn Hmn
    have hMchild := next_machines'.is_child Hmn
    apply IH Mn
    · exact h Mn Hmn
    · exact hMchild.used_symbols hsym
    · exact hMchild.used_states hlab
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

  /-
  Here starts a calculatory part of the proof where we simplify the goal
  to be only about the child machines.
  -/
  calc Finset.fold Max.max nh (λ M' ↦ (BBCompute decider M'.val).val) (next_machines' M C.state C.tape.head Clast.1)
    _ = Finset.fold Max.max nh (λ M' ↦ Busybeaver' l s (terminating_children M'.val)) (next_machines' M C.state C.tape.head Clast.1) := by {
    apply Finset.fold_congr
    intro M' hM'
    exact hMn M' hM'
  }
    _  = Finset.fold Max.max nh (Busybeaver' l s) (
      (next_machines' M C.state C.tape.head Clast.1).image (λ M' ↦ terminating_children M'.val)
    ) := by simp [Finset.fold_image_idem]
    _ = Max.max nh (Finset.fold Max.max 0 (Busybeaver' l s) (
      (next_machines' M C.state C.tape.head Clast.1).image (λ M' ↦ terminating_children M'.val)
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

  apply Busybeaver'.biject_fold
  · intro M' hM'
    exists M'
    simp
    simp only [Finset.mem_fold_union, Finset.mem_image, id] at hM'
    obtain ⟨childs, hchilds, hM'childs⟩ := hM'
    obtain ⟨nextM, hnextM, hchilds⟩ := hchilds
    cases hchilds
    simp [terminating_children] at hM'childs
    constructor
    · simp [terminating_children]
      calc
        is_child M'.M nextM.val := hM'childs
        is_child nextM.val M := next_machines'.is_child hnextM
    · simp [next_machines'] at hnextM
      obtain ⟨sym', dir, lab', hs, hdef⟩ := hnextM
      cases hdef
      simp at hM'childs
      specialize hM'childs C.state C.tape.head
      simp [update_with] at hM'childs
      rw [← hM'childs]
      simp
  · /-
    The tricky bit of the proof.

    Any child machine with a non-halting transition at C is equivalent to a next_machine':
    - if the transition uses already used states/symbols, then it is itself a child of a
      next_machine'
    - otherwise, "normalize" the machine into a machine using the successor of the sates/symbols
      this one is a next_machine'

    This in turns creates 4 subcases, each of which need to be handled independently.
    -/
    intro M' hM'
    simp [terminating_children] at hM'
    simp only [Finset.mem_fold_union, Finset.mem_image]
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
          sorry
        · sorry
    · sorry
    · sorry
}

/- instance is_descendant.decidable: DecidableRel (α:=Machine l s) is_descendant := -/
/- by { -/
/-   unfold is_descendant DecidableRel -/
/-   intro A B -/
/-   induction A ≤d B -/
/- } -/
/- def descendants (M: Machine l s): Finset (Machine l s) := -/
/-   Finset.univ (α:=Machine l s) |>.filter (λ M' ↦ M ≤d M') -/
/-
theorem correct (h: BBCompute decider M = { val := n, undec := {}}): Busybeaver' l s M.children = n := by {
  trivial
}

-/

end BBCompute
/-
namespace TM

/--
The busybeaver number with only one state is 1.

The numbers are slightly off because of the definitions of the various components.
-/
theorem Busybeaver.one_state: Busybeaver 0 s = 0 :=
by {
  simp [only_right]
  apply Nat.eq_zero_of_le_zero
  apply Nat.le_of_lt_add_one
  apply Busybeaver'.upper_bound_of_lt
  swap
  · simp

  intro ⟨M, n, term⟩ hM
  simp [GoingTo] at *
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
  suffices ClosedSet M (λ C ↦ C.state = default ∧ C.tape.head = default ∧ C.tape.right = default) default from this.nonHalting

  constructor
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

end TM
-/
