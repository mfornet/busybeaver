/-
Definition and lemmas about the Busy beaver problem
-/
import Busybeaver.Basic
import Busybeaver.Reachability
namespace TM

open TM.Machine

variable {M: Machine l s}

structure Terminating (l s: ℕ) where
  M: Machine l s
  n: ℕ
  terminates: M.halts_in n default
deriving DecidableEq

instance Machine.canLiftTerminating: CanLift (Machine l s) {T : Terminating l s // T.n = n } (λ M ↦ M.val.M) (λ M ↦ M.halts_in n default) where
  prf M hM := by {
    simp
    use ⟨M, n, hM⟩
  }

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
  simp [Machine.get]
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
lemma upper_bound (h: ∀(M: Machine l s), (∃ B, (default -[M]{n}-> B)) → ¬(M.halts default)):
  Busybeaver l s < n :=
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
