-- This module serves as the root of the `Busybeaver` library.
-- Import modules here that should be built as part of the library.
import Busybeaver.Basic
import Busybeaver.Reachability

open TM

variable {l s: ℕ}

section BusybeaverDef

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
  S.val.map Terminating.n |>.fold max 0

lemma Busybeaver'.max {S: Finset (Terminating l s)} (hM: M ∈ S) : M.n ≤ Busybeaver' l s S :=
by {
  unfold Busybeaver'
  induction S using Finset.induction with
  | empty => cases hM
  | @insert  M' S' hM' IH => {
    simp at hM
    rcases hM with hM | hM <;> simp_all
  }
}

noncomputable def Busybeaver (l s: ℕ) := Busybeaver' l s Finset.univ

namespace Busybeaver

/--
Any terminating machine runs for at most BB(l,s) steps
-/
lemma max {M: Terminating l s}: M.n ≤ Busybeaver l s := by {
  unfold Busybeaver
  apply Busybeaver'.max
  exact Finset.mem_univ M
}

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

end Busybeaver

end BusybeaverDef

def filterWith (S: Finset (Machine l s)) (filter: (M: Machine l s) → HaltM M Unit): Finset (Machine l s) :=
  S.filter $ λ m ↦ ¬(filter m |>.decided)

structure BBResult (l s: ℕ) where
  val : ℕ
  undec : Finset (Machine l s)

def BBResult.join (t₁ t₂: BBResult l s): BBResult l s := {
  val := max t₁.val t₂.val
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

def BBResult.from_haltm {M: Machine l s} (h: HaltM M α): BBResult l s := match h with
| .unknown _ => { val := 0, undec := {M}}
| .halts_prf n _ => { val := n, undec := {}}
| .loops_prf _ => {val := 0, undec := {}}


def BBcompute (S: Finset (Machine l s)) (filter: (M: Machine l s) → HaltM M α): BBResult l s :=
  S.fold BBResult.join { val := 0, undec := {}} (λ M ↦ BBResult.from_haltm (filter M))
