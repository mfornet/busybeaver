-- This module serves as the root of the `Busybeaver` library.
-- Import modules here that should be built as part of the library.
import Busybeaver.Basic
import Busybeaver.Reachability

open TM

variable {l s: ℕ}

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


def Busybeaver (S: Finset (Machine l s)) (filter: (M: Machine l s) → HaltM M Unit): BBResult l s :=
  S.fold BBResult.join { val := 0, undec := {}} (λ M ↦ BBResult.from_haltm (filter M))
