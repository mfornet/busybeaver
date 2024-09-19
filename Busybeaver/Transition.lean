/-
This file defines _transitions_ and their properties.

A transition is a pair (label, symbol).
-/

import Busybeaver.Basic
import Busybeaver.Reachability

namespace TM

def Machine.halting_trans (M: Machine l s) := (Finset.univ (α:=Label l × Symbol s)).filter (λ pair ↦ M pair.1 pair.2 = .halt)

@[simp]
lemma Machine.halting_trans.mem_iff {M: Machine l s}: (lab, sym) ∈ M.halting_trans ↔ M lab sym = .halt :=
  by simp [Machine.halting_trans]

def Machine.n_halting_trans (M: Machine l s) := M.halting_trans.card

def Machine.trans_reachable_from (M: Machine l s)
  (lab: Label l) (sym: Symbol s) (C: Config l s): Prop :=
  ∃B n, (C -[M]{n}-> B) ∧ B.state = lab ∧ B.tape.head = sym

def Machine.trans_unreachable_from (M: Machine l s)
  (lab: Label l) (sym: Symbol s) (C: Config l s) := ¬(M.trans_reachable_from lab sym C)

namespace Machine.halting_trans

theorem all_unreachable {M: Machine l s} (h: ∀T ∈ M.halting_trans, M.trans_unreachable_from T.1 T.2 default):
  ¬(M.halts default) :=
by {
  intro ⟨n, C, Clast, Creach⟩

  simp [Machine.LastState] at Clast
  simp [Machine.trans_unreachable_from, Machine.trans_reachable_from] at h

  specialize h C.state C.tape.head Clast C n Creach

  simp at h
}

lemma empty_loops {M: Machine l s} (h: M.halting_trans = ∅): ¬(M.halts default) :=
by {
  apply all_unreachable
  simp [h]
}

lemma eq_zero_nonhalts {M: Machine l s} (hM: M.n_halting_trans = 0): ¬M.halts default := by {
  simp [Machine.n_halting_trans] at hM
  exact empty_loops hM
}

end Machine.halting_trans
