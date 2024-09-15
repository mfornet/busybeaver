/-
A definition of an order for turing machines.
-/
import Busybeaver.Basic
import Busybeaver.Reachability
import Busybeaver.Problem
import Busybeaver.Deciders.NoHaltState

namespace TM.Machine

def is_child (M M': Machine l s): Prop :=
  ∀ lab sym, M' lab sym = .halt ∨ M' lab sym = M lab sym

notation M' " ≤c " M => is_child M M'

namespace is_child

instance decidable: DecidableRel (α:=Machine l s) is_child :=
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

instance isTrans: IsTrans (Machine l s) is_child :=
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

variable {M M': Machine l s}

@[simp]
lemma refl: M ≤c M :=
by {
  intro lab sym
  right
  rfl
}

lemma step (h: M ≤c M') (hM: A -[M]-> B): A -[M']-> B :=
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

lemma parent_step (h: M ≤c M') (hM': A -[M']-> B): (A -[M]-> B) ∨ M.LastState A :=
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

lemma multistep (h: M ≤c M') (hM: A -[M]{n}-> B): A -[M']{n}-> B :=
by induction hM with
| refl => exact .refl
| @succ A B C n' hAB _ IH => exact Multistep.succ (is_child.step h hAB) IH

lemma parent_multistep (h: M ≤c M') (hM': A -[M']{n}-> B): M.halts A ∨ (A -[M]{n}-> B) :=
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

lemma halt_of_halt_parent (h: M ≤c M') (hM: ¬M.halts default): ¬M'.halts default :=
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

lemma halt_trans_sub (h: M ≤c M'): M'.halting_trans ⊆ M.halting_trans :=
by {
  intro ⟨sym, lab⟩ hS
  simp [Machine.halting_trans] at *
  cases h sym lab <;> simp_all only
}

lemma ne_halt_trans_ssub (h: M ≤c M') (h': M ≠ M'): M'.halting_trans ⊂ M.halting_trans :=
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

lemma ne_exists_halt_trans (h: M ≤c M') (h': M ≠ M'):
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

end is_child

noncomputable def terminating_children (M: Machine l s): Finset (Terminating l s) :=
  Finset.univ.filter (λ M' ↦ M ≤c M'.M)

namespace terminating_children

variable {M: Machine l s}

lemma zero_transitions (hM: M.n_halting_trans = 0): terminating_children M = ∅ :=
by {
  apply Finset.eq_empty_of_forall_not_mem
  intro M' hM'
  simp [terminating_children] at hM'
  have hMnohalts := Machine.eq_zero_nonhalts hM
  simp [init] at hMnohalts
  apply hM'.halt_of_halt_parent hMnohalts
  use M'.n
  exact M'.terminates
}

lemma one_transition (hMt: M.halts_in n default) (hM: M.n_halting_trans = 1): terminating_children M = {⟨M, n, hMt⟩} :=
by {
  simp [terminating_children]
  ext M'
  simp
  constructor
  swap
  · intro h
    cases h
    simp
  intro hM'
  obtain ⟨C, hCl, hCr⟩ := hMt

  obtain ⟨M', n', t'⟩ := M'
  suffices M' = M by {
    cases this
    simp
    apply Machine.halts_in.deterministic t'
    use C
  }

  simp at hM'
  by_contra neq
  push_neg at neq

  have hsub := is_child.ne_halt_trans_ssub hM' neq.symm

  have le1 := calc M'.n_halting_trans
    _ < M.n_halting_trans := by {
      simp [n_halting_trans]
      exact Finset.card_lt_card hsub
    }
    _ = 1 := hM
  simp at le1

  have M'ns := Machine.eq_zero_nonhalts le1

  apply M'ns
  use n'
}

/-
If two TMs have different next statements, their terminating_children are disjoint.
-/
lemma disjoint_of_different_transition
  (hMM': M lab sym ≠ M' lab sym)
  (hM: M lab sym ≠ .halt)
  (hM': M' lab sym ≠ .halt): Disjoint (terminating_children M) (terminating_children M') :=
by {
  rw [Finset.disjoint_iff_inter_eq_empty, Finset.eq_empty_iff_forall_not_mem]
  intro M₀ hM₀
  simp [terminating_children] at hM₀
  obtain ⟨hM₀, hM₀'⟩ := hM₀
  specialize hM₀ lab sym
  specialize hM₀' lab sym
  simp [hM] at hM₀
  simp [hM'] at hM₀'
  apply hMM'
  rw [hM₀, hM₀']
}
