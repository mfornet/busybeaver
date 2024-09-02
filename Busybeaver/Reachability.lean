import Busybeaver.Basic

namespace TM

variable {M: Machine l s}

notation (priority:=high) s₁ "-[" M "]->" s₂ => Machine.step M s₁ = @Option.some (Config _ _) s₂

namespace Machine.step

lemma deterministic (hB: A -[M]-> B) (hC: A -[M]-> C): B = C := by {
  simp [Machine.step] at *
  split at hB
  · rename_i heq
    simp [heq] at hC
  · rename_i heq
    simp [heq] at hC
    simp at hB
    rw [← hB, ← hC]
}

@[simp]
lemma some (h: M q T.head = .next sym' dir q'): M.step ⟨q, T⟩ = some ⟨q', T.write sym' |>.move dir⟩ :=
by {
  simp [Machine.step]
  split
  · rename_i heq
    rw [h] at heq
    cases heq
  · rename_i heq
    rw [h] at heq
    cases heq
    rfl
}

@[simp]
lemma some' (h: M q sym = .next sym' dir q') (hsym: sym = T.head) (hT: T' = (T.write sym' |>.move dir)): M.step ⟨q, T⟩ = .some ⟨q', T'⟩ :=
by {
  rw [hsym] at h
  rw [hT]
  exact some h
}

@[simp]
lemma some_rev (h: M.step B = .some C): ∃ sym dir, M B.state B.tape.head = .next sym dir C.state ∧ C.tape = (B.tape.write sym |>.move dir) :=
by {
  simp [step] at h
  split at h
  · cases h
  cases h
  rename_i sym dir _ _
  exists sym
  exists dir
}

@[simp]
lemma none: (M.step c = .none) ↔ M c.state c.tape.head = .halt :=
 by {
  constructor
  · intro h
    simp [Machine.step] at h
    split at h
    · trivial
    · contradiction
  · intro h
    simp [Machine.step]
    split
    · rfl
    · simp_all
 }

end Machine.step

inductive Machine.Multistep (M: Machine l s): ℕ → Config l s → Config l s → Prop
| refl {C} : M.Multistep 0 C C
| succ {A B C n} : (A -[M]-> B) → M.Multistep n B C → M.Multistep (.succ n) A C

notation (priority:=high) s₁ "-["M"]{"k"}->" s₂ => Machine.Multistep M k s₁ s₂

inductive Machine.Progress (M: Machine l s) : Config l s → Config l s → Prop
| single {C C'} : (C -[M]-> C') → M.Progress C C'
| step {A B C} : (A -[M]-> B) → M.Progress B C → M.Progress A C

notation A " -[" M "]->+ " B => Machine.Progress M A B

inductive Machine.EvStep (M: Machine l s): Config l s → Config l s → Prop
| refl {C} : M.EvStep C C
| step {A B C} : (A -[M]-> B) → M.EvStep B C → M.EvStep A C

notation A " -["M"]->* " B => Machine.EvStep M A B

namespace Machine.Multistep

def trans (hA: A -[M]{n}-> B) (hB: B -[M]{n'}-> C): A -[M]{n + n'}-> C := by induction hA with
| refl => {
  simp
  exact hB
}
| @succ A I B n hAI _ IH => {
  simp
  conv =>
   pattern n + 1 + n'
   rw [add_assoc, add_comm 1, ← add_assoc]
  apply succ hAI
  exact IH hB
}

def deterministic (hB: A -[M]{n}-> B) (hC: A -[M]{n}-> C): B = C := by {
  induction hB generalizing C with
  | refl => {
    cases hC
    rfl
  }
  | @succ A I B n' hIB _ IH => {
    cases hC
    rename_i I' hAI' hIC'
    rw [hAI'] at hIB
    cases hIB
    exact IH hIC'
  }
}

instance: Trans (M.Multistep n) (M.Multistep n') (M.Multistep (n + n')) where
  trans := by {
    intro A B C hA hB
    exact trans hA hB
  }

lemma single (h: A -[M]-> B): A -[M]{1}-> B := by {
  apply succ h
  exact refl
}

lemma single' (h: A -[M]{1}-> B): A -[M]-> B :=
  by {
    cases h with
    | @succ _ C _ _ hAC hCB => {
      cases hCB
      exact hAC
    }
  }

lemma tail (h: A -[M]{n}-> B) (h': B -[M]-> C): A -[M]{n + 1}-> C :=
  by calc A
    _ -[M]{n}-> B := h
    _ -[M]{1}-> C := single h'

lemma split (h: A -[M]{n + k}-> B): ∃C, (A -[M]{n}-> C) ∧ (C -[M]{k}-> B) :=
  by induction n generalizing B k with
  | zero => {
    simp at *
    exists A
    constructor
    · exact refl
    · exact h
  }
  | succ n' IH => {
    rw [add_assoc, add_comm 1] at h
    obtain ⟨C, hAC, hCB⟩ := IH h

    cases hCB
    rename_i C' hCC' hC'B

    exists C'
    constructor
    · exact tail hAC hCC'
    · exact hC'B
  }

lemma split' (h: A -[M]{n}-> B) (hn: n = k₁ + k₂): ∃C, (A -[M]{k₁}-> C) ∧ (C -[M]{k₂}-> B) :=
  by {
    rw [hn] at h
    exact split h
  }

lemma split_le (hB: A -[M]{n}-> B) (hC: A -[M]{k}-> C) (hk: k ≤ n): C -[M]{n - k}-> B :=
  by induction k generalizing A n with
  | zero => {
    simp_all
    cases hC
    exact hB
  }
  | succ k IH => {
    cases hC
    rename_i C' hAC' hC'C
    specialize @IH (n - 1) C' (by {
      cases hB
      · simp at hk
      rename_i Cb n hACb hCbB
      rw [hAC'] at hACb
      cases hACb
      simp
      exact hCbB
    }) hC'C
    conv =>
      pattern n - (k + 1)
      rw [add_comm, Nat.sub_add_eq]
    apply IH
    exact Nat.le_sub_one_of_lt hk
  }

lemma split_add (hB: A -[M]{n}-> B) (hC: A -[M]{n + k}-> C): B -[M]{k}-> C :=
  by {
    obtain ⟨C', hAC', hC'B⟩ := hC.split
    rw [← deterministic hB hAC'] at hC'B
    exact hC'B
  }

lemma to_evstep (h: A -[M]{n}-> B): A -[M]->* B :=
  by induction h with
  | refl => exact .refl
  | succ hAB _ IH => {
    exact .step hAB IH
  }

lemma get_prefix (h: A -[M]{n}-> B) (hk: k ≤ n): ∃C, A -[M]{k}-> C :=
by induction h generalizing k with
| @refl C => {
  exists C
  simp_all
  exact .refl
}
| @succ A B _ n hAB _ IH => {
  rcases Nat.eq_zero_or_eq_sub_one_add_one (n:=k) with hk' | hk'
  · simp_all
    exists A
    exact .refl

  rw [add_comm] at hk'
  simp [*, -hk'] at hk
  apply Nat.sub_le_of_le_add at hk
  obtain ⟨C, hC⟩ := IH hk
  exists C
  rw [hk']
  calc A
    _ -[M]{1}-> B := Multistep.single hAB
    _ -[M]{k - 1}-> C := hC
}

end Machine.Multistep

namespace Machine.Progress

lemma trans (hA: A -[M]->+ B) (hB: B -[M]->+ C): A -[M]->+ C := by
  induction hA with
  | single h => exact step h hB
  | @step A I B hAB _ IH => exact step hAB (IH hB)

instance: IsTrans (Config l s) M.Progress where
  trans := by {
    intro A B C hA hB
    exact trans hA hB
  }

lemma to_multistep (h: A -[M]->+ B): ∃ n, A -[M]{n+1}-> B :=
  by induction h with
  | single h => {
    exists 0
    simp
    exact .single h
  }
  | @step A I B hAB _ IH => {
    obtain ⟨n, hn⟩ := IH
    exists n + 1
    exact Multistep.succ hAB hn
  }

lemma to_evstep (h: A -[M]->+ B): A -[M]->* B :=
  by induction h with
  | single h => exact EvStep.step h .refl
  | @step A I B hAI _ IH => exact EvStep.step hAI IH


lemma from_multistep (h: A -[M]{n + 1}-> B): A -[M]->+ B :=
  by induction n generalizing A with
  | zero => {
    cases h
    rename_i I hAI hIB
    cases hIB
    exact .single hAI
  }
  | succ n IH => {
    cases h
    rename_i I hAI hIB
    specialize IH hIB
    calc A
      _ -[M]->+ I := .single hAI
      _ -[M]->+ B := IH
  }

end Machine.Progress

namespace Machine.EvStep

lemma trans (hA: A -[M]->* B) (hB: B -[M]->* C): A -[M]->* C :=
  by induction hA with
  | refl => exact hB
  | @step A I B hAI _ IH => exact step hAI (IH hB)

instance: IsTrans (Config l s) M.EvStep where
  trans := by {
    intro A B C hA hB
    exact trans hA hB
  }

lemma to_multistep (h: A -[M]->* B): ∃n, A -[M]{n}-> B :=
  by induction h with
  | refl => {
    exists 0
    exact .refl
  }
  | @step A I B hAI _ IH => {
    obtain ⟨n, hn⟩ := IH
    exists 1 + n
    calc A
      _ -[M]{1}-> I := .single hAI
      _ -[M]{n}-> B := hn
  }

end Machine.EvStep

instance: Trans M.Progress M.EvStep M.Progress where
  trans := by {
    intro A B C hA hB
    induction hB with
    | refl => exact hA
    | @step B I _ hBI _ IH => {
      apply IH
      calc A
        _ -[M]->+ B := hA
        _ -[M]->+ I := .single hBI
    }
  }

instance: Trans M.EvStep M.Progress M.Progress where
  trans := by {
    intro A B C hA hB
    induction hA with
    | refl => exact hB
    | @step A I B hAI _ IH => {
      specialize IH hB
      calc A
        _ -[M]->+ I := .single hAI
        _ -[M]->+ C := IH
    }
  }

def Machine.halts_in (M: Machine l s) (n: ℕ) (A: Config l s): Prop := ∃ C, M.LastState C ∧ A -[M]{n}-> C

def Machine.halts (M: Machine l s) (A: Config l s): Prop := ∃ n, M.halts_in n A

namespace Machine.halts_in

lemma no_multistep (hM: M.LastState A): ¬(A -[M]{n + 1}-> C) := by {
  intro hAC
  cases hAC
  rename_i B hAB hBC
  simp [Machine.LastState, -step.none] at hM
  rw [hM] at hAB
  cases hAB
}

lemma no_progress (hM: M.LastState A): ¬(A -[M]->+ B) := by {
  intro hAC
  obtain ⟨n, hn⟩ := hAC.to_multistep
  exact absurd hn (no_multistep hM)
}

lemma evstep_same (hM: M.LastState A) (h: A -[M]->* B): A = B :=
  by {
    have ⟨n, h⟩ := h.to_multistep
    induction n with
    | zero => {
      cases h
      rfl
    }
    | succ n _ => {
      exact absurd h (no_multistep hM)
    }
  }

lemma orders (h: M.halts_in n A) (hB: B -[M]{k}-> A): M.halts_in (k + n) B := by {
  obtain ⟨C, cLast, cReach⟩ := h
  exists C
  constructor
  · exact cLast
  apply Multistep.trans hB cReach
}

lemma from_last (h: M.LastState C): M.halts_in 0 C := by {
  exists C
  constructor
  · exact h
  · exact .refl
}

lemma exceeds (hM: M.halts_in k A) (hn: k < n): ¬(A -[M]{n}-> B) := by {
  intro hAB
  obtain ⟨C, hCL, hAC⟩ := hM
  have hCB := Multistep.split_le hAB hAC hn.le
  rcases n with _ | n
  · exact Nat.not_succ_le_zero k hn
  conv at hCB =>
    pattern n + 1 - k
    rw [Nat.sub_add_comm (Nat.le_of_lt_succ hn)]
  exact no_multistep hCL hCB
}

lemma preceeds (hM: M.halts_in k A) (hAB: A -[M]{n}-> B) (hk: n ≤ k): M.halts_in (k - n) B := by {
  obtain ⟨C, hCl, hAC⟩ := hM
  exists C
  constructor
  · exact hCl
  exact Multistep.split_le hAC hAB hk
}

lemma within (hM: M.halts_in k A) (hB: A -[M]{n}-> B) : n ≤ k := by {
  by_contra hk
  simp at hk
  exact exceeds hM hk hB
}

lemma deterministic (hMk: M.halts_in k A) (hMn: M.halts_in n A): k = n :=
  by {
    apply Nat.le_antisymm
    · obtain ⟨_, _, hk⟩ := hMk
      exact within hMn hk
    · obtain ⟨_, _, hn⟩ := hMn
      exact within hMk hn
  }

lemma split (hM: M.halts_in n A) (hn: k ≤ n): ∃B, A -[M]{k}-> B :=
by {
  obtain ⟨C, _, hC⟩ := hM
  exact hC.get_prefix hn
}

end Machine.halts_in

namespace Machine.halts

lemma mono (h: A -[M]{n}-> B) (hM: M.halts B): M.halts A := by {
  obtain ⟨nb, hnb⟩ := hM
  exists n + nb
  exact halts_in.orders hnb h
}

lemma tail (h: A -[M]{n}-> B) (hM: M.halts A): M.halts B := by {
  obtain ⟨k, hk⟩ := hM
  have hkn := halts_in.within hk h
  have hB := halts_in.preceeds hk h hkn
  exists k - n
}

lemma skip (h: A -[M]{n}-> B) (hM: ¬(M.halts B)): ¬(M.halts A) := by {
  intro ⟨nA, hnA⟩
  have hn := halts_in.within hnA h
  obtain ⟨Ca, hCaL, hACa⟩ := hnA
  have hBCa := Multistep.split_le hACa h hn
  apply hM
  exists nA - n
  exists Ca
}

lemma skip_evstep (h: A -[M]->* B) (hM: ¬(M.halts B)): ¬(M.halts A) := by {
  have ⟨_, hAB⟩ := h.to_multistep
  exact skip hAB hM
}

lemma skip_next (h: A -[M]-> B) (hM: ¬(M.halts B)): ¬(M.halts A) :=
by {
  refine skip (n:=1) ?_ hM
  exact Multistep.single h
}

end Machine.halts

/--
Monad for computations that prove (non-)termination of machine M
-/
inductive HaltM {l s: ℕ} (M: TM.Machine l s) (α: Type u)
| unknown: α → HaltM M α
| halts_prf n C : M.LastState C ∧ (default -[M]{n}-> C) → HaltM M α
| loops_prf : ¬(M.halts init) → HaltM M α
deriving Repr

namespace HaltM
variable {l s: ℕ}

instance (M: TM.Machine l s): Monad (HaltM M) where
  pure := .unknown
  bind := λ m f ↦ match m with
    | .unknown v => f v
    | .halts_prf n C p => .halts_prf n C p
    | .loops_prf p => .loops_prf p

def decided: HaltM M α → Bool
| .unknown _ => False
| _ => True

end HaltM

def Machine.stepH
  (M: TM.Machine l s) (σ: {s // init -[M]{k}-> s}): HaltM M {s' // init -[M]{k + 1}-> s'} :=
  match hi: M.step σ.val with
  | .none => .halts_prf k σ.val (by {
    constructor
    · simp_all [Machine.LastState]
    · exact σ.prop
  })
  | .some nxt => .unknown ⟨nxt, by {
    obtain ⟨s, hs⟩ := σ
    simp_all
    exact Machine.Multistep.tail hs hi
  }⟩

