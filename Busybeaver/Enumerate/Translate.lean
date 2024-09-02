/-
A translation is a swap of symbols on the tape.

We prove here that translated machine are equivalent to their original (through transformations)
-/
import Busybeaver.Basic
import Busybeaver.Enumerate.Basic
import Busybeaver.Enumerate.Perm

open TM.Machine

namespace Turing.Tape
/-
We begin by defining translations on tapes
-/

def translator (S S': Symbol s) (hS: default ≠ S) (hS': default ≠ S'): Turing.PointedMap (Symbol s) (Symbol s) := {
  f := swap S S',
  map_pt' := swap.ne hS hS'
}

def translate (T: Turing.Tape (Symbol s)) (S S': Symbol s) (hS: default ≠ S) (hS': default ≠ S'): Turing.Tape (Symbol s) :=
  T.map (translator S S' hS hS')


lemma ext [Inhabited α] {T₁ T₂: Turing.Tape α} (h: ∀(i: ℤ), T₁.nth i = T₂.nth i): T₁ = T₂ :=
by {
  obtain ⟨Th₁, Tl₁, Tr₁⟩ := T₁
  obtain ⟨Th₂, Tl₂, Tr₂⟩ := T₂
  simp
  constructor
  · have h0 := h 0
    simp at h0
    exact h0
  constructor
  · apply Turing.ListBlank.ext
    intro i
    have hleft := h $ Int.negSucc i
    simp [nth] at hleft
    exact hleft
  · apply Turing.ListBlank.ext
    intro i
    have hright := h $ Int.ofNat (i + 1)
    simp [nth] at hright
    exact hright
}

@[simp]
lemma map_nth {Γ Γ': Type*} [Inhabited Γ] [Inhabited Γ'] {T: Turing.Tape Γ} (f: PointedMap Γ Γ'): (T.map f).nth i = f.f (T.nth i) :=
by {
  obtain ⟨Th, Tl, Tr⟩ := T
  simp [nth]
  split
  · rfl
  · conv =>
     pattern (map f _).right
     simp [map]
    exact ListBlank.nth_map f Tr _
  · conv =>
      pattern (map f _).left
      simp [map]
    exact ListBlank.nth_map f Tl _
}

@[simp]
lemma default_nth {Γ: Type*} [Inhabited Γ]: nth default i = default (α:=Γ) :=
by {
  simp [nth]
  split <;> simp [default, ListBlank.nth]
}

@[simp]
lemma map_default {Γ Γ': Type*} [Inhabited Γ] [Inhabited Γ'] {f: PointedMap Γ Γ'}: Turing.Tape.map f default = default :=
by {
  apply ext
  intro i
  simp
}

end Turing.Tape

namespace TM.Machine

def translated (M: Machine l s) (S S': Symbol s): Machine l s :=
  λ lab sym ↦ match M lab (swap S S' sym) with
  | .halt => .halt
  | .next sym' dir lab' => .next (swap S S' sym') dir lab'

@[simp]
lemma translated.involutive {M: Machine l s}: (M.translated S S').translated S S' = M :=
by {
  apply funext
  intro lab
  apply funext
  intro symo
  unfold translated
  split <;> {
    rename_i heq
    split at heq <;> {
      cases heq
      try simp_all
    }
  }
}

variable {S S': Symbol s} (hS: default ≠ S) (hS': default ≠ S')

instance translated.transformation: Transformation (l:=l) (s:=s) (λ C ↦ ⟨C.state, Turing.Tape.translate C.tape S S' hS hS'⟩) (λ M ↦ Machine.translated M S S') where
  fCinv := by {
    intro ⟨Cs, Ct⟩
    simp
    apply Turing.Tape.ext
    intro i
    simp [Turing.Tape.translate, Turing.Tape.translator]
  }

  fMinv := by {
    intro M
    beta_reduce
    simp
  }

  simulate := by {
    intro M A B hAB
    have ⟨sym, dir, hAnxt, hBtape⟩ := Machine.step.some_rev hAB
    apply Machine.step.some' (sym:=swap S S' A.tape.head) (sym':=swap S S' sym) (dir:=dir)
    · simp [translated]
      split <;> simp_all
    · rfl
    · apply Turing.Tape.ext
      intro i
      rw [hBtape]
      rw [Turing.Tape.translate, Turing.Tape.map_move, Turing.Tape.map_write]
      congr
  }

lemma translated.equi_halts: (M, C) =H (M.translated S S', ⟨C.state, C.tape.translate S S' hS hS'⟩) :=
  translated.transformation hS hS' |>.equi_halts

lemma translated.equi_halts' {M: Machine l s} (hS: default ≠ S) (hS': default ≠ S'): (M, default) =H (M.translated S S', default) := by {
  suffices (Turing.Tape.translate default S S' hS hS') = default by {
    have hMe := translated.equi_halts (M:=M) (C:=default) hS hS'
    conv at hMe =>
      pattern Config.tape (default (α:=Config l s))
      unfold default
      unfold Config.inhabited
      unfold Config.tape
      simp
    rw [this] at hMe
    exact hMe
  }
  simp [Turing.Tape.translate]
}
