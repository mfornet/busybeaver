import Mathlib.Computability.TuringMachine
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Sort
import Busybeaver.TuringExt

abbrev Label (l: ℕ) := Fin (l + 1)
instance: Fintype (Label l) := inferInstance
instance: LE (Label l) := inferInstance
instance: Repr (Label l) := inferInstance
instance: Inhabited (Label l) := inferInstance

abbrev Symbol (s: ℕ) := Fin (s + 1)
instance: Fintype (Symbol s) := inferInstance
instance: LE (Symbol s) := inferInstance
instance: Repr (Symbol s) := inferInstance
instance: Inhabited (Symbol s) := inferInstance

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

namespace TM

section Defs
inductive Stmt (l s: ℕ)
| halt
| next: Symbol s → Turing.Dir → Label l → Stmt l s
deriving DecidableEq

instance: Inhabited $ Stmt l s := ⟨.halt⟩

-- Machines are arrays of code (label-major)
structure Machine (l s: ℕ) where
  vals: Array <| Stmt l s
  wf: vals.size = (l + 1) * (s + 1) -- := Label l → Symbol s → Stmt l s

def Machine.get_index (M: Machine l s) (lab: Label l) (sym: Symbol s): Fin M.vals.size :=
  ⟨lab.val * (s + 1) + sym.val, by {
    obtain ⟨vals, vwf⟩ := M
    obtain ⟨lab, hlab⟩ := lab
    obtain ⟨sym, hsym⟩ := sym
    simp [vwf]
    calc lab * (s + 1) + sym
      _ ≤ l * (s + 1) + sym := by {
        simp
        refine Nat.mul_le_mul ?_ (Nat.le_refl _)
        exact Nat.le_of_lt_succ hlab
      }
      _ < l * (s + 1) + (s + 1) := by {
        simp
        exact hsym
      }
      _ = (l + 1) * (s + 1) := (Nat.succ_mul l (s + 1)).symm
  }⟩

@[simp]
lemma Machine.get_index.size_only {M M': Machine l s} {lab: Label l} {sym: Symbol s}:
  (M.get_index lab sym).val = (M'.get_index lab sym).val := by rfl

@[simp]
lemma Machine.get_index.embed {M: Machine l s} {lab lab': Label l} {sym sym': Symbol s}:
  (M.get_index lab sym = M.get_index lab' sym') ↔ (lab = lab' ∧ sym = sym') :=
by {
  constructor
  swap
  · intro ⟨heql, heqs⟩
    cases heql
    cases heqs
    rfl
  intro heq
  simp [Machine.get_index] at heq
  obtain ⟨sym, hsym⟩ := sym
  obtain ⟨sym', hsym'⟩ := sym'
  obtain ⟨lab, hlab⟩ := lab
  obtain ⟨lab', hlab'⟩ := lab'
  simp_all
  suffices sym = sym' by {
    cases this
    simp_all
    refine Nat.eq_of_mul_eq_mul_right ?h heq
    exact Nat.zero_lt_succ s
  }
  calc sym
    _ = (lab * (s + 1) + sym) % (s + 1) := (Nat.mul_add_mod_of_lt hsym).symm
    _ = (lab' * (s + 1) + sym') % (s + 1) := by rw [heq]
    _ = sym' := Nat.mul_add_mod_of_lt hsym'
}

@[simp]
lemma Machine.get_index.size_only_embed {M M': Machine l s} {lab lab': Label l} {sym sym': Symbol s}:
  ((M.get_index lab sym).val = (M'.get_index lab' sym').val) ↔ (lab = lab' ∧ sym = sym') :=
by {
  rw [
    Machine.get_index.size_only (M':=M) (M:=M') (lab:=lab') (sym:=sym'),
    ← Machine.get_index.embed (M:=M)
  ]
  exact Fin.val_inj
}

def Machine.get_lab_sym (M: Machine l s) (idx: Fin M.vals.size): Label l × Symbol s :=
  (⟨idx / (s + 1), by {
    obtain ⟨idx, hid⟩ := idx
    obtain ⟨C, hC⟩ := M
    simp at *
    simp at hid
    rw [hC] at hid
    refine (Nat.div_lt_iff_lt_mul ?_).mpr hid
    exact Nat.zero_lt_succ s
  }⟩, ⟨idx % (s + 1), by {
    obtain ⟨idx, hid⟩ := idx
    obtain ⟨C, hC⟩ := M
    simp at *
    simp at hid
    rw [hC] at hid
    apply Nat.mod_lt idx
    exact Nat.zero_lt_succ s
  }⟩)

@[simp]
lemma Machine.get_lab_sym.size_only {M M': Machine l s} {idx: Fin M.vals.size}:
  M.get_lab_sym idx = M'.get_lab_sym ⟨idx.val, by {
    obtain ⟨idx, hi⟩ := idx
    simp
    rw [M'.wf]
    rw [M.wf] at hi
    trivial
  }⟩ := by rfl

@[simp]
lemma Machine.get_lab_sym_get_index {M: Machine l s} {lab: Label l} {sym: Symbol s}:
  (M.get_lab_sym <| M.get_index lab sym) = (lab, sym) :=
by {
  obtain ⟨lab, hlab⟩ := lab
  obtain ⟨sym, hsym⟩ := sym
  simp [Machine.get_lab_sym, Machine.get_index]
  constructor
  · rw [
      Nat.add_comm,
      Nat.add_mul_div_right sym lab (Nat.zero_lt_succ s)
    ]
    simp
    exact hsym
  · exact hsym
}

@[simp, grind .]
lemma Machine.get_index_get_lab_sym {M: Machine l s} {idx: Fin M.vals.size}:
  let (lab, sym) := M.get_lab_sym idx
  M.get_index lab sym = idx :=
by {
  obtain ⟨idx, hidx⟩ := idx
  simp [Machine.get_index, Machine.get_lab_sym]
  exact Nat.div_add_mod' idx (s + 1)
}

def Machine.get (M: Machine l s) (lab: Label l) (sym: Symbol s): Stmt l s :=
  M.vals[M.get_index lab sym]

def Machine.map (M: Machine l s) (f: Fin M.vals.size → Stmt l s → Stmt l s): Machine l s :=
  {
    vals := M.vals.mapFinIdx (fun i a hi ↦ f ⟨i, hi⟩ a),
    wf := by {
      rw [← M.wf]
      exact Array.size_mapFinIdx
    }
  }

@[simp]
lemma Machine.map_get {M: Machine l s} {f: Fin M.vals.size → Stmt l s → Stmt l s} {lab: Label l} {sym: Symbol s}:
  (M.map f).get lab sym = f (M.get_index lab sym) (M.get lab sym) := by simp [Machine.map, Machine.get, Machine.get_index]

def Machine.map' (M: Machine l s) (f: Label l → Symbol s → Stmt l s → Stmt l s): Machine l s :=
  M.map <| λ idx ↦
    let (lab, sym) := M.get_lab_sym ⟨idx, by grind⟩
    f lab sym

@[simp]
lemma Machine.map'_get {M: Machine l s} {f: Label l → Symbol s → Stmt l s → Stmt l s} {lab: Label l} {sym: Symbol s}:
  (M.map' f).get lab sym = f lab sym (M.get lab sym) := by simp [Machine.map']

def Machine.update_with (M: Machine l s) (lab: Label l) (sym: Symbol s) (S: Stmt l s) : Machine l s := {
  vals := M.vals.set (M.get_index lab sym) S,
  wf := by {
    simp
    exact M.wf
  }
}

@[simp]
lemma Machine.update_with.get {M: Machine l s} {lab lab': Label l} {sym sym': Symbol s} {S: Stmt l s}:
  (M.update_with lab sym S).get lab' sym' = if lab = lab' ∧ sym = sym' then S else M.get lab' sym'
  :=
by {
  obtain ⟨vals, hV⟩ := M
  simp [Machine.update_with, Machine.get]
  simp [Array.set]
  rw [List.getElem_set]
  simp
  split
  · rfl
  simp_all only [not_and]
  rfl
}

@[simp]
lemma Machine.update_with.get_eq {M: Machine l s} {lab: Label l} {sym: Symbol s} {S: Stmt l s} :
  (M.update_with lab sym S).get lab sym = S := by simp [Machine.update_with, Machine.get, Machine.get_index]

structure Config (l s: ℕ) [Inhabited $ Symbol s] where
  state: Label l
  tape: Turing.Tape (Symbol s)

end Defs

instance: DecidableEq (Config l s) := by {
  unfold DecidableEq
  intro a b
  obtain ⟨sa, ta⟩ := a
  obtain ⟨sb, tb⟩ := b
  simp_all
  apply instDecidableAnd
}

variable {l s: ℕ }

section PrettyPrint
open Std.Format Lean

unsafe instance: Repr (Config l s) := ⟨λ cfg _ ↦
  let leftRepr := Quot.unquot cfg.tape.left |>.reverse.map repr
  let rightRepr := Quot.unquot cfg.tape.right |>.map repr
  Std.Format.joinSep leftRepr " " ++ s!" {cfg.state}>{cfg.tape.head} " ++ Std.Format.joinSep
  rightRepr " "⟩

instance: Repr (Stmt l s) where
  reprPrec := λ s _ ↦ match s with
    | .halt => "---"
    | .next s d l => repr s ++ repr d ++ toString (Char.ofNat (l + Char.toNat 'A'))

instance: Repr (Machine l s) := ⟨λ M _ ↦
  joinSep (Finset.univ (α:=Label l) |>.sort (· ≤ ·) |>.map (λ lab ↦
    join (Finset.univ (α:=Symbol s) |>.sort (· ≤ ·) |>.map (λ sym ↦ repr $ M.get lab sym))
  )) "_"⟩

end PrettyPrint

instance Machine.inhabited: Inhabited $ Machine l s := ⟨{
  vals := Array.replicate ((l + 1) * (s + 1)) .halt,
  wf := Array.size_replicate
}⟩

@[simp]
lemma Machine.default_all_halt {l s: ℕ} {lab : Label l} {sym : Symbol s}:
  (default: Machine l s).get lab sym = .halt := by simp [default, Machine.get]

instance Stmt.fintype: Fintype $ Stmt l s := by {
  suffices equiv: Option (Symbol s × Turing.Dir × Label l) ≃ Stmt l s by {
    have hOfin : Fintype $ Option (Symbol s × Turing.Dir × Label l) := by {
      suffices Fintype $ (Symbol s × Turing.Dir × Label l) from fintypeOfOption
      exact instFintypeProd (Symbol s) (Turing.Dir × Label l)
    }
    apply Fintype.ofEquiv (Option (Symbol s × Turing.Dir × Label l)) equiv
  }
  exact {
    toFun := λ o ↦ match o with
    | .none => .halt
    | .some (s, d, l) => .next s d l,
    invFun := λ s ↦ match s with
    | .halt => .none
    | .next s d l => .some (s, d, l),
    left_inv := by {
      unfold Function.LeftInverse
      intro v
      cases v <;> simp
    }
    right_inv := by {
      simp [Function.LeftInverse, Function.RightInverse]
      intro v
      cases v <;> simp
    }
  }
}

instance Machine.finite: Fintype $ Machine l s := by {
  classical
  let n := (l + 1) * (s + 1)
  let e : Machine l s ≃ (Fin n → Stmt l s) := {
    toFun := fun M i => M.vals[Fin.cast (by simpa [n] using M.wf.symm) i]
    invFun := fun f => {
      vals := Array.ofFn f
      wf := by simp [n]
    }
    left_inv := by
      intro M
      cases M with
      | mk vals wf =>
        simp [n]
        apply Array.ext
        · simpa [n] using wf.symm
        · intro i hi1 hi2
          simp
    right_inv := by
      intro f
      funext i
      simp [n]
  }
  exact Fintype.ofEquiv (Fin n → Stmt l s) e.symm
}

instance Machine.decEq: DecidableEq (Machine l s) := by {
  intro ⟨Ac, Ah⟩ ⟨Bc, Bh⟩
  simp
  infer_instance
}

@[ext]
lemma Machine.ext {M M': Machine l s}: (∀ lab sym, M.get lab sym = M'.get lab sym) → M = M' := by {
  obtain ⟨C, hC⟩ := M
  obtain ⟨C', hC'⟩ := M'
  simp [Machine.get]
  intro hCC'
  ext i hi hi'
  · rw [hC, hC']
  let Mi : Machine l s := ⟨C, hC⟩
  let Mi' : Machine l s := ⟨C', hC'⟩
  let idx : Fin C.size := ⟨i, hi⟩
  let ls := Mi.get_lab_sym idx
  have hls : Mi'.get_lab_sym ⟨i, hi'⟩ = ls := by
    simpa [Mi, Mi', idx, ls] using (Machine.get_lab_sym.size_only (M:=Mi) (M':=Mi') (idx:=idx))
  have hEq := hCC' ls.1 ls.2
  have hidx : Mi.get_index ls.1 ls.2 = idx := by
    simpa [ls] using (Machine.get_index_get_lab_sym (M:=Mi) (idx:=idx))
  have hidx' : Mi'.get_index ls.1 ls.2 = ⟨i, hi'⟩ := by
    have := (Machine.get_index_get_lab_sym (M:=Mi') (idx:=⟨i, hi'⟩))
    simpa [hls, ls] using this
  simpa [Machine.get, Mi, Mi', idx, hidx, hidx'] using hEq
}

instance Config.inhabited: Inhabited $ Config l s := ⟨⟨default, default⟩⟩

def Machine.step (M: Machine l s) (orig: Config l s): Option (Config l s) := match M.get orig.state orig.tape.head with
| .halt => none
| .next sym dir state => some { state, tape := orig.tape.write sym |>.move dir}

def Machine.eval (M: Machine l s) (bound: ℕ) (orig: Config l s): Option (Config l s) := match bound with
| 0 => orig
| n + 1 => M.step orig >>= M.eval n

def Machine.LastState (M: Machine l s) (σ: Config l s): Bool := M.step σ |>.isNone

def init: Config l s := default

end TM
