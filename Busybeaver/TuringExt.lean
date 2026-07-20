import Mathlib.Computability.TuringMachine.StackTuringMachine

instance: Fintype Turing.Dir := by {
  refine @Fintype.ofEquiv Turing.Dir Bool _ ?_
  exact {
    toFun := λ b ↦ if b then .left else .right
    invFun := λ t ↦ match t with | .left => true | .right => false
    left_inv := by intro b; cases b <;> rfl
    right_inv := by intro t; cases t <;> rfl
  }
}

instance Turing.BlankExtends.instDecidableRel {Γ} [Inhabited Γ] [DecidableEq Γ] : DecidableRel (@Turing.BlankExtends Γ _)
  | [], ys => decidable_of_iff (∀ y ∈ ys, y = default) (by
      simp only [Turing.BlankExtends, List.nil_append]
      exact ⟨fun hy => ⟨ys.length, List.eq_replicate_of_mem hy⟩,
             fun ⟨n, hn⟩ y hy => List.eq_of_mem_replicate (hn ▸ hy)⟩)
  | x :: xs, [] => .isFalse (by simp [Turing.BlankExtends])
  | x :: xs, y :: ys =>
    letI := instDecidableRel xs ys
    decidable_of_iff (x = y ∧ Turing.BlankExtends xs ys) (by {
      simp [Turing.BlankExtends]
      intro n _
      exact ⟨(·.symm), (·.symm)⟩
    })

instance Turing.BlankRel.instDecidableRel {Γ} [Inhabited Γ] [DecidableEq Γ]: DecidableRel (@Turing.BlankRel Γ _) :=
  fun a b => by unfold Turing.BlankRel; infer_instance


namespace Turing.ListBlank

variable {Γ} [Inhabited Γ]

instance instHAppend: HAppend (List Γ) (ListBlank Γ) (ListBlank Γ) where
  hAppend := append

lemma append_assoc' {L₁ L₂: List Γ} {L: ListBlank Γ}: L₁ ++ L₂ ++ L = L₁ ++ (L₂ ++ L) :=
  Turing.ListBlank.append_assoc L₁ L₂ L

instance instDecidableEq [DecidableEq Γ]: DecidableEq (Turing.ListBlank Γ) := by
  refine @Quotient.decidableEq _ (Turing.BlankRel.setoid Γ) ?_
  intro a b
  change Decidable (Turing.BlankRel a b)
  infer_instance

lemma cons_nth_zero {T: Turing.ListBlank Γ}: (cons A T).nth 0 = A :=
by induction T using Turing.ListBlank.induction_on; simp

lemma cons_nth_succ {T: Turing.ListBlank Γ}: (cons A T).nth (i + 1) = T.nth i :=
by induction T using Turing.ListBlank.induction_on; simp

@[simp]
lemma cons_injective {T T': Turing.ListBlank Γ} {g g': Γ}: cons g T = cons g' T' ↔ g = g' ∧ T = T' :=
  ⟨fun h => ⟨by rw [← head_cons g T, ← head_cons g' T', h],
            by rw [← tail_cons g T, ← tail_cons g' T', h]⟩,
   fun ⟨hg, hT⟩ => by rw [hg, hT]⟩

@[simp]
lemma cons_default_empty: cons default ∅ = (∅: Turing.ListBlank Γ) :=
by ext i; cases i <;> (simp; rfl)

@[simp]
lemma append_mk_nth {L: List Γ} {T: Turing.ListBlank Γ}:
  (L ++ T).nth i = if _ : i < L.length then L[i] else T.nth (i - L.length) :=
by
  induction T using Turing.ListBlank.induction_on with
  | h T =>
    by_cases h' : i < L.length
    · rw [show (L ++ Turing.ListBlank.mk T) = Turing.ListBlank.append L (Turing.ListBlank.mk T) from rfl,
        Turing.ListBlank.append_mk, Turing.ListBlank.nth_mk, List.getI_append _ _ _ h',
        List.getI_eq_getElem _ h']
      simp [h']
    · rw [show (L ++ Turing.ListBlank.mk T) = Turing.ListBlank.append L (Turing.ListBlank.mk T) from rfl,
        Turing.ListBlank.append_mk, Turing.ListBlank.nth_mk,
        List.getI_append_right _ _ _ (Nat.le_of_not_lt h')]
      simp [h']

@[simp]
lemma default_nth: (default: Turing.ListBlank Γ).nth i = default :=
  by rfl

@[simp]
lemma append_empty {T: Turing.ListBlank Γ}: ([]: List Γ) ++ T = T :=
  by rfl

@[simp]
lemma append_cons {T: Turing.ListBlank Γ} {L: List Γ} {g: Γ}: g :: L ++ T = Turing.ListBlank.cons g (L ++ T) :=
  by rfl

@[simp]
lemma append_nth {T: Turing.ListBlank Γ} {L: List Γ}: (L ++ T).nth n = if h: n < L.length then L[n]'h else T.nth (n - L.length) :=
  append_mk_nth

@[simp]
lemma liftOn_mk {L: List Γ}: Turing.ListBlank.liftOn (Turing.ListBlank.mk L) f prf = f L :=
  by rfl

@[simp]
lemma mk_eq_mk {L L': List Γ}: Turing.ListBlank.mk L = Turing.ListBlank.mk L' ↔ Turing.BlankRel L L' :=
  ⟨fun h => Quotient.exact' h, fun h => Quotient.sound' h⟩

/--
If two list blanks are different, then by [Classical.choice] they differ at some point.
-/
lemma ne_exists_different {Lb Lb': Turing.ListBlank Γ}: Lb ≠ Lb' ↔ ∃n, Lb.nth n ≠ Lb'.nth n := by
  rw [Ne, Turing.ListBlank.ext_iff, not_forall]

def meet_blank [DecidableEq Γ]: List Γ → List Γ → List Γ
| [], [] => []
| [], head :: tail | head :: tail, [] => if head = default then default :: meet_blank tail [] else []
| head :: tail, head' :: tail' => if head = head' then head :: meet_blank tail tail' else []
termination_by L L' => L.length + L'.length

lemma meet_blank.commutative [DecidableEq Γ] {L L': List Γ}: meet_blank L L' = meet_blank L' L :=
by induction L, L' using meet_blank.induct with simp_all [meet_blank]
| case7 head tail head' tail' hne => simp [Ne.symm hne]

@[simp]
lemma meet_blank.replicate_default_left [DecidableEq Γ]: meet_blank [] (List.replicate n default) = List.replicate n (default: Γ) :=
by induction n with
| zero => simp [meet_blank]
| succ n IH => simp [List.replicate_succ, meet_blank]; rw [commutative]; exact IH

@[simp]
lemma meet_blank.replicate_default_right [DecidableEq Γ]: meet_blank (List.replicate n default) [] = List.replicate n (default: Γ) :=
by rw [commutative]; exact replicate_default_left

private lemma meet_blank.blank_extends [DecidableEq Γ] {L L': List Γ} (h: BlankExtends L L'): meet_blank L L' = L' :=
by
  obtain ⟨n, rfl⟩ := h
  induction L <;> simp_all [meet_blank]

@[simp]
def take (Lb: Turing.ListBlank Γ): ℕ → List Γ
| 0 => []
| n + 1 => Lb.head :: Lb.tail.take n

@[simp]
lemma take.length {Lb: Turing.ListBlank Γ}: (Lb.take n).length = n :=
  by induction n generalizing Lb <;> simp_all

@[simp]
theorem take_nth {Lb: Turing.ListBlank Γ} {n i: ℕ} (h: i < n): (Lb.take n)[i]'(by simp [h]) = Lb.nth i :=
by induction i generalizing n Lb with
| zero => cases n with | zero => omega | succ n => simp
| succ i IH => cases n with | zero => omega | succ n => simpa using IH (Nat.lt_of_succ_lt_succ h)

@[simp]
def drop (Lb: Turing.ListBlank Γ): ℕ → ListBlank Γ
| 0 => Lb
| n + 1 => Lb.tail.drop n

@[simp]
lemma drop_nth {Lb: Turing.ListBlank Γ}: (Lb.drop n).nth n' = Lb.nth (n + n') :=
by induction n generalizing Lb with
| zero => simp
| succ n IH => simp only [drop]; rw [IH, ← Turing.ListBlank.nth_succ]; congr 1; omega

lemma append_take_drop {Lb: Turing.ListBlank Γ}: (Lb.take n) ++ (Lb.drop n) = Lb :=
by
  ext i
  simp
  split
  · rename_i h; simp [take_nth h]
  · rename_i heq; congr 1; omega

end Turing.ListBlank

instance Turing.Tape.instDecidableEq {Γ} [Inhabited Γ] [DecidableEq Γ]: DecidableEq (Turing.Tape Γ) :=
  -- NB: tactic-free so that `decide` can kernel-reduce this instance.
  fun a b =>
    decidable_of_iff (a.head = b.head ∧ a.left = b.left ∧ a.right = b.right)
      (by cases a; cases b; simp)

namespace Turing.Dir
instance: Repr Turing.Dir where
  reprPrec := λ d _ ↦ match d with
    | .left => "L"
    | .right => "R"

def other: Turing.Dir → Turing.Dir
| .left => .right
| .right => .left

lemma eq_left_or_eq_right {d: Turing.Dir}: d = .left ∨ d = .right :=
by cases d <;> trivial

@[simp]
lemma move.other [Inhabited α] {Γ: Turing.Tape α}: (Γ.move d).move d.other = Γ :=
by cases d <;> simp [Turing.Tape.move, Turing.Dir.other]

@[simp]
lemma other.symmetric {d: Turing.Dir}: d.other.other = d :=
by cases d <;> simp [other]

end Turing.Dir

namespace Turing.Tape

variable {Γ} [Inhabited Γ]

@[simp] lemma default_head : (default : Turing.Tape Γ).head = default := rfl

@[simp] lemma default_left : (default : Turing.Tape Γ).left = default := rfl

@[simp] lemma default_right : (default : Turing.Tape Γ).right = default := rfl

@[simp] lemma write_nth_zero (T : Turing.Tape Γ) (sym : Γ) :
    (T.write sym).nth (0 : ℤ) = sym := by
  simp [Turing.Tape.nth, Turing.Tape.write]

lemma write_nth_of_ne_zero (T : Turing.Tape Γ) (sym : Γ) {i : ℤ} (hi : i ≠ 0) :
    (T.write sym).nth i = T.nth i := by
  cases i using Int.casesOn with
  | ofNat n =>
      cases n with
      | zero =>
          cases (hi rfl)
      | succ _ =>
          simp [Turing.Tape.nth, Turing.Tape.write]
  | negSucc _ =>
      simp [Turing.Tape.nth, Turing.Tape.write]

end Turing.Tape
