import Busybeaver.TM.Table
import Busybeaver.TM.Table.Reachability
import Busybeaver.TuringExt

/-!
Generic "block crossing" reachability lemmas for table machines.

These are the reusable primitives for proving non-halting of counter-style
machines (the BB(5) sporadic holdouts): a Turing machine head sweeping across a
uniform block of symbols while staying in a fixed control state.

All configurations are expressed with `Turing.Tape.mk' L R`, where `L` is the
left `ListBlank` and `R` is the *inclusive* right `ListBlank` (head + right).
A single machine step in this representation is:

* right step writing `b` on reading `a`:
  `mk' L (a :: R) → mk' (b :: L) R`
* left step writing `b` on reading `a`:
  `mk' (l₀ :: L) (a :: R) → mk' L (l₀ :: b :: R)`
-/

namespace TM.Table

open Turing

@[simp] lemma ListBlank.head_empty {Γ} [Inhabited Γ] : (∅ : ListBlank Γ).head = default := rfl
@[simp] lemma ListBlank.tail_empty {Γ} [Inhabited Γ] : (∅ : ListBlank Γ).tail = ∅ := rfl

variable {l s : ℕ} {M : Machine l s}

/-- One rightward step in `mk'` form. -/
lemma step_right_mk' {q q' : Label l} {a b : Symbol s}
    (h : M.get q a = .next b .right q') (L R : ListBlank (Symbol s)) :
    (⟨q, Tape.mk' L (ListBlank.cons a R)⟩ : Config l s) -[M]->
      ⟨q', Tape.mk' (ListBlank.cons b L) R⟩ := by
  refine Machine.step.some' h ?_ ?_
  · simp
  · simp [Tape.write_mk', Tape.move_right_mk']

/-- One leftward step in `mk'` form. -/
lemma step_left_mk' {q q' : Label l} {a b l₀ : Symbol s}
    (h : M.get q a = .next b .left q') (L R : ListBlank (Symbol s)) :
    (⟨q, Tape.mk' (ListBlank.cons l₀ L) (ListBlank.cons a R)⟩ : Config l s) -[M]->
      ⟨q', Tape.mk' L (ListBlank.cons l₀ (ListBlank.cons b R))⟩ := by
  refine Machine.step.some' h ?_ ?_
  · simp
  · simp [Tape.write_mk', Tape.move_left_mk']

/-- One rightward step reading the blank cell at the right edge (`mk' L ∅`). -/
lemma step_right_blank {q q' : Label l} {b : Symbol s}
    (h : M.get q default = .next b .right q') (L : ListBlank (Symbol s)) :
    (⟨q, Tape.mk' L (∅ : ListBlank (Symbol s))⟩ : Config l s) -[M]->
      ⟨q', Tape.mk' (ListBlank.cons b L) ∅⟩ :=
  Machine.step.some' h rfl rfl

/-- One leftward step reading the blank cell at the right edge (`mk' (cons l₀ L) ∅`). -/
lemma step_left_blank {q q' : Label l} {b l₀ : Symbol s}
    (h : M.get q default = .next b .left q') (L : ListBlank (Symbol s)) :
    (⟨q, Tape.mk' (ListBlank.cons l₀ L) (∅ : ListBlank (Symbol s))⟩ : Config l s) -[M]->
      ⟨q', Tape.mk' L (ListBlank.cons l₀ (ListBlank.cons b ∅))⟩ := by
  refine Machine.step.some' h rfl ?_
  simp [Tape.write_mk', Tape.move_left_mk']

/-- One leftward step at the left edge (`mk' ∅ (cons a R)`): moving onto a fresh
blank cell, leaving the just-written `b` to the right. -/
lemma step_left_edge {q q' : Label l} {a b : Symbol s}
    (h : M.get q a = .next b .left q') (R : ListBlank (Symbol s)) :
    (⟨q, Tape.mk' (∅ : ListBlank (Symbol s)) (ListBlank.cons a R)⟩ : Config l s) -[M]->
      ⟨q', Tape.mk' ∅ (ListBlank.cons default (ListBlank.cons b R))⟩ := by
  refine Machine.step.some' h ?_ ?_
  · simp
  · simp [Tape.write_mk', Tape.move_left_mk']

/-- Pushing one symbol from a `replicate` block to the front of an appended `ListBlank`. -/
lemma replicate_succ_append {Γ} [Inhabited Γ] (a : Γ) (n : ℕ) (L : ListBlank Γ) :
    List.replicate (n + 1) a ++ L = List.replicate n a ++ ListBlank.cons a L := by
  rw [List.replicate_succ', ListBlank.append_assoc']
  congr 1

/-- A head reading symbol `a` in state `q`, with `M.get q a = .next b .right q`
(a rightward self-loop), sweeps across a block of `n` copies of `a` in `n`
steps, leaving a block of `n` copies of `b` behind it. -/
lemma right_run {q : Label l} {a b : Symbol s}
    (h : M.get q a = .next b .right q) :
    ∀ (n : ℕ) (L R : ListBlank (Symbol s)),
      (⟨q, Tape.mk' L (List.replicate n a ++ R)⟩ : Config l s) -[M]{n}->
        ⟨q, Tape.mk' (List.replicate n b ++ L) R⟩
  | 0, L, R => by simpa using Machine.Multistep.refl
  | n + 1, L, R => by
      have hL : (List.replicate (n + 1) a ++ R) = ListBlank.cons a (List.replicate n a ++ R) := by
        rw [List.replicate_succ]; rfl
      have hR : (List.replicate (n + 1) b ++ L) = List.replicate n b ++ ListBlank.cons b L :=
        replicate_succ_append b n L
      rw [hL, hR]
      exact Machine.Multistep.succ (step_right_mk' h L _) (right_run h n (ListBlank.cons b L) R)

/-- A head reading symbol `a` in state `q`, with `M.get q a = .next b .left q`
(a leftward self-loop), sweeps across a block of `n` copies of `a` to its left
in `n` steps, leaving a block of `n` copies of `b` to its right. -/
lemma left_run {q : Label l} {a b : Symbol s}
    (h : M.get q a = .next b .left q) :
    ∀ (n : ℕ) (L R : ListBlank (Symbol s)),
      (⟨q, Tape.mk' (List.replicate n a ++ L) (ListBlank.cons a R)⟩ : Config l s) -[M]{n}->
        ⟨q, Tape.mk' L (ListBlank.cons a (List.replicate n b ++ R))⟩
  | 0, L, R => by simpa using Machine.Multistep.refl
  | n + 1, L, R => by
      have hL : (List.replicate (n + 1) a ++ L) = ListBlank.cons a (List.replicate n a ++ L) := by
        rw [List.replicate_succ]; rfl
      have hR : (List.replicate (n + 1) b ++ R) = List.replicate n b ++ ListBlank.cons b R :=
        replicate_succ_append b n R
      rw [hL, hR]
      exact Machine.Multistep.succ (step_left_mk' h _ _) (left_run h n L (ListBlank.cons b R))

/-- Accumulator for the `zigzag` sweep: prepends `t` copies of the pair `[c, b]`. -/
def zigzagAcc (b c : Symbol s) : ℕ → ListBlank (Symbol s) → ListBlank (Symbol s)
  | 0, R => R
  | t + 1, R => ListBlank.cons c (ListBlank.cons b (zigzagAcc b c t R))

lemma zigzagAcc_cons (b c : Symbol s) (t : ℕ) (R : ListBlank (Symbol s)) :
    zigzagAcc b c t (ListBlank.cons c (ListBlank.cons b R)) =
      ListBlank.cons c (ListBlank.cons b (zigzagAcc b c t R)) := by
  induction t with
  | zero => rfl
  | succ t ih => simp only [zigzagAcc, ih]

/-- The `t` complete pairs of a two-state alternating leftward sweep. States
`q1` and `q2` both read `a` and move left; `q1` writes `b → q2`, `q2` writes
`c → q1`. Each pair consumes two `a`s from the left, prepending `c, b` to the
right. -/
lemma zigzag_pairs {q1 q2 : Label l} {a b c : Symbol s}
    (h1 : M.get q1 a = .next b .left q2)
    (h2 : M.get q2 a = .next c .left q1) :
    ∀ (t : ℕ) (L R : ListBlank (Symbol s)),
      (⟨q1, Tape.mk' (List.replicate (2 * t) a ++ L) (ListBlank.cons a R)⟩ : Config l s)
        -[M]{2 * t}->
      ⟨q1, Tape.mk' L (ListBlank.cons a (zigzagAcc b c t R))⟩
  | 0, L, R => by simpa using Machine.Multistep.refl
  | t + 1, L, R => by
      have hblk : List.replicate (2 * (t + 1)) a ++ L
          = ListBlank.cons a (ListBlank.cons a (List.replicate (2 * t) a ++ L)) := by
        simp only [Nat.mul_succ, List.replicate_succ, ListBlank.append_cons]
      rw [hblk]
      have e1 := step_left_mk' (l₀ := a) h1 (ListBlank.cons a (List.replicate (2 * t) a ++ L)) R
      have e2 := step_left_mk' (l₀ := a) h2 (List.replicate (2 * t) a ++ L) (ListBlank.cons b R)
      have ih := zigzag_pairs h1 h2 t L (ListBlank.cons c (ListBlank.cons b R))
      rw [zigzagAcc_cons] at ih
      have hcount : 2 * (t + 1) = 2 * t + 1 + 1 := by omega
      rw [hcount]
      exact Machine.Multistep.succ e1 (Machine.Multistep.succ e2 ih)

/-- A two-state alternating leftward sweep across an odd block `a^(2t+1)`,
bounded on the left by a separator `sep ≠ a`. The head starts reading the first
`a` (in state `q1`); after `2t+1` steps it ends in state `q2` reading `sep`, with
the block rewritten to the `[c, b]` pattern. -/
lemma zigzag {q1 q2 : Label l} {a b c : Symbol s}
    (h1 : M.get q1 a = .next b .left q2)
    (h2 : M.get q2 a = .next c .left q1)
    (t : ℕ) (sep : Symbol s) (L R : ListBlank (Symbol s)) :
    (⟨q1, Tape.mk' (List.replicate (2 * t) a ++ ListBlank.cons sep L) (ListBlank.cons a R)⟩
      : Config l s) -[M]{2 * t + 1}->
    ⟨q2, Tape.mk' L (ListBlank.cons sep (ListBlank.cons b (zigzagAcc b c t R)))⟩ := by
  have hpairs := zigzag_pairs h1 h2 t (ListBlank.cons sep L) R
  have hlast := step_left_mk' (l₀ := sep) h1 L (zigzagAcc b c t R)
  exact hpairs.tail hlast

end TM.Table
