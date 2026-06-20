import Busybeaver.Deciders.Sweep

/-!
# Directed-tape calculus (head on the left)

The reusable "head reads the top of the left side" configuration `headL`
(Coq BusyCoq's `l <{{q}} r`) and the corresponding abstract-left leftward step,
generic over `Machine l s`.  This is the same calculus proven inline for SM6
(Skelet #10) in `BB5Table.lean`, hoisted here so the binary-counter holdouts
SM9–12 can share it.
-/

namespace TM.Table

open Turing

variable {l s : ℕ} {M : Machine l s}

/-- Head-on-left directed configuration (Coq `l <{{q}} r`): the head reads the
top of `L`, so the underlying tape is `mk' L.tail (L.head :: R)`. -/
def headL (q : Label l) (L R : ListBlank (Symbol s)) : Config l s :=
  ⟨q, Tape.mk' L.tail (ListBlank.cons L.head R)⟩

@[simp] lemma headL_cons (q : Label l) (a : Symbol s) (L R : ListBlank (Symbol s)) :
    headL q (ListBlank.cons a L) R = ⟨q, Tape.mk' L (ListBlank.cons a R)⟩ := by
  simp [headL]

lemma headL_empty (q : Label l) (R : ListBlank (Symbol s)) :
    headL q ∅ R = ⟨q, Tape.mk' ∅ (ListBlank.cons default R)⟩ := rfl

/-- A leftward step with the left side abstract, landing in `headL` form
(the general form of `step_left_mk'`). -/
lemma step_left_head {q q' : Label l} {a b : Symbol s}
    (h : M.get q a = .next b .left q') (L R : ListBlank (Symbol s)) :
    (⟨q, Tape.mk' L (ListBlank.cons a R)⟩ : Config l s) -[M]-> headL q' L (ListBlank.cons b R) := by
  refine Machine.step.some' h ?_ ?_
  · simp
  · simp [Tape.write_mk', Tape.move_left_mk']

end TM.Table
