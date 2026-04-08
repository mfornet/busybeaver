-- TODO: Move to Busybeaver/Model/Reachability.lean
import Busybeaver.Basic

namespace TM.Model

variable {M : Type _} [TM.Model M]

-- Stepping with machine M from A leads to B in one step (not base steps)
def Step {M : Type _} [TM.Model M] (m : M) (A B : Config M) : Prop :=
  (TM.Model.step m A |>.outcome) = .continue B

notation (priority:=high) s₁ "-[" M "]->'" s₂ => Step M s₁ s₂

inductive Multistep (m : M) : Nat → Config M → Config M → Prop
| refl {C} : Multistep m 0 C C
| step {A B C n} : (A -[m]->' B) → Multistep m n B C → Multistep m (n+1) A C

notation (priority:=high) s₁ "-["M"]{"k"}->'" s₂ => Multistep M k s₁ s₂

inductive Progress (m : M) : Config M → Config M → Prop
| single {C C'} : (C -[m]->' C') → Progress m C C'
| step {A B C} : (A -[m]->' B) → Progress m B C → Progress m A C

notation A " -[" m "]->+' " B => Progress m A B

inductive Machine.EvStep (m : M): Config M → Config M → Prop
| refl {C} : Machine.EvStep m C C
| step {A B C} : (A -[m]->' B) → Machine.EvStep m B C → Machine.EvStep m  A C

notation A " -["m"]->*' " B => Machine.EvStep m A B

-- def StepRel {M : Type _} [TM.Model M] (m : M) (k : Nat) (A B : Config M) : Prop :=
--   TM.Model.step m A = ⟨k, .continue B⟩

-- def SegmentHaltRel {M : Type _} [TM.Model M] (m : M) (k : Nat) (A B : Config M) : Prop :=
--   TM.Model.step m A = ⟨k, .halted B⟩

-- inductive HaltRel (m : M) : Nat → Config M → Config M → Prop
-- | halt {k A B} : SegmentHaltRel m k A B → HaltRel m k A B
-- | step {i j A B C} :
--     StepRel m i A B →
--     HaltRel m j B C →
--     HaltRel m (i + j) A C

-- def halts_in (m : M) (k : Nat) (A : Config M) : Prop := ∃ C, HaltRel m k A C

-- def halts (m : M) (A : Config M) : Prop := ∃ k, halts_in m k A

-- namespace Multistep

-- lemma single {m : M} (hAB : StepRel m k A B) : Multistep m k A B := by
--   exact .step hAB .refl

-- lemma trans {m : M} (hAB : Multistep m i A B) (hBC : Multistep m j B C) :
--     Multistep m (i + j) A C := by
--   induction hAB with
--   | refl =>
--       simpa using hBC
--   | @step i j A B D hAB hBD IH =>
--       simpa [Nat.add_assoc] using
--         Multistep.step hAB (IH hBC)

-- end Multistep

-- namespace HaltRel

-- lemma to_halts_in {m : M} (h : HaltRel m k A B) : halts_in m k A := ⟨B, h⟩

-- lemma to_halts {m : M} (h : HaltRel m k A B) : halts m A := ⟨k, h.to_halts_in⟩

-- lemma trans_multistep {m : M} (hAB : Multistep m i A B) (hBC : HaltRel m j B C) :
--     HaltRel m (i + j) A C := by
--   induction hAB with
--   | refl =>
--       simpa using hBC
--   | @step i j A B D hAB hBD IH =>
--       simpa [Nat.add_assoc] using
--         HaltRel.step hAB (IH hBC)

-- end HaltRel

-- inductive HaltM (m : M) (α : Type _)
-- | unknown : α → HaltM m α
-- | halts_prf : ∀ k C, HaltRel m k (init M) C → HaltM m α
-- | loops_prf : ¬halts m (init M) → HaltM m α

-- namespace HaltM

-- variable {m : M} {α : Type _}

-- instance (m : M) : Monad (HaltM m) where
--   pure := .unknown
--   bind := fun x f =>
--     match x with
--     | .unknown v => f v
--     | .halts_prf k C h => .halts_prf k C h
--     | .loops_prf h => .loops_prf h

-- def decided : HaltM m α → Bool
-- | .unknown _ => false
-- | _ => true

-- end HaltM

-- abbrev GDecider (M : Type _) [TM.Model M] :=
--   (m : M) → HaltM m Unit

end TM.Model
