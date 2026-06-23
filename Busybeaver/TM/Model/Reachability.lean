import Busybeaver.Basic

namespace TM.Model

variable {M : Type _} [TM.Model M]

-- Stepping with machine M from A leads to B in one step (not base steps)
def Step (m : M) (A B : Config M) : Prop :=
  (TM.Model.step m A |>.outcome) = .continue B

-- TODO: Remove the tick from this macro once we delete the old version.
notation (priority:=high) s₁ "-["m"]->'" s₂ => Step m s₁ s₂

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


def StepBase (m : M) (k : ℕ) (A B : Config M) : Prop :=
  (TM.Model.step m A) = ⟨k, .continue B⟩

-- `Base` talks about the base machine, so MultistepBase counts the number of steps taken by that machine,
-- rather than the high-level machine M.
inductive MultistepBase (m : M) : Nat → Config M → Config M → Prop
| refl {C} : MultistepBase m 0 C C
| step {A B C n₁ n₂} : StepBase m n₁ A B → MultistepBase m n₂ B C → MultistepBase m (n₁ + n₂) A C

notation (priority:=high) s₁ "-["m"]{"k"}->>'" s₂ => MultistepBase m k s₁ s₂

namespace Multistep

lemma single {m : M} (hAB : A -[m]->' B) : A -[m]{1}->' B :=
  .step hAB .refl

lemma single' {m : M} (h : A -[m]{1}->' B) : A -[m]->' B :=
  match h with | .step hAB .refl => hAB

lemma trans {m : M} (hAB : A -[m]{i}->' B) (hBC : B -[m]{j}->' C) :
    A -[m]{i + j}->' C := by
  induction hAB with
  | refl => simpa using hBC
  | step hAB _ IH => simpa [Nat.add_right_comm] using Multistep.step hAB (IH hBC)

lemma step_to_base {m : M} (hAB : A -[m]->' B) : ∃ n, StepBase m n A B := by
  cases hstep : TM.Model.step m A with
  | mk n outcome =>
      refine ⟨n, ?_⟩
      unfold Step at hAB
      simpa [StepBase, hstep] using hAB

lemma to_base {m : M} (hAB : A -[m]{i}->' B) : ∃ n, A -[m]{n}->>' B := by
  induction hAB with
  | refl => exact ⟨0, .refl⟩
  | step hAB _ IH =>
      obtain ⟨n₁, hn₁⟩ := step_to_base hAB
      obtain ⟨n₂, hn₂⟩ := IH
      exact ⟨_, .step hn₁ hn₂⟩

lemma deterministic {m : M} (hB : A -[m]{n}->' B) (hC : A -[m]{n}->' C) : B = C := by
  induction hB generalizing C with
  | refl => cases hC; rfl
  | step hAB _ IH =>
      cases hC with
      | step hAC hCC =>
          unfold Step at hAB hAC
          rw [hAC] at hAB
          cases hAB
          exact IH hCC

lemma split {m : M} (h : A -[m]{n + k}->' B) : ∃ D : Config M, (A -[m]{n}->' D) ∧ (D -[m]{k}->' B) := by
  induction n generalizing A B with
  | zero => exact ⟨A, .refl, by simpa using h⟩
  | succ n IH =>
      have h' : A -[m]{(n + k) + 1}->' B := by rwa [Nat.add_right_comm]
      cases h' with
      | step hAX hXB =>
          obtain ⟨D, hXD, hDB⟩ := IH hXB
          exact ⟨D, .step hAX hXD, hDB⟩

lemma split_le {m : M} (hB : A -[m]{n}->' B) (hC : A -[m]{k}->' C) (hk : k ≤ n) :
    C -[m]{n - k}->' B := by
  obtain ⟨D, hAD, hDB⟩ := split (n := k) (k := n - k) (by rwa [Nat.add_sub_of_le hk])
  rwa [deterministic hAD hC] at hDB

lemma split_add {m : M} (hB : A -[m]{n}->' B) (hC : A -[m]{n + k}->' C) : B -[m]{k}->' C :=
  by simpa [Nat.add_sub_cancel_left] using split_le hC hB (Nat.le_add_right n k)

lemma to_evstep {m : M} (h : A -[m]{n}->' B) : A -[m]->*' B := by
  induction h with
  | refl => exact .refl
  | step hAB _ IH => exact .step hAB IH

end Multistep

namespace MultistepBase

lemma single {m : M} (hAB : StepBase m n A B) : A -[m]{n}->>' B :=
  .step hAB .refl

lemma trans {m : M} (hAB : A -[m]{i}->>' B) (hBC : B -[m]{j}->>' C) :
    A -[m]{i + j}->>' C := by
  induction hAB with
  | refl => simpa using hBC
  | step hAB _ IH => simpa [Nat.add_assoc] using MultistepBase.step hAB (IH hBC)

end MultistepBase

def halts_in_base (m : M) (k : Nat) (A : Config M) : Prop := ∃ C, LastState m C ∧ A -[m]{k}->' C

def halts (m : M) (A : Config M) : Prop := ∃ k, halts_in_base m k A

inductive HaltM (m : M) (α : Type _)
| unknown : α → HaltM m α
| halts_prf n C : LastState m C ∧ (default -[m]{n}->>' C) → HaltM m α
| loops_prf : ¬halts m default → HaltM m α

namespace HaltM

variable {m : M} {α : Type _}

instance (m : M) : Monad (HaltM m) where
  pure := .unknown
  bind := fun x f =>
    match x with
    | .unknown v => f v
    | .halts_prf k C h => .halts_prf k C h
    | .loops_prf h => .loops_prf h

def decided : HaltM m α → Bool
| .unknown _ => false
| _ => true

end HaltM

namespace Progress

lemma trans {m : M} (hA : A -[m]->+' B) (hB : B -[m]->+' C) : A -[m]->+' C := by
  induction hA with
  | single h => exact .step h hB
  | step hAB _ IH => exact .step hAB (IH hB)

lemma to_multistep {m : M} (h : A -[m]->+' B) : ∃ n, A -[m]{n + 1}->' B := by
  induction h with
  | single h => exact ⟨0, Multistep.single h⟩
  | step hAB _ IH =>
      obtain ⟨n, hn⟩ := IH
      exact ⟨n + 1, by simpa [Nat.add_assoc] using Multistep.step hAB hn⟩

lemma from_multistep {m : M} (h : A -[m]{n + 1}->' B) : A -[m]->+' B := by
  induction n generalizing A with
  | zero => exact .single (Multistep.single' h)
  | succ n IH =>
      cases h with
      | step hAB hBC => exact trans (.single hAB) (IH hBC)

end Progress

namespace Machine.EvStep

lemma trans {m : M} (hA : A -[m]->*' B) (hB : B -[m]->*' C) : A -[m]->*' C := by
  induction hA with
  | refl => exact hB
  | step hAB _ IH => exact .step hAB (IH hB)

lemma to_multistep {m : M} (h : A -[m]->*' B) : ∃ n, A -[m]{n}->' B := by
  induction h with
  | refl => exact ⟨0, .refl⟩
  | step hAB _ IH =>
      obtain ⟨n, hn⟩ := IH
      exact ⟨n + 1, .step hAB hn⟩

lemma trans_progress {m : M} (hA : A -[m]->*' B) (hB : B -[m]->+' C) : A -[m]->+' C := by
  induction hA with
  | refl => exact hB
  | step hAB _ IH => exact .step hAB (IH hB)

end Machine.EvStep

namespace halts_in_base

lemma no_multistep {m : M} (hM : LastState m A) : ¬(A -[m]{n + 1}->' C) := by
  intro hAC
  cases hstep : TM.Model.step m A with
  | mk dn outcome =>
      cases outcome <;> simp [LastState, hstep] at hM
      case halted cfg =>
        cases hAC with
        | step hAB _ =>
            unfold Step at hAB
            simp [hstep] at hAB

lemma no_progress {m : M} (hM : LastState m A) : ¬(A -[m]->+' B) := by
  intro hAC
  obtain ⟨n, hn⟩ := Progress.to_multistep hAC
  exact no_multistep hM hn

lemma evstep_same {m : M} (hM : LastState m A) (h : A -[m]->*' B) : A = B := by
  obtain ⟨n, hn⟩ := Machine.EvStep.to_multistep h
  cases n with
  | zero => cases hn; rfl
  | succ n => exact absurd hn (no_multistep hM)

lemma no_multistep' {m : M} (hM : LastState m A) (hn : 0 < n) : ¬(A -[m]{n}->' C) := by
  rw [← Nat.sub_one_add_one_eq_of_pos hn]
  exact no_multistep hM

lemma preceeds {m : M} (hM : halts_in_base m k A) (hAB : A -[m]{n}->' B) (hk : n ≤ k) :
    halts_in_base m (k - n) B := by
  obtain ⟨C, hCl, hAC⟩ := hM
  exact ⟨C, hCl, Multistep.split_le hAC hAB hk⟩

lemma within {m : M} (hM : halts_in_base m k A) (hB : A -[m]{n}->' B) : n ≤ k := by
  by_contra hk
  simp only [not_le] at hk
  obtain ⟨C, hCl, hAC⟩ := hM
  exact no_multistep' hCl (Nat.sub_pos_of_lt hk) (Multistep.split_le hB hAC hk.le)

end halts_in_base

namespace halts

lemma mono {m : M} (h : A -[m]{n}->' B) (hM : halts m B) : halts m A := by
  obtain ⟨nb, C, hCl, hBC⟩ := hM
  exact ⟨n + nb, C, hCl, Multistep.trans h hBC⟩

lemma tail {m : M} (h : A -[m]{n}->' B) (hM : halts m A) : halts m B := by
  obtain ⟨k, hk⟩ := hM
  have hkn := halts_in_base.within hk h
  exact ⟨k - n, halts_in_base.preceeds hk h hkn⟩

lemma skip {m : M} (h : A -[m]{n}->' B) (hM : ¬halts m B) : ¬halts m A :=
  fun hA => hM (tail h hA)

lemma skip_evstep {m : M} (h : A -[m]->*' B) (hM : ¬halts m B) : ¬halts m A := by
  obtain ⟨n, hn⟩ := Machine.EvStep.to_multistep h
  exact skip hn hM

lemma skip_next {m : M} (h : A -[m]->' B) (hM : ¬halts m B) : ¬halts m A :=
  skip (Multistep.single h) hM

end halts

noncomputable def stepH (m : M) (σ : {s // default -[m]{k}->' s}) :
    HaltM m {s' // default -[m]{k + 1}->' s'} :=
  match hstep : TM.Model.step m σ.val with
  | ⟨_, .halted _⟩ =>
      let n := Classical.choose (Multistep.to_base σ.prop)
      .halts_prf n σ.val <| by
        constructor
        · simp [TM.Model.LastState, hstep]
        · exact Classical.choose_spec (Multistep.to_base σ.prop)
  | ⟨_, .continue nxt⟩ =>
      .unknown ⟨nxt, by
        have hcontinue : σ.val -[m]->' nxt := by
          simp [Step, hstep]
        simpa using Multistep.trans σ.prop (Multistep.single hcontinue)⟩

end TM.Model
