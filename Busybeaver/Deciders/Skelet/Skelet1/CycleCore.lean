import Busybeaver.Deciders.Skelet.Skelet1.Universe
import Busybeaver.TM.Table.ClosedSet

/-!
# Skelet #1 — cyclic family and evaluator soundness

This module contains the reusable logical half of the Skelet #1 non-halting
argument.  It is deliberately separated from both the expensive universe-cycle
replay and the large concrete reflective certificate, so changes to generic
iteration/non-halting reasoning do not force either computation to be rebuilt.
-/

namespace Deciders.Skelet.Skelet1

open Turing TM.Table

/-! ## Iterating `fullstep`. -/

/-- Coq `steps`. -/
def steps : ℕ → conf → Option conf
  | 0, c => some c
  | n + 1, c =>
    match fullstep c with
    | some c' => steps n c'
    | none => none

lemma steps_spec (n : ℕ) (c c' : conf) (h : steps n c = some c') :
    lift c -[M]->* lift c' := by
  induction' n with n ih generalizing c;
  · cases h ; tauto;
  · cases h' : fullstep c <;> simp_all +decide [ steps ];
    exact fullstep_spec _ _ h' |> fun h'' => h''.trans ( ih _ _ _ h )

/-! ## The infinite cyclic family. -/

/-- An `EvStep` between distinct configurations is a `Progress` (≥ 1 step). -/
lemma evstep_progress_of_ne {A B : Config 4 1} (h : A -[M]->* B) (hne : A ≠ B) :
    A -[M]->+ B := by
  cases h with
  | refl => exact absurd rfl hne
  | step hstep tail => exact Trans.trans (Machine.Progress.single hstep) tail

/-- `steps` splits additively. -/
lemma steps_add (m n : ℕ) (c : conf) :
    steps (m + n) c = (steps m c).bind (steps n) := by
  induction m generalizing c with
  | zero => simp [steps]
  | succ m ih =>
    rw [show m + 1 + n = (m + n) + 1 by omega]
    cases hf : fullstep c with
    | none => simp [steps, hf]
    | some c' => simp only [steps, hf]; exact ih c'

/-- A right-facing lift is never equal to a left-facing lift (states differ). -/
lemma lift_right_ne_left (a b : Ltape) (c d : Rtape) :
    lift (.right, a, c) ≠ lift (.left, b, d) := by
  intro h
  have hs := congrArg Config.state h
  simp only [lift, AR, CL, headL] at hs
  exact absurd hs (by decide)

/-- The configuration reached after 30 accelerated steps from the reset
configuration (with symbolic tail `l`).  It faces `left`. -/
def cyc30 (l : Ltape) : conf :=
  (.left,
    [Lsym.C0, Lsym.xs 7087, Lsym.D, Lsym.D, Lsym.xs 2179, Lsym.C0,
     Lsym.xs 13074, Lsym.D, Lsym.xs 6275, Lsym.C0, Lsym.xs 11026, Lsym.D,
     Lsym.xs 7299, Lsym.C0, Lsym.xs 10514, Lsym.D, Lsym.xs 7555, Lsym.C0,
     Lsym.xs 10386, Lsym.D, Lsym.xs 7619, Lsym.C0, Lsym.xs 10354, Lsym.D,
     Lsym.xs 7635, Lsym.C0, Lsym.xs 10346, Lsym.D, Lsym.xs 7639, Lsym.C0] ++ l,
    [Rsym.Cr, Rsym.xs 3851, Rsym.P])

set_option maxRecDepth 200000 in
/-- Coq `infinite_cycle`: the reset configuration `(right, l_C0 :: l, K)` returns
to a larger copy of itself (`F` prepended), making genuine progress. -/
lemma infinite_cycle (l : Ltape) :
    lift (.right, Lsym.C0 :: l, K) -[M]->+ lift (.right, Lsym.C0 :: F ++ l, K) := by
  have h30 : steps 30 (.right, Lsym.C0 :: l, K) = some (cyc30 l) := by
    rw [cyc30]; rfl
  have h982 : steps 982 (.right, Lsym.C0 :: l, K) = some (.right, Lsym.C0 :: F ++ l, K) := by
    rfl
  have h952 : steps 952 (cyc30 l) = some (.right, Lsym.C0 :: F ++ l, K) := by
    have := steps_add 30 952 (.right, Lsym.C0 :: l, K)
    rw [h30] at this
    simpa [h982] using this.symm
  have e1 : lift (.right, Lsym.C0 :: l, K) -[M]->* lift (cyc30 l) :=
    steps_spec 30 _ _ h30
  have e2 : lift (cyc30 l) -[M]->* lift (.right, Lsym.C0 :: F ++ l, K) :=
    steps_spec 952 _ _ h952
  have hne : lift (.right, Lsym.C0 :: l, K) ≠ lift (cyc30 l) := by
    rw [cyc30]; exact lift_right_ne_left _ _ _ _
  exact Trans.trans (evstep_progress_of_ne e1 hne) e2

/-- Coq `cycle_nonhalt`: any reset configuration does not halt. -/
lemma cycle_nonhalt (l : Ltape) : ¬ M.halts (lift (.right, Lsym.C0 :: l, K)) := by
  have cs : ClosedSet M (fun C => ∃ l, C = lift (.right, Lsym.C0 :: l, K))
      (lift (.right, Lsym.C0 :: l, K)) := by
    refine ⟨?_, ?_⟩
    · rintro ⟨C, l', rfl⟩
      exact ⟨⟨lift (.right, Lsym.C0 :: F ++ l', K), F ++ l', rfl⟩, infinite_cycle l'⟩
    · exact ⟨⟨_, l, rfl⟩, Machine.EvStep.refl⟩
  exact cs.nonHalting

/-! ## The reflective reachability computation. -/

/-- Coq `is_cycling`. -/
def is_cycling : conf → Bool
  | (.right, Lsym.C0 :: _, r) => decide (r = K)
  | _ => false

lemma is_cycling_spec (c : conf) (h : is_cycling c = true) :
    ¬ M.halts (lift c) := by
  rcases c with ⟨ d, l, r ⟩;
  rcases d with ( _ | _ | d ) <;> rcases l with ( _ | _ | l ) <;> simp_all +decide [ is_cycling ];
  exact cycle_nonhalt _

/-- Coq `doit`. -/
def doit : ℕ → conf → Bool
  | 0, _ => false
  | n + 1, c =>
    if is_cycling c then true
    else
      match fullstep c with
      | some c' => doit n c'
      | none => false

/-
If `A -[M]->* B` and `B` does not halt, then `A` does not halt.
-/
lemma multistep_nonhalt {A B : Config 4 1} (h : A -[M]->* B) (hB : ¬ M.halts B) :
    ¬ M.halts A := by
  convert Machine.halts.skip_evstep h ‹_› using 1

lemma doit_spec (n : ℕ) (c : conf) (h : doit n c = true) :
    ¬ M.halts (lift c) := by
  induction' n with n ih generalizing c;
  · cases h;
  · by_cases h_cycling : is_cycling c;
    · exact is_cycling_spec c h_cycling;
    · obtain ⟨c', hc'⟩ : ∃ c', fullstep c = some c' ∧ doit n c' = true := by
        unfold doit at h; aesop;
      exact multistep_nonhalt ( fullstep_spec c c' hc'.1 ) ( ih c' hc'.2 )

end Deciders.Skelet.Skelet1
