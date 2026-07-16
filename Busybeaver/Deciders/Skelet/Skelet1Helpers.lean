import Busybeaver.Deciders.Skelet.Skelet1Stride

namespace Deciders.Skelet.Skelet1

open Turing TM.Table

/-- Turn a successful continuation-passing unit stride into a concrete machine
execution.  This is the Lean counterpart of Coq's `use_stride'`, and is the
basic proof-producing operation needed by the universe-cycle replay. -/
lemma use_strideK (t t' : Rtape) (l : Ltape)
    (h : strideK 0 1 t id = some t') :
    lift (.right, l, t) -[M]->* lift (.left, l, t') := by
  rw [strideK_spec] at h
  cases hs : stride 0 1 t with
  | none => simp [hs] at h
  | some u =>
      simp [hs] at h
      subst t'
      exact stride_correct_0 t u (liftL l) hs

/-- Peel one unit from a positive long stride and simultaneously realize that
unit as a concrete execution of `M`.  This packages the recurring bookkeeping
step in Coq's `apply_stride` tactic. -/
lemma peel_stride_execution (N : ℕ) (t t' : Rtape) (l : Ltape)
    (hN : 0 < N) (h : stride 0 N t = some t') :
    ∃ u, (lift (.right, l, t) -[M]->* lift (.left, l, u)) ∧
      stride 0 (N - 1) u = some t' := by
  have heq : 1 + (N - 1) = N := by omega
  obtain ⟨u, hu, hrest⟩ := prepare_strideK t t' 0 1 (N - 1) (by simpa [heq] using h)
  exact ⟨u, use_strideK t (rxs 0 u) l (by simpa using hu id), by simpa using hrest⟩

/-- Successor-indexed variant of `peel_stride_execution`, avoiding subtraction
in long symbolic replays. -/
lemma peel_stride_execution_succ (N : ℕ) (t t' : Rtape) (l : Ltape)
    (h : stride 0 (N + 1) t = some t') :
    ∃ u, (lift (.right, l, t) -[M]->* lift (.left, l, u)) ∧
      stride 0 N u = some t' := by
  obtain ⟨u, hu, hrest⟩ := prepare_strideK t t' 0 1 N (by simpa [Nat.add_comm] using h)
  exact ⟨u, use_strideK t (rxs 0 u) l (by simpa using hu id), hrest⟩

/-
Execute a unit stride on an explicit symbolic tape when its reduction calls
for an `m`-unit stride on an abstract tail `t`.  Unlike
`peel_stride_execution`, this consumes the entire requested tail segment at
once, matching the variable-size splitting performed by Coq's `apply_stride`.
-/
lemma consume_stride_segment (N m xs : ℕ) (t t' current : Rtape)
    (k : Rtape → Rtape) (l : Ltape) (hm : m ≤ N)
    (h : stride 0 N t = some t')
    (hreduce : strideK 0 1 current id = strideK xs m t k) :
    ∃ u, (lift (.right, l, current) -[M]->*
      lift (.left, l, k (rxs xs u))) ∧
      stride 0 (N - m) u = some t' := by
  have hmn : m + (N - m) = N := by omega
  obtain ⟨u, hu, hrest⟩ := prepare_strideK t t' xs m (N - m) (by simpa [hmn] using h)
  have h_step : strideK 0 1 current id = some (k (rxs xs u)) := by
    rw [hreduce]
    simpa using hu k
  exact ⟨u, use_strideK current (k (rxs xs u)) l h_step, hrest⟩

/-
Consume a variable-size stride segment and immediately replay a fixed number
of ordinary symbolic steps.  This packages one complete iteration of Coq's
`apply_stride; repeat apply_simple` replay pattern.
-/
lemma consume_stride_segment_then_steps
    (N m strideXs steps : ℕ) (t t' current : Rtape)
    (k : Rtape → Rtape) (left : Ltape) (next : conf)
    (hm : m ≤ N) (h : stride 0 N t = some t')
    (hreduce : strideK 0 1 current id = strideK strideXs m t k)
    (hsteps : ∀ u, simpleSteps steps (.left, left, k (rxs strideXs u)) = some next) :
    ∃ u, (lift (.right, left, current) -[M]->* lift next) ∧
      stride 0 (N - m) u = some t' := by
  obtain ⟨ u, hu ⟩ := consume_stride_segment N m strideXs t t' current k left hm h hreduce;
  exact ⟨ u, hu.1.trans ( simpleSteps_spec _ _ _ ( hsteps u ) ), hu.2 ⟩

/-
Dependent version of `consume_stride_segment_then_steps`, allowing the
post-step symbolic configuration to retain the freshly exposed tail.
-/
lemma consume_stride_segment_then_steps_dep
    (N m strideXs steps : ℕ) (t t' current : Rtape)
    (k : Rtape → Rtape) (left : Ltape) (next : Rtape → conf)
    (hm : m ≤ N) (h : stride 0 N t = some t')
    (hreduce : strideK 0 1 current id = strideK strideXs m t k)
    (hsteps : ∀ u, simpleSteps steps (.left, left, k (rxs strideXs u)) = some (next u)) :
    ∃ u, (lift (.right, left, current) -[M]->* lift (next u)) ∧
      stride 0 (N - m) u = some t' := by
  have := @Deciders.Skelet.Skelet1.consume_stride_segment;
  exact this N m strideXs t t' current k left hm h hreduce |> fun ⟨ u, hu₁, hu₂ ⟩ => ⟨ u, hu₁.trans <| simpleSteps_spec steps _ _ <| hsteps u, hu₂ ⟩

/-- Continuation form of `consume_stride_segment`.  This is convenient for a
recursive symbolic replay: after consuming the exposed tail stride, the caller
only has to prove the rest of the execution for every possible residual tail. -/
lemma consume_stride_segment_cps
    (N m strideXs : ℕ) (t t' current : Rtape) (k : Rtape → Rtape)
    (left : Ltape) (target : conf)
    (h : stride 0 N t = some t')
    (hreduce : strideK 0 1 current id = strideK strideXs m t k)
    (hm : m ≤ N)
    (cont : ∀ u, stride 0 (N - m) u = some t' →
      lift (.left, left, k (rxs strideXs u)) -[M]->* lift target) :
    lift (.right, left, current) -[M]->* lift target := by
  obtain ⟨u, eu, hu⟩ :=
    consume_stride_segment N m strideXs t t' current k left hm h hreduce
  exact eu.trans (cont u hu)

/-
CPS wrapper for a recurring `stride; simple steps; continue` phase of the
universe-cycle replay.
-/
lemma consume_stride_segment_then_steps_cps
    (N m strideXs steps : ℕ) (t t' current : Rtape)
    (k : Rtape → Rtape) (left : Ltape) (next : Rtape → conf)
    (target : conf)
    (h : stride 0 N t = some t')
    (hreduce : strideK 0 1 current id = strideK strideXs m t k)
    (hm : m ≤ N)
    (hsteps : ∀ u, simpleSteps steps (.left, left, k (rxs strideXs u)) = some (next u))
    (cont : ∀ u, stride 0 (N - m) u = some t' →
      lift (next u) -[M]->* lift target) :
    lift (.right, left, current) -[M]->* lift target := by
  -- Apply `consume_stride_segment_then_steps_dep` to obtain the existential execution and residual stride statement.
  obtain ⟨u, hu⟩ := consume_stride_segment_then_steps_dep N m strideXs steps t t' current k left next hm h hreduce hsteps;
  exact hu.1.trans ( cont u hu.2 )

end Deciders.Skelet.Skelet1
