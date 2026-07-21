import Busybeaver.Deciders.Skelet.Skelet1.Stride

namespace Deciders.Skelet.Skelet1

open Turing TM.Table

/-- Symbolic reachability between compressed configurations.  Keeping the
large `lift` terms out of intermediate replay goals avoids repeatedly
unifying their enormous concrete tape expansions. -/
inductive SymReach : conf → conf → Prop
  | refl (c : conf) : SymReach c c
  | simple {c c' : conf} (h : simple_step c = some c') : SymReach c c'
  | stride {l : Ltape} {r r' : Rtape} (h : stride 0 1 r = some r') :
      SymReach (.right, l, r) (.left, l, r')
  | trans {c₁ c₂ c₃ : conf} : SymReach c₁ c₂ → SymReach c₂ c₃ → SymReach c₁ c₃

/-- Symbolic reachability is sound for the concrete machine. -/
lemma SymReach.sound {c c' : conf} (h : SymReach c c') :
    lift c -[M]->* lift c' := by
  induction h with
  | refl => exact Machine.EvStep.refl
  | simple hs => exact simple_step_spec _ _ hs
  | stride hs => exact stride_correct_0 _ _ _ hs
  | trans _ _ ih₁ ih₂ => exact ih₁.trans ih₂

/-- Add one computable symbolic simulator step, in continuation-passing form.
The explicit `next` argument lets elaboration reduce `simple_step` before it has
to unify the rest of a long replay. -/
lemma use_simple_step_sym_cps (current next target : conf)
    (h : simple_step current = some next)
    (cont : SymReach next target) : SymReach current target := by
  exact SymReach.trans (SymReach.simple h) cont

/-- A batch of ordinary simulator steps gives one compact symbolic edge.  This
keeps long non-stride stretches from producing deeply nested `SymReach.trans`
terms in generated universe replays. -/
lemma simpleSteps_sym (n : ℕ) (current next : conf)
    (h : simpleSteps n current = some next) : SymReach current next := by
  induction n generalizing current with
  | zero =>
      simp only [simpleSteps, Option.some.injEq] at h
      subst next
      exact SymReach.refl current
  | succ n ih =>
      simp only [simpleSteps] at h
      cases hs : simple_step current with
      | none => simp [hs] at h
      | some middle =>
          rw [hs] at h
          exact SymReach.trans (SymReach.simple hs) (ih middle h)

/-- Continuation-passing wrapper for a batch of ordinary symbolic steps. -/
lemma use_simpleSteps_sym_cps (n : ℕ) (current next target : conf)
    (h : simpleSteps n current = some next)
    (cont : SymReach next target) : SymReach current target := by
  exact SymReach.trans (simpleSteps_sym n current next h) cont

/-- Symbolic counterpart of `use_strideK`. -/
lemma use_strideK_sym (t t' : Rtape) (l : Ltape)
    (h : strideK 0 1 t id = some t') :
    SymReach (.right, l, t) (.left, l, t') := by
  rw [strideK_spec] at h
  cases hs : stride 0 1 t with
  | none => simp [hs] at h
  | some u =>
      simp [hs] at h
      subst t'
      exact SymReach.stride hs

/-- Symbolic/CPS version of `consume_stride_segment`.  Unlike the concrete
version below, its continuation never mentions `lift`, so a long generated
replay only manipulates small compressed configurations. -/
lemma consume_stride_segment_sym_cps
    (N m strideXs : ℕ) (t t' current : Rtape) (k : Rtape → Rtape)
    (left : Ltape) (target : conf)
    (h : stride 0 N t = some t')
    (hreduce : strideK 0 1 current id = strideK strideXs m t k)
    (hm : m ≤ N)
    (cont : ∀ u, stride 0 (N - m) u = some t' →
      SymReach (.left, left, k (rxs strideXs u)) target) :
    SymReach (.right, left, current) target := by
  have hmn : m + (N - m) = N := by omega
  obtain ⟨u, hu, hrest⟩ :=
    prepare_strideK t t' strideXs m (N - m) (by simpa [hmn] using h)
  have hstep : strideK 0 1 current id = some (k (rxs strideXs u)) := by
    rw [hreduce]
    simpa using hu k
  exact SymReach.trans (use_strideK_sym current (k (rxs strideXs u)) left hstep)
    (cont u hrest)

/-- Consume a variable-size stride segment and batch the following ordinary
steps in the compressed replay.  Generated certificates can use one such node
per stride phase instead of one node per simulator transition. -/
lemma consume_stride_segment_then_steps_sym_cps
    (N m strideXs steps : ℕ) (t t' current : Rtape)
    (k : Rtape → Rtape) (left : Ltape) (next : Rtape → conf)
    (target : conf)
    (h : stride 0 N t = some t')
    (hreduce : strideK 0 1 current id = strideK strideXs m t k)
    (hm : m ≤ N)
    (hsteps : ∀ u,
      simpleSteps steps (.left, left, k (rxs strideXs u)) = some (next u))
    (cont : ∀ u, stride 0 (N - m) u = some t' →
      SymReach (next u) target) :
    SymReach (.right, left, current) target := by
  exact consume_stride_segment_sym_cps N m strideXs t t' current k left target
    h hreduce hm fun u hu =>
      use_simpleSteps_sym_cps steps _ (next u) target (hsteps u) (cont u hu)

/-- Consume one unit directly from an abstract tail.  This specialized form
avoids asking elaboration to infer the segment length and continuation when a
replay reaches a bare tail variable. -/
lemma consume_stride_head_sym_cps
    (N : ℕ) (t t' : Rtape) (left : Ltape) (target : conf)
    (h : stride 0 N t = some t') (hN : 1 ≤ N)
    (cont : ∀ u, stride 0 (N - 1) u = some t' →
      SymReach (.left, left, u) target) :
    SymReach (.right, left, t) target := by
  simpa only [rxs, id_eq] using
    consume_stride_segment_sym_cps N 1 0 t t' t id left target h rfl hN cont

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

/-- Run ordinary symbolic steps until a stride becomes available.  This groups
long stretches of `simple_step` reductions into one compact proof term. -/
def simpleUntilStride : ℕ → conf → Option conf
  | 0, c => some c
  | n + 1, c =>
    match try_stride c with
    | some _ => some c
    | none =>
      match simple_step c with
      | some c' => simpleUntilStride n c'
      | none => none

lemma simpleUntilStride_spec (n : ℕ) (c c' : conf)
    (h : simpleUntilStride n c = some c') :
    lift c -[M]->* lift c' := by
  induction n generalizing c with
  | zero =>
      simp only [simpleUntilStride, Option.some.injEq] at h
      subst c'
      exact Machine.EvStep.refl
  | succ n ih =>
      simp only [simpleUntilStride] at h
      cases hs : try_stride c with
      | some d =>
          rw [hs] at h
          simp only [Option.some.injEq] at h
          subst c'
          exact Machine.EvStep.refl
      | none =>
          rw [hs] at h
          cases ht : simple_step c with
          | none => simp [ht] at h
          | some d =>
              rw [ht] at h
              exact (simple_step_spec c d ht).trans (ih d h)

/-- Consume one abstract stride segment and then compactly evaluate ordinary
symbolic steps up to the next available stride. -/
lemma consume_stride_segment_then_until_cps
    (N m strideXs fuel : ℕ) (t t' current : Rtape)
    (k : Rtape → Rtape) (left : Ltape) (next : Rtape → conf)
    (target : conf)
    (h : stride 0 N t = some t')
    (hreduce : strideK 0 1 current id = strideK strideXs m t k)
    (hm : m ≤ N)
    (hrun : ∀ u, simpleUntilStride fuel (.left, left, k (rxs strideXs u)) = some (next u))
    (cont : ∀ u, stride 0 (N - m) u = some t' →
      lift (next u) -[M]->* lift target) :
    lift (.right, left, current) -[M]->* lift target := by
  obtain ⟨u, eu, hu⟩ :=
    consume_stride_segment N m strideXs t t' current k left hm h hreduce
  exact eu.trans ((simpleUntilStride_spec fuel _ _ (hrun u)).trans (cont u hu))

end Deciders.Skelet.Skelet1
