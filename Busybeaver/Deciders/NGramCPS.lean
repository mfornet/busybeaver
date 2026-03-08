/-!
# 1-gram Closed Position Set (n-gram CPS) Decider

Represents tape configurations abstractly as 4-tuples:
  (symbol left of head, current state, symbol under head, symbol right of head)

Computes the forward closure from the initial abstract position and checks
whether any halting transition is reachable. If not, the machine loops forever.

This is an instance of the n-gram CPS family with n = 1.

Reference: paper §4.4, Coq `NGramCPS_decider_spec`.
-/
import Busybeaver.Basic
import Busybeaver.Reachability
import Busybeaver.ClosedSet

namespace TM

open Machine

/-!
## Abstract positions
-/

/-- Abstract 1-gram position: the four-tuple
    (symbol immediately left of head, current state, symbol under head, symbol immediately right). -/
structure NGramPos (l s : ℕ) where
  left  : Symbol s
  state : Label l
  sym   : Symbol s
  right : Symbol s
deriving DecidableEq, Repr

/-- `NGramPos l s` is finite — it embeds into a product of four finite types. -/
instance : Fintype (NGramPos l s) :=
  Fintype.ofEquiv (Symbol s × Label l × Symbol s × Symbol s) {
    toFun    := fun p => { left := p.1, state := p.2.1, sym := p.2.2.1, right := p.2.2.2 }
    invFun   := fun p => (p.left, p.state, p.sym, p.right)
    left_inv := fun _ => rfl
    right_inv := fun _ => rfl
  }

/-- The initial abstract position: all blank tape, initial (default) state. -/
def NGramPos.init : NGramPos l s := ⟨default, default, default, default⟩

/-!
## Successor function
-/

/-- One-step successors of an abstract position under machine `M`.

When moving right we write `sym'`, the new head is the old `right`, and the
new right symbol is unknown — so we enumerate all symbols.
When moving left the symmetric situation applies. -/
def NGramPos.successors (M : Machine l s) (p : NGramPos l s) : Finset (NGramPos l s) :=
  match M.get p.state p.sym with
  | .halt       => ∅
  | .next sym' .right lab' =>
      -- Move right: left ← sym', head ← p.right, right ← ?
      Finset.univ.image (fun r => ⟨sym', lab', p.right, r⟩)
  | .next sym' .left lab' =>
      -- Move left: right ← sym', head ← p.left, left ← ?
      Finset.univ.image (fun l => ⟨l, lab', p.left, sym'⟩)

/-!
## Abstraction function and key lemma
-/

/-- Extract the abstract position from a concrete configuration. -/
def Config.toNGram (C : Config l s) : NGramPos l s :=
  ⟨C.tape.left.head, C.state, C.tape.head, C.tape.right.head⟩

@[simp]
lemma Config.toNGram_init : (init : Config l s).toNGram = NGramPos.init := by
  simp [Config.toNGram, NGramPos.init, init, default]

/-- After one machine step, the new abstract position is a successor of the old one.

**Proof sketch** (direction Right):
- After writing `sym'` and moving right:
  - new `tape.head`      = old `tape.right.head`   = `p.right`
  - new `tape.left.head` = `sym'`                  (just written, now the top of the left stack)
  - new `tape.right.head` = old `tape.right.tail.head` (unknown; we cover all values)
- So the new abstract position is `⟨sym', lab', p.right, ?⟩` for some `?`, which is in the
  image over all symbols. -/
lemma Config.toNGram_step_succ {M : Machine l s} {C C' : Config l s}
    (hStep : C -[M]-> C') :
    C'.toNGram ∈ NGramPos.successors M C.toNGram := by
  obtain ⟨sym', dir, hM, hC'tape⟩ := Machine.step.some_rev hStep
  simp only [NGramPos.successors, Config.toNGram, hM]
  cases dir with
  | right =>
    simp only [Finset.mem_image, Finset.mem_univ, true_and]
    -- Witness: the new right symbol (old tape.right.tail.head, which we don't track)
    exact ⟨C'.tape.right.head, by
      simp [Config.toNGram, hC'tape, Turing.Tape.write, Turing.Tape.move]⟩
  | left =>
    simp only [Finset.mem_image, Finset.mem_univ, true_and]
    -- Witness: the new left symbol (old tape.left.tail.head, which we don't track)
    exact ⟨C'.tape.left.head, by
      simp [Config.toNGram, hC'tape, Turing.Tape.write, Turing.Tape.move]⟩

/-!
## Main correctness theorem
-/

/-- If `closure` is a closed set of abstract positions that:
  1. Is closed under the successor function,
  2. Contains the initial abstract position, and
  3. Contains no halting position,
then the machine does not halt. -/
theorem ngramCPS_correct {M : Machine l s} {closure : Finset (NGramPos l s)}
    (hClosed  : ∀ p ∈ closure, NGramPos.successors M p ⊆ closure)
    (hInit    : NGramPos.init ∈ closure)
    (hNoHalt  : ∀ p ∈ closure, M.get p.state p.sym ≠ .halt) :
    ¬M.halts init := by
  closed_set (fun C => C.toNGram ∈ closure)
  · -- Closed: every config satisfying the invariant can progress to another.
    intro ⟨C, hC⟩
    have hNotHalt : M.get C.state C.tape.head ≠ .halt := hNoHalt _ hC
    -- C is not halting, so it can take a step.
    cases hh : M.step C with
    | none  => exact absurd (Machine.step.none.mp hh) hNotHalt
    | some C' =>
        have hC'mem : C'.toNGram ∈ closure :=
          hClosed _ hC (Config.toNGram_step_succ hh)
        exact ⟨⟨C', hC'mem⟩, Machine.Progress.single hh⟩
  · -- Enters: the initial config satisfies the invariant.
    exact ⟨⟨init, Config.toNGram_init ▸ hInit⟩, Machine.EvStep.refl⟩

/-!
## Forward closure computation
-/

/-- One closure step: add all immediate successors of current positions. -/
def ngramStep (M : Machine l s) (current : Finset (NGramPos l s)) : Finset (NGramPos l s) :=
  current ∪ current.fold (· ∪ ·) ∅ (NGramPos.successors M)

lemma ngramStep_mono (M : Machine l s) (current : Finset (NGramPos l s)) :
    current ⊆ ngramStep M current :=
  Finset.subset_union_left

lemma ngramStep_succ_mem {M : Machine l s} {current : Finset (NGramPos l s)}
    {p : NGramPos l s} (hp : p ∈ current)
    {q : NGramPos l s} (hq : q ∈ NGramPos.successors M p) :
    q ∈ ngramStep M current := by
  simp only [ngramStep, Finset.mem_union, Finset.mem_fold_union]
  exact Or.inr ⟨p, hp, hq⟩

/-- Iterate `ngramStep` `bound` times starting from `{init}`. -/
def ngramClosure (bound : ℕ) (M : Machine l s) : Finset (NGramPos l s) :=
  (List.range bound).foldl (fun current _ => ngramStep M current) {NGramPos.init}

@[simp]
lemma ngramClosure_zero (M : Machine l s) : ngramClosure 0 M = {NGramPos.init} := rfl

lemma ngramClosure_succ (M : Machine l s) (n : ℕ) :
    ngramClosure (n + 1) M = ngramStep M (ngramClosure n M) := by
  simp [ngramClosure, List.range_succ, List.foldl_append]

lemma ngramClosure_mono (M : Machine l s) (n : ℕ) :
    ngramClosure n M ⊆ ngramClosure (n + 1) M := by
  rw [ngramClosure_succ]
  exact ngramStep_mono M _

/-- The initial abstract position is always in the closure, for any bound. -/
lemma ngramClosure_init_mem (M : Machine l s) (bound : ℕ) :
    NGramPos.init ∈ ngramClosure bound M := by
  induction bound with
  | zero      => simp
  | succ n IH => exact ngramClosure_mono M n IH

/-!
## Decider
-/

/-- 1-gram CPS decider with `bound` closure iterations.

Computes the forward closure of the initial abstract position and checks:
- Every position in the closure has all its successors also in the closure
  (i.e. the closure is stable / fixed-point reached).
- No position in the closure corresponds to a halting transition.

If both conditions hold, the machine provably does not halt. -/
def ngramCPSDecider (bound : ℕ) (M : Machine l s) : HaltM M Unit :=
  let closure := ngramClosure bound M
  if h : (∀ p ∈ closure, NGramPos.successors M p ⊆ closure) ∧
         (∀ p ∈ closure, M.get p.state p.sym ≠ .halt) then
    .loops_prf (ngramCPS_correct h.1 (ngramClosure_init_mem M bound) h.2)
  else
    .unknown ()

end TM
