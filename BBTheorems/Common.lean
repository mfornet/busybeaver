import Busybeaver

/-!
# Common scaffolding for the gated BB value theorems

The `BBTheorems` library states the concrete Busy Beaver values as kernel-level
theorems. It is **not** part of the default build (`lake build` skips it); build
it explicitly with

```
lake build BBTheorems            -- everything (BB(5,2) takes hours!)
lake build BBTheorems.BB2        -- a single value
```

Each value theorem instantiates `Busybeaver.BBCompute.correct_complete` with the
same pure decider pipeline the CLI uses, discharging the "no undecided machines"
hypothesis by `native_decide`. Two deliberate trust notes, and the reason this
library is gated out of the default build:

* `BBCompute` is defined by well-founded recursion, so the kernel cannot evaluate
  it — `native_decide` (i.e. the compiled evaluator, axiom `Lean.ofReduceBool`)
  is genuinely required here. The main `Busybeaver` library stays free of it.
* The step-count convention: the library's `Busybeaver` counts steps to reach the
  *pre-halt* configuration, one less than the literature convention that counts
  the final halting transition. Each `bbN` theorem states the internal value and
  a `_literature` companion restates it in the standard convention.
-/

open TM TM.Table Pipeline

namespace BBTheorems

/-- Package the two facts a value theorem needs from one native evaluation:
no machine was left undecided, and the computed maximum is `v`.

The decider is a parameter (rather than fixed to `toTableDecider`) so that the
sizes that never need the hardcoded BB5 table can use `toTableDeciderCore` and
keep the table — and hence the sporadic-machine certificates, with their current
`sorry`/`native_decide` axioms — out of their constant closure. -/
abbrev ResultSpec (l s v : ℕ) (dec : (M : Machine l s) → HaltM M Unit) : Prop :=
  (compute l s dec).undec = ∅ ∧ (compute l s dec).val = v

/-- Turn a `ResultSpec` into the value theorem via `correct_complete`. -/
theorem ResultSpec.busybeaver {l s v : ℕ} {dec : (M : Machine l s) → HaltM M Unit}
    (hl : l ≠ 0) (h : ResultSpec l s v dec) : Busybeaver l s = v :=
  (Busybeaver.BBCompute.correct_complete hl h.1).trans h.2

end BBTheorems
