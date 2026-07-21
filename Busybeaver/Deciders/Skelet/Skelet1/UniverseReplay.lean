import Busybeaver.Deciders.Skelet.Skelet1.Helpers
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Cases

/-!
# Skelet #1 — universe cycle and non-halting

This file continues the Lean port of `Coq-BB5/BusyCoq/Skelet1.v`.  It sits on top
of the accelerated `step` layer (`Skelet1Stride.lean`) and develops the
"universe cycle" self-similarity theorem `uni_cycle`, the `try_uni_cycle` /
`fullstep` wrappers, the `infinite_cycle` / `cycle_nonhalt` cyclic-family
argument, and finally the reflective reachability computation `doit` that
assembles `¬ M.halts init`.

Where the Coq development uses `positive`/`N` we use `ℕ`.
-/

namespace Deciders.Skelet.Skelet1

open Turing TM.Table

/-! ## The distinguished blocks `F`, `G`, `J`, `K` and constants. -/

/-- Coq `F`. -/
def F : Ltape := [Lsym.xs 10344, Lsym.D, Lsym.xs 7640, Lsym.C2]

/-- Coq `G`. -/
def G : Rtape :=
  [Rsym.xs 300, Rsym.D, Rsym.xs 30826, Rsym.D, Rsym.xs 72142, Rsym.D,
   Rsym.xs 3076, Rsym.D, Rsym.xs 1538, Rsym.D]

/-- Coq `J`. -/
def J : Ltape :=
  [Lsym.D, Lsym.C2, Lsym.xs 95, Lsym.C0,
   Lsym.xs 7713, Lsym.D, Lsym.D, Lsym.xs 1866, Lsym.C1,
   Lsym.xs 13231, Lsym.D, Lsym.xs 6197, Lsym.C3,
   Lsym.xs 11066, Lsym.D, Lsym.xs 7279, Lsym.C0,
   Lsym.xs 10524, Lsym.D, Lsym.xs 7550, Lsym.C2,
   Lsym.xs 10389, Lsym.D, Lsym.xs 7618, Lsym.C1,
   Lsym.xs 10355, Lsym.D, Lsym.xs 7635, Lsym.C3,
   Lsym.xs 10347, Lsym.D, Lsym.xs 7639, Lsym.C3,
   Lsym.xs 10345, Lsym.D, Lsym.xs 7640, Lsym.C1]

/-- Coq `K`. -/
def K : Rtape :=
  [Rsym.xs 7639, Rsym.D, Rsym.xs 10347, Rsym.Cr,
   Rsym.xs 7635, Rsym.D, Rsym.xs 10355, Rsym.Cr,
   Rsym.xs 7619, Rsym.D, Rsym.xs 10387, Rsym.Cr,
   Rsym.xs 7555, Rsym.D, Rsym.xs 10515, Rsym.Cr,
   Rsym.xs 7299, Rsym.D, Rsym.xs 11027, Rsym.Cr,
   Rsym.xs 6275, Rsym.D, Rsym.xs 13075, Rsym.Cr,
   Rsym.xs 2179, Rsym.D, Rsym.D, Rsym.xs 7088, Rsym.Cr,
   Rsym.xs 1, Rsym.Cr, Rsym.xs 3849, Rsym.P]

/-- Coq `uni_P`. -/
def uni_P : ℕ := 53946

/-- Coq `uni_T = 4 * uni_P - 5`. -/
def uni_T : ℕ := 4 * uni_P - 5

/-! ## The universe-cycle theorem (Coq `uni_cycle`). -/

set_option maxRecDepth 10000000
set_option maxHeartbeats 0

/-- Coq `uni_cycle`.  A single universe period: given a stride of length
`uni_T` on the right tape, the configuration advances by consuming `uni_P` from
the `l_xs` counter and appending one `F` on the left and one `G` on the right. --/

theorem uni_cycle (l : Ltape) (r r' : Rtape) (xs : ℕ)
    (h : stride 0 uni_T r = some r') :
    lift (.right, Lsym.D :: Lsym.C1 :: Lsym.xs (xs + (uni_P + 1)) :: J ++ l, r) -[M]->*
      lift (.right, Lsym.D :: Lsym.C1 :: Lsym.xs (xs + 1) :: J ++ F ++ l, G ++ r') := by
  norm_num [uni_T, uni_P] at h ⊢
  repeat
    first
    | refine consume_stride_segment_cps
        (hreduce := by norm_num [strideK, rxs]) (h := by assumption) (hm := by omega) ?_
      intro u hu
    | refine (simple_step_spec _ _ (by rfl)).trans ?_
    | refine (stride_correct_0 _ _ _ (by assumption)).trans ?_
    | exact Machine.EvStep.refl

end Deciders.Skelet.Skelet1
