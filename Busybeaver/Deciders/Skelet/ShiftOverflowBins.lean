import Busybeaver.Deciders.Sweep
import Busybeaver.Deciders.Skelet.FixedBin
import Busybeaver.Deciders.Skelet.ShiftOverflow

/-!
# Tape-side encodings for the shift-overflow machines

A Lean port of `Coq-BB5/BusyCoq/ShiftOverflowBins.v`: the left/right tape-side
representations `L`/`R`/`K`/`Lk` of the binary counters used by the BB(5)
holdouts SM9–12 (Skelet #26/#33/#34/#35).  This is the third shared layer (after
`FixedBin` and `ShiftOverflow`) and the bridge from the abstract counter values
to the concrete tape (`Turing.ListBlank`).

Coq's `side` (a `Stream`) is Lean's `Turing.ListBlank (Symbol 1)`, head-nearest
first; `const 0` is `∅`.  The block-prepend operators `_ <* _` / `_ *> _` become
explicit `ListBlank.cons` chains, and the Coq reversed-list literal `<[…]` is
folded into that order.  The left counter ranges over `Num` (Coq `N`), the right
counter over `PosNum` (Coq `positive`).
-/

namespace Deciders.Skelet.ShiftOverflowBins

open Turing
open Deciders.Skelet.FixedBin (Bin)

/-- A one-sided tape (Coq `side`). -/
abbrev side := ListBlank (Symbol 1)

local notation "𝟙" => (1 : Symbol 1)
local notation "𝟘" => (0 : Symbol 1)

@[simp] lemma cons0_empty : ListBlank.cons (0 : Symbol 1) ∅ = ∅ := ListBlank.cons_default_empty

/-- Left counter body on a `positive` (Coq `L'`). -/
def L' : PosNum → side
  | .one => .cons 𝟘 (.cons 𝟘 (.cons 𝟘 (.cons 𝟙 ∅)))
  | .bit0 n => .cons 𝟘 (.cons 𝟘 (.cons 𝟘 (.cons 𝟘 (L' n))))
  | .bit1 n => .cons 𝟘 (.cons 𝟘 (.cons 𝟘 (.cons 𝟙 (L' n))))

/-- Left counter (Coq `L`). -/
def L : Num → side
  | .zero => ∅
  | .pos n => L' n

/-- Right counter (Coq `R`): each bit is a `[1;0]`/`[1;1]` pair, LSB nearest the head. -/
def R : PosNum → side
  | .one => .cons 𝟙 (.cons 𝟙 ∅)
  | .bit0 n => .cons 𝟙 (.cons 𝟘 (R n))
  | .bit1 n => .cons 𝟙 (.cons 𝟙 (R n))

/-- Left counter body in `K` form (Coq `K'`): `L'` with its head `0` dropped. -/
def K' : PosNum → side
  | .one => .cons 𝟘 (.cons 𝟘 (.cons 𝟙 ∅))
  | .bit0 n => .cons 𝟘 (.cons 𝟘 (.cons 𝟘 (.cons 𝟘 (K' n))))
  | .bit1 n => .cons 𝟘 (.cons 𝟘 (.cons 𝟙 (.cons 𝟘 (K' n))))

/-- `K` counter (Coq `K`). -/
def K : Num → side
  | .zero => ∅
  | .pos n => K' n

/-- Fixed-width left block (Coq `Lk`), as a finite list prepended onto a side. -/
def Lk : ∀ {k : ℕ}, Bin k → List (Symbol 1)
  | _, .bb => []
  | _, .b0 n => 𝟘 :: 𝟘 :: 𝟘 :: 𝟘 :: Lk n
  | _, .b1 n => 𝟘 :: 𝟘 :: 𝟘 :: 𝟙 :: Lk n

/-- `L'` is `K'` with a `0` pushed on (Coq `L_as_K`, positive part). -/
theorem L'_as_K' : ∀ n, L' n = ListBlank.cons 𝟘 (K' n)
  | .one => rfl
  | .bit0 n => by simp only [L', K', L'_as_K' n]
  | .bit1 n => by simp only [L', K', L'_as_K' n]

/-- `L n = K n` with a `0` pushed on (Coq `L_as_K`). -/
theorem L_as_K : ∀ n, L n = ListBlank.cons 𝟘 (K n)
  | .zero => by simp [L, K]
  | .pos n => L'_as_K' n

end Deciders.Skelet.ShiftOverflowBins
