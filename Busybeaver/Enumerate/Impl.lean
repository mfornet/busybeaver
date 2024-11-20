/-
Implementation of the enumeration algorithm.

This hides the implementation details of the algorithm behind a `csimp`.
-/
import Busybeaver.Enumerate.Alg
import Batteries.Lean.System.IO

namespace TM.Busybeaver

instance: Monad Task where
  pure := Task.pure
  bind := Task.bind

def PARA_DEPTH: ℕ := 3

lemma BBResult.join.rightcomm: RightCommutative (BBResult.join (l:=l) (s:=s)) where
  right_comm A B C := by {
    simp [BBResult.join]
    constructor
    · exact Max.right_comm A.val B.val C.val
    · exact add_right_comm A.undec B.undec C.undec
  }

def waitMultiset (S: Multiset (Task α)): Task (Multiset α) :=
  Quotient.liftOn S (λ L ↦ List.waitAll L |>.map Quotient.mk'') (by {
    simp
    intro A B hAB
    simp [Task.map]
    induction hAB using List.Perm.recOn with
    | nil => {
      simp [List.waitAll]
    }
    | @cons X L₁ L₂ hL IH => {
      simp [List.waitAll, Task.bind, Task.map]
      congr 1
      simp
      injection IH
      rename_i heq
      exact Multiset.coe_eq_coe.mp heq
    }
    | @trans A B C hAB hBC IHA IHB => {
      injection IHA
      injection IHB
      congr 1
      simp_all only
    }
    | @swap A B L => {
      simp [List.waitAll, Task.bind, Task.map]
      congr 1
      simp
      exact List.Perm.swap A.get B.get L.waitAll.get
    }
  })

@[simp]
lemma waitMultiset.empty: (waitMultiset (∅: Multiset <| Task α)).get = 0 := by
  rfl

@[simp]
lemma waitMultiset.get (f: α → Task β) (S: Multiset α): (waitMultiset <| S.map f).get = S.map (λ a ↦ f a |>.get) :=
by {
  induction S using Quotient.inductionOn
  rename_i L
  simp [waitMultiset, Task.map]
  induction L with
  | nil => {
    simp [List.waitAll]
  }
  | cons head tail IH => {
    simp [List.waitAll, Task.bind, Task.map, IH]
  }
}

set_option linter.unusedVariables false in
def BBComputeP (decider: (M': Machine l s) → HaltM M' Unit) (M: Machine l s): BBResult l s :=
  let rec loop (M: Machine l s): Task (BBResult l s) :=
    match decider M with
    | .loops_prf _ => .pure { val := 0, undec := {} } -- If this one loops, then the descendents also loop
    | .halts_prf n C hC =>
      if hMn: M.n_halting_trans <= 1 then
        .pure { val := n, undec := {}}
      else
      let next := (next_machines M C.state C.tape.head).val.attach
      if hMn': M.n_halting_trans > PARA_DEPTH then do
        let unquoted ← waitMultiset <| next.map (λ M' ↦ loop M'.val)
        return unquoted.foldl BBResult.join { val := n, undec := {} }
      else
        Task.spawn <| λ _ ↦
          next.map (λ M' ↦ BBCompute decider M'.val) |>.foldl BBResult.join { val := n, undec := {} }
    | .unknown _ => .pure { val := 0, undec := {M} } -- This machine is undecided, no need to go further
  termination_by M.n_halting_trans
  decreasing_by {
    obtain ⟨M', hM'⟩ := M'
    obtain ⟨hCl, _⟩ := hC
    simp [Machine.LastState] at hCl
    have hMM' := next_machines.halttrans_le hCl M' hM'
    simp_wf
    rw [hMM']
    simp at hMn
    exact Nat.sub_one_lt_of_lt hMn
  }
  loop M |>.get

@[csimp]
lemma BBCompute.impl: @BBCompute = @BBComputeP := by {
  funext l s decider M
  induction M using BBCompute.induct decider with
  | case1 M' hM' h | case4 M' hM' h => {
    simp only [BBCompute, h]
    simp only [BBComputeP, BBComputeP.loop, h]
  }
  | case3 M' n C hC h hntrans => {
    unfold BBCompute
    simp [h, hntrans]
    unfold BBComputeP
    unfold BBComputeP.loop
    simp at hntrans
    simp [h, hntrans]
  }
  | case2 M' n C hC h hntrans IH => {
    unfold BBCompute
    simp [h, hntrans]
    unfold BBComputeP
    unfold BBComputeP.loop
    simp at hntrans
    simp [h, hntrans]

    split
    · absurd hntrans
      simp
      trivial
    split <;> {
      simp [instMonadTask, Task.bind, Finset.fold, Multiset.fold]
      rw [Multiset.foldr_swap]
      congr 1
      · funext A B
        simp [BBResult.join]
        constructor
        · exact Nat.max_comm B.val A.val
        · exact AddCommMagma.add_comm B.undec A.undec

      try {
        congr 1
        funext M₀
        exact IH M₀
      }
    }
  }
}
