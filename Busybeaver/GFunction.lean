import Busybeaver.Basic
import Busybeaver.Reachability
import Busybeaver.Enumerate.Alg
import Busybeaver.Deciders.BoundExplore
import Busybeaver.Parse

/-!
Inspired by a discussion with Tristan Sterin on the bbchalenge discord.

The `G(n)` function is the least number of states such that there exist a TM halting in `k` for each
`k` < n.
-/

namespace TM.GFunction

open TM Machine Busybeaver

def runUpTo (n: ℕ) (M: Machine l s): Option { T: ℕ × Config l s // (default -[M]{T.1}-> T.2) ∧ M.LastState T.2 ∧ T.1 ≤ n } :=
  let rec loop (cur: ℕ) (left: ℕ) (C: Config l s) (hC: default -[M]{cur}-> C) (hcur: cur + left = n):
    Option { T: ℕ × Config l s // (default -[M]{T.1}-> T.2) ∧ M.LastState T.2 ∧ T.1 ≤ n} := match left with
    | 0 => if hC': M.LastState C then
      some <| ⟨(cur, C), by {
        rw [← hcur]
        simp
        trivial
      }⟩
      else 
        .none
    | left' + 1 => match hMC: M.step C with
      | .none => some ⟨(cur, C), by {
        rw [
          ← hcur
        ]

        rw [Machine.step.none] at hMC
        simp [Machine.LastState]
        trivial
      }⟩
      | .some B => loop (cur + 1) left' B (Multistep.tail hC hMC) (by {
        rw [← hcur, Nat.add_comm left', Nat.add_assoc]
      })
  loop 0 n default Multistep.refl (by simp)

def compute (n: ℕ) (M: Machine l s): Multiset (ℕ × Machine l s) :=
match runUpTo n M with
| none => {}
| some ⟨(n', C), prf⟩ =>
    have _: n' ≤ n := by {
      simp at prf
      exact prf.2.2
    }
    (n', M) ::ₘ
    if hMn: M.n_halting_trans > 1 then
      (next_machines M C.state C.tape.head).attach.val |>.map (λ M' ↦ compute n M'.val) |>.sum
    else
      {}
termination_by M.n_halting_trans
decreasing_by {
  simp_wf
  obtain ⟨M', hM'⟩ := M'
  simp at prf
  obtain ⟨_, hCl, _⟩ := prf
  simp [Machine.LastState] at hCl
  have hMM' := next_machines.halttrans_le hCl M' hM'
  simp_wf
  rw [hMM']
  exact Nat.sub_one_lt_of_lt hMn
}

unsafe def get_max (n: ℕ) (M: Machine l s): (ℕ × Machine l s) :=
  let unquot := Quot.unquot <| compute n M
  unquot.foldl (λ (n, M) (nA, MA) ↦ if n > nA then (n, M) else (nA, MA)) (0, default)
