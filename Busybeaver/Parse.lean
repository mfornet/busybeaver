/-
Parsing machines in standard format for convenience.
-/
import Busybeaver.Basic
import Lean.Data.Parsec

open Lean Parsec

namespace TM.Parse

def pdir: Parsec Turing.Dir := attempt do
  let c ← anyChar
  match c with
  | 'L' => return .left
  | 'R' => return .right
  | _ => fail s!"Expected one of L/R"

def psym: Parsec ℕ := attempt do
  let d ← digit
  return d.toString.toNat!

def plab: Parsec ℕ := attempt do
  let d ← asciiLetter
  return d.toNat - Char.toNat 'A'

abbrev TStmt := Option (ℕ × Turing.Dir × ℕ)

def pstmt: Parsec TStmt := attempt do
  if (← peek!) == '-' then
    skip ; skip ; skip
    return .none
  else
    let sym ← psym
    let dir ← pdir
    let lab ← plab
    return .some (sym, dir, lab)

def pStateCode: Parsec <| Array TStmt := many1 pstmt

def sep1 (el: Parsec α) (sep: Parsec β): Parsec (Array α) :=
  do manyCore (do let _ ← sep; el) #[← el]

structure MParseRes where
  l : ℕ
  s : ℕ
  M : Machine l s
deriving Inhabited

def pmachine: Parsec MParseRes := attempt do
  let code ← sep1 pStateCode (pchar '_')
  if hcs: code.size = 0 then
    unreachable!
  else

  let l := code.size - 1
  let asize := (code[0]'(Nat.zero_lt_of_ne_zero hcs)).size

  if has: asize = 0 then
    unreachable!
  else

  if hca: ∀i: Fin code.size, (code[i.val]'(i.prop)).size = asize then
    let s := asize - 1

    let mut mcode: Array (Array (Stmt l s)) := code.map
      λ ic ↦ ic.map λ
        | .none => .halt
        | .some (tsym, tdir, tlab) => .next tsym tdir tlab

    have hmc: mcode.size = code.size := by simp [mcode]
    have hmsc : ∀ i: Fin mcode.size, (mcode[i.val]'i.prop).size = asize := by {
      intro ⟨i, hi⟩
      simp [mcode]
      rw [hmc] at hi
      exact hca ⟨i, hi⟩
    }

    return {
      l := l,
      s := s,
      M := λ ⟨lab, hlab⟩ ⟨sym, hsym⟩ ↦
        have hlab' : lab < mcode.size := by {
          rw [hmc]
          calc lab
            _ < l + 1 := hlab
            _ = code.size := by {
              simp [l]
              exact Nat.succ_pred_eq_of_ne_zero hcs
            }
        }
        let scode := mcode[lab]'hlab'
        scode[sym]'(by {
          simp [scode]
          calc sym
            _ < s + 1 := hsym
            _ = mcode[lab].size := by {
              simp [s]
              specialize hmsc ⟨lab, hlab'⟩
              simp at hmsc
              rw [hmsc]
              exact Nat.succ_pred_eq_of_ne_zero has
            }
        })
    }
  else
    fail s!"Not all states have the same number of statements"
