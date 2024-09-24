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
  do manyCore (attempt do let _ ← sep; el) #[← el]

structure MParseRes where
  l : ℕ
  s : ℕ
  M : Machine l s
deriving Inhabited

def pmachine: Parsec MParseRes := attempt do
  let code ← sep1 pStateCode (pchar '_')
  if hcs: code.size = 0 then
    fail "Empty code"
  else

  let l := code.size - 1
  let asize := (code[0]'(Nat.zero_lt_of_ne_zero hcs)).size

  if has: asize = 0 then
    fail "Empty code"
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

section MachNotation

open Lean Meta Elab Term

instance: ToExpr (Label l) := inferInstance
instance: ToExpr (Symbol l) := inferInstance
instance: ToExpr Turing.Dir where
  toExpr D := Expr.const (match D with
  | Turing.Dir.right => ``Turing.Dir.right
  | Turing.Dir.left => ``Turing.Dir.left) []

  toTypeExpr := Expr.const ``Turing.Dir []

instance [inst: ToExpr α]: ToExpr (List α) where
  toExpr := λ
    | .nil => Expr.const ``List.nil []
    | .cons head tail => mkApp2 (Expr.const ``List.cons []) (toExpr head) (toExpr tail)
  toTypeExpr := mkApp (Expr.const ``List []) inst.toTypeExpr

instance: ToExpr (Stmt l s) where
  toExpr := λ
    | .halt => mkApp2 (Expr.const ``Stmt.halt []) (mkNatLit l) (mkNatLit s)
    | .next sym dir lab => mkApp5 (Expr.const ``Stmt.next []) (mkNatLit l) (mkNatLit s) (toExpr sym) (toExpr dir) (toExpr lab)
  toTypeExpr := mkApp2 (Expr.const ``Stmt []) (mkNatLit l) (mkNatLit s)

elab "mach[" content:str "]" : term => do
  let ⟨l, s, M⟩ := pmachine.run content.getString |>.toOption.get!
  let values : List <| List <| Stmt l s :=
    Fin.list (l + 1) |>.map λ L ↦ Fin.list (s + 1) |>.map λ S ↦ M L S
  let valE : Expr := toExpr values
  let lE : Expr := mkNatLit l
  let sE : Expr := mkNatLit s
  let stx: Syntax ← `(
    fun (lab: Label $(← exprToSyntax lE)) (sym: Symbol $(← exprToSyntax sE)) ↦
      ($(← exprToSyntax valE):term)[lab]![sym]!
  )
  elabTerm stx <| .some <| mkApp2 (.const ``Machine []) lE sE
end MachNotation
