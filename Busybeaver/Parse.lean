/-
Parsing machines in standard format for convenience.
-/
import Busybeaver.Basic
import Std.Internal.Parsec.String

open Lean Std.Internal.Parsec String

namespace TM.Parse

def pdir: Parser Turing.Dir := attempt do
  let c ← any
  match c with
  | 'L' => return .left
  | 'R' => return .right
  | _ => fail s!"Expected one of L/R"

def psym: Parser ℕ := attempt do
  let d ← digit
  return d.toString.toNat!

def plab: Parser ℕ := attempt do
  let d ← asciiLetter
  return d.toNat - Char.toNat 'A'

abbrev TStmt := Option (ℕ × Turing.Dir × ℕ)

def pstmt: Parser TStmt := attempt do
  if (← peek!) == '-' then
    skip ; skip ; skip
    return .none
  else
    let sym ← psym
    let dir ← pdir
    let lab ← plab
    return .some (sym, dir, lab)

def pStateCode: Parser <| Array TStmt := many1 pstmt

def sep1 (el: Parser α) (sep: Parser β): Parser (Array α) :=
  do manyCore (attempt do let _ ← sep; el) #[← el]

structure MParseRes where
  l : ℕ
  s : ℕ
  M : Machine l s
deriving Inhabited

def pmachine: Parser MParseRes := attempt do
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
        | .some (tsym, tdir, tlab) =>
            .next
              (⟨tsym % (s + 1), Nat.mod_lt _ (Nat.zero_lt_succ s)⟩ : Symbol s)
              tdir
              (⟨tlab % (l + 1), Nat.mod_lt _ (Nat.zero_lt_succ l)⟩ : Label l)

    have hmc: mcode.size = code.size := by simp [mcode]
    have hmsc : ∀ i: Fin mcode.size, (mcode[i.val]'i.prop).size = asize := by {
      intro i
      have hi : i.val < code.size := by simpa [hmc] using i.prop
      simpa [mcode] using (hca ⟨i.val, hi⟩)
    }

    let fcode : Array <| Stmt l s := mcode.flatten

    return {
      l := l,
      s := s,
      M := ⟨fcode, by {
        simp [fcode]
        conv =>
          rhs
          lhs
          simp [l, Nat.sub_one_add_one hcs]
        conv =>
          rhs
          rhs
          simp [s, Nat.sub_one_add_one has]
        rw [← Array.sum_eq_sum_toList]
        rw [Array.toList_map]
        have hconst : ∀ a ∈ List.map Array.size mcode.toList, a = asize := by
          intro a ha
          rw [List.mem_iff_get] at ha
          rcases ha with ⟨n, hn⟩
          have hna : n.1 < mcode.size := by simpa using n.2
          have hget : (List.map Array.size mcode.toList).get n = (mcode[n.1]'hna).size := by
            rw [List.get_eq_getElem]
            rw [List.getElem_map]
            rw [Array.getElem_toList]
          rw [hget] at hn
          exact hn.symm.trans (hmsc ⟨n.1, hna⟩)
        calc (List.map Array.size mcode.toList).sum
          _ = (List.map Array.size mcode.toList).length • asize := by
            exact List.sum_eq_card_nsmul (List.map Array.size mcode.toList) asize hconst
          _ = (List.map Array.size mcode.toList).length * asize := by rw [Nat.nsmul_eq_mul]
          _ = code.size * asize := by simpa [hmc]
      }⟩
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
  let valE : Expr := toExpr M.vals
  let lE : Expr := mkNatLit l
  let sE : Expr := mkNatLit s
  let stx: Syntax ← `(
    fun (lab: Label $(← exprToSyntax lE)) (sym: Symbol $(← exprToSyntax sE)) ↦
      ($(← exprToSyntax valE):term)[lab]![sym]!
  )
  elabTerm stx <| .some <| mkApp2 (.const ``Machine []) lE sE
end MachNotation
