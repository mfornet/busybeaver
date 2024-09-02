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

def psym (s): Parsec (Symbol s) := attempt do
  let d ← digit
  return d.toString.toNat!

def plab (l): Parsec (Label l) := attempt do
  let d ← asciiLetter
  return d.toNat - Char.toNat 'A'

def pstmt (l s): Parsec (Stmt l s) := attempt do
  if (← peek!) == '-' then
    skip ; skip ; skip
    return .halt
  else
    let sym ← psym s
    let dir ← pdir
    let lab ← plab l
    return .next sym dir lab
