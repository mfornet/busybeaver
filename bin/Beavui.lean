import LCurses
import Busybeaver

open LCurses TM

def ntoColor (n: ℕ): Color :=
  #[Color.blue, Color.red, Color.green, Color.yellow, Color.magenta][n % 5]'(by {
    simp
    apply Nat.mod_lt
    decide
  })

def main : List String → IO UInt32
| [fst] => do
  let Except.ok { l, s, M } := Parse.pmachine.run fst | throw <| IO.userError "Failed to parse"
  let root ← initscr

  let Mrep := toString <| repr M
  for state in List.finRange (l + 1) do
    for sym in List.finRange (s + 1) do
      match M state sym with
      | .halt => root.addstr "---"
      | .next sym dir lab => do
        

  let _ ← root.getch

  endwin
  return 0
| _ => do return 1
