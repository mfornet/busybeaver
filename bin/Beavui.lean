import LCurses
import Busybeaver

open LCurses TM

def colors := #[Color.blue, Color.red, Color.green, Color.yellow, Color.magenta]

def main : List String → IO UInt32
| [fst] => do
  let Except.ok { l, s, M } := Parse.pmachine.run fst | throw <| IO.userError "Failed to parse"
  let root ← initscr
  start_colors

  let pairs ← colors.mapM (λ fg ↦ new_pair (fg:=fg))

  let Mrep := toString <| repr M
  for state in List.finRange (l + 1) do
    for sym in List.finRange (s + 1) do
      match M state sym with
      | .halt => root.addstr "---"
      | .next sym dir lab => do
        root.addstr s!"{toString sym}{repr dir}"
        root.addch (Char.ofNat <| 'A'.toNat + lab) {pair:=pairs[↑lab % pairs.size]'(by {
          apply Nat.mod_lt
          sorry
        })}
    if state < l then
      root.addch '_'

  let _ ← root.getch

  endwin
  return 0
| _ => do return 1
