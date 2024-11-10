import LCurses
import Busybeaver

open LCurses TM

--- A Lazy datastructure to 
inductive Configs (M: Machine l s) where
| nil
| cons : Config l s → (offset: Int) → Thunk (Configs M) → Configs M

instance: Inhabited <| Configs M := ⟨.nil⟩

partial def Configs.init (M: Machine l s) (cfg: Config l s := default) (offset: Int := 0): Configs M :=
  Configs.cons cfg offset <| Thunk.mk <| λ _ ↦ match hMs: M.step cfg with
    | .none => Configs.nil
    | .some c₂ => Configs.init M c₂ <| match hM: M cfg.state cfg.tape.head with
      | .next _ .left _ => offset - 1
      | .next _ .right _ => offset + 1
      | .halt => False.elim (by {
        obtain ⟨sym, dir, hM', _⟩ := Machine.step.some_rev hMs
        rw [hM] at hM'
        cases hM'
      })

def Configs.get? {M: Machine l s} : Configs M → ℕ → Configs M
| nil, _ => .nil
| C, 0 => C
| cons _ _ nxt, n + 1 => nxt.get.get? n

structure ConfigsResult (M: Machine l s) where
  cfg : Config l s
  offset : Int
  steps : ℕ

def colors := #[Color.blue, Color.red, Color.green, Color.yellow, Color.magenta, Color.cyan]

def main : List String → IO UInt32
| [fst] => do
  let Except.ok { l, s, M } := Parse.pmachine.run fst | throw <| IO.userError "Failed to parse"
  let root ← initscr
  echo false
  raw true
  start_colors

  let pairs ← colors.mapM (λ fg ↦ new_pair (fg:=fg))
  let cfgs := Configs.init M

  let mut off := 0
  let mut xoff: Int := 0

  while true do
    -- Get width and height
    let height := root.getmaxy.toNat
    let width := root.getmaxx.toNat

    displayIn root pairs width 0 height xoff <| cfgs.get? off

    root.refresh

    match (← root.getch) with
    -- Up / down
    | 'j' => off := off + 1
    | 'k' => off := off - 1
    | 'g' => off := 0
    | 'd' => off := off + (height / 2)
    | 'u' => off := off - (height / 2)

    -- Control left/right
    | 'l' => xoff := xoff - 1
    | 'h' => xoff := xoff + 1
    | 'c' => xoff := 0

    -- Exit and specials
    | 'q' => break
    | _ => pure ()

  endwin
  return 0
| _ => do return 1
where
  getChar {s: ℕ} (s: Symbol s) (head: Bool := false): Char :=
    let v := (toString s).get! 0
    if v == '0' && !head then
      ' '
    else
      v
  -- Assumes that we start drawing on cell 0
  drawLine {l s: ℕ} (pairs: Array Pair) (win: Window) (width cur: ℕ) (cfg: Config l s) (off: Int): IO Unit := do
    let head_pair := pairs[↑cfg.state % pairs.size]!
    let midpoint := width / 2
    for i in List.range width do
      let cell : Int := Int.ofNat i - (off + midpoint)
      let is_head := cell == 0
      win.move (UInt32.ofNat cur) (UInt32.ofNat i)
      win.insch (getChar (head:=is_head) <| cfg.tape.nth cell) <| if is_head then {pair:=head_pair} else {}

  displayIn {l s: ℕ} {M: Machine l s} (win: Window) (pairs: Array Pair) (width cur height: ℕ) (xoff: Int) (configs: Configs M): IO Unit :=
    match (height - cur), configs with
    | 0, _ | _, .nil => pure ()
    | n + 1, .cons cfg off nxt => do
      -- Display one line
      drawLine pairs win width cur cfg (off + xoff)
      displayIn win pairs width (cur + 1) height xoff nxt.get
