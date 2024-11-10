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

  while true do
    -- Get width and height
    let height := root.getmaxy.toNat
    let width := root.getmaxx.toNat

    match (← root.getch) with
    | 'j' => off := off + 1
    | 'k' => off := off - 1
    | 'g' => off := 0
    | 'd' => off := off + (height / 2)
    | 'u' => off := off - (height / 2)
    | _ => break

    displayIn root pairs width 0 height <| cfgs.get? off

    root.refresh

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
    let { left, head, right } := cfg.tape
    let midpoint := width / 2
    for i in List.range width do
      let cell : Int := Int.ofNat i - midpoint
      win.move (UInt32.ofNat cur) (UInt32.ofNat i)
      if cell == off then
        -- Print head
        win.insch (getChar head true) {pair:=head_pair}
      else if cell < off then
        let sym := left.nth (cell - off).natAbs
        win.insch <| getChar sym
      else
        -- Print right
        let sym := right.nth (cell - off).toNat
        win.insch <| getChar sym

  displayIn {l s: ℕ} {M: Machine l s} (win: Window) (pairs: Array Pair) (width cur height: ℕ) (configs: Configs M): IO Unit :=
    match (height - cur), configs with
    | 0, _ | _, .nil => pure ()
    | n + 1, .cons cfg off nxt => do
      -- Display one line
      drawLine pairs win width cur cfg off
      displayIn win pairs width (cur + 1) height nxt.get
