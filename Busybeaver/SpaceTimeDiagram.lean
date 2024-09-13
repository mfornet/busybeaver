import Busybeaver.Basic
import Lean.Data.AssocList
import Busybeaver.Parse

/-!
Generates a time diagram for a TM as an SVG.
-/

namespace SVG

inductive Size where
| pixels : ℤ → Size

instance: OfNat Size n where
  ofNat := .pixels n

instance: Coe ℤ Size where
  coe := .pixels

instance: Coe ℕ Size where
  coe n := .pixels ↑n

instance: ToString Size where
  toString := λ
  | .pixels n => toString n

inductive Kind where
| rect (width height: Size) (x y: Size)

instance: ToString Kind where
  toString := λ
  | .rect width height x y => s!"rect width=\"{width}\" height=\"{height}\" x=\"{x}\" y=\"{y}\""

inductive Color where
| rgb : UInt8 → UInt8 → UInt8 → Color
| hsl : Fin 361 → Fin 101 → Fin 101 → Color

instance: ToString Color where
  toString := λ
  | .rgb r g b => s!"rgb({r} {g} {b})"
  | .hsl h s l => s!"hsl({h}deg {s}% {l}%)"

structure Elem where
  kind : Kind
  fill? : Option Color
  modifiers : List (String × String)

instance: ToString Elem where
  toString e :=
  "<" ++ toString e.kind ++
    (if let .some c := e.fill? then
      " fill=\""  ++ toString c ++ "\""
    else
      "")
  ++ e.modifiers.foldl (λ acc ⟨k, v⟩ ↦ s!"{acc} {k}=\"{v}\"") "" ++ "/>"

structure Doc where
  width : Size
  height : Size
  elems: List Elem

instance: ToString Doc where
  toString doc :=
    s!"<svg width=\"{doc.width}\" height=\"{doc.height}\" xmlns=\"http://www.w3.org/2000/svg\">{String.join (doc.elems.map toString)}</svg>"

def Doc.writeTo (doc: Doc) (stream: IO.FS.Stream) := stream.putStr (toString doc)


declare_syntax_cat svg
declare_syntax_cat svg_elem
declare_syntax_cat svg_color
declare_syntax_cat svg_attrib

syntax str : svg_attrib
syntax num : svg_attrib
syntax "{{" term "}}" : svg_attrib

syntax "rgb(" term "," term "," term ")" : svg_color
syntax "hsl(" term "," term "," term ")" : svg_color
syntax "{{" term "}}" : svg_color

syntax "<svg width=" svg_attrib " height=" svg_attrib ">" svg_elem* "</svg>" : term
syntax "<rect width=" svg_attrib " height=" svg_attrib " x=" svg_attrib " y=" svg_attrib (" fill=" svg_color)? "/>" : svg_elem

syntax "se[[" svg_elem "]]" : term
syntax "sa[[" svg_attrib "]]" : term
syntax "sc[[" svg_color "]]" : term

macro_rules
| `(term| <svg width=$w height=$h>$[$el:svg_elem]*</svg>) => `(term| Doc.mk sa[[$w]] sa[[$h]] [$[ se[[$el]] ],*])

| `(term| se[[<rect width=$w height=$h x=$x y=$y/>]]) =>
    `(term| Elem.mk (Kind.rect sa[[$w]] sa[[$h]] sa[[$x]] sa[[$y]]) .none [])
| `(term| se[[<rect width=$w height=$h x=$x y=$y fill=$c/>]]) =>
    `(term| Elem.mk (Kind.rect sa[[$w]] sa[[$h]] sa[[$x]] sa[[$y]]) (.some sc[[$c]]) [])

| `(term| sc[[rgb($r,$g,$b)]]) => `(term| Color.rgb $r $g $b)
| `(term| sc[[hsl($h,$s,$l)]]) => `(term| Color.hsl $h $s $l)
| `(term| sc[[{{$v}}]]) => pure v

| `(term| sa[[$v:num]]) => `(term| $v)
| `(term| sa[[$v:str]]) => `(term| $v)
| `(term| sa[[{{$v}}]]) => pure v
end SVG

namespace TM.SpaceTime

private def sColor (sym: Symbol s): SVG.Color :=
  let val: ℕ := (sym * 255) / s
  let val: UInt8 := UInt8.ofNat val
  SVG.Color.rgb val val val

private def lColor (label: Label l): SVG.Color :=
  let val: ℕ := (label * 300) / l
  let val: Fin 361 := val
  SVG.Color.hsl val 82 43

def size := 10

private def symToRec (sym: Symbol s) (offset: ℤ) (depth: ℕ): SVG.Elem :=
  se[[
    <rect width={{size}} height={{size}} x={{↑(offset * size)}} y={{↑(depth * size)}} fill={{sColor sym}}/>
  ]]

abbrev Line (l s) := Config l s × Turing.Dir

def getLines (depth: ℕ) (cfg: Config l s) (M: Machine l s): List <| Line l s := match depth with
| 0 => []
| n + 1 => match hM: M cfg.state cfg.tape.head with
  | .halt => []
  | .next _ dir _ =>
    let ncfg : Config l s := M.step cfg |>.get (by simp [Option.isSome, Machine.step, hM])
    (cfg, dir) :: getLines n ncfg M

def getBounds (left cur right: ℤ): List (Line l s) → ℤ × ℤ
| [] => (left, right)
| (_, dir) :: rest => match dir with
  | .left => getBounds (min (cur - 1) left) (cur - 1) right rest
  | .right => getBounds left (cur + 1) (max (cur + 1) right) rest

lemma getBounds.leftNeg {L: List <| Line l s}: (getBounds le cu ri L).1 ≤ le :=
by induction le, cu, ri, L using getBounds.induct with simp [getBounds]
| case2 left cur right _ rest IH => {
  simp at IH
  exact IH.2
}
| case3 left cur right _ rest IH => {
  simp at IH
  exact IH
}

lemma getBounds.rightPos {L: List <| Line l s}: ri ≤ (getBounds le cu ri L).2 :=
by induction le, cu, ri, L using getBounds.induct with simp [getBounds]
| case2 left cur right _ rest IH => {
  simp at IH
  exact IH
}
| case3 left cur right _ rest IH => {
  simp at IH
  exact IH.2
}

/--
Turns the given ListBlank into a list of length target
-/
unsafe def unquotAndPad (target: ℕ) (hT: Turing.ListBlank (Symbol s)): List (Symbol s) :=
  let unq := Quot.unquot hT
  unq ++ List.replicate (target - unq.length) default

unsafe def configToRects (offset: ℤ) (leftmax rightmax: ℕ) (depth: ℕ) (cfg: Config l s): List SVG.Elem :=

  /-
  Tricky: depdending on `offset` we need to padd correctly on left and right.

   o
  XXX|XXX -> lp = l + o, lr = r - o
  l     r

       o
  XXX|XXX -> lp = l + o, lr = r - o
  l     r
  -/
  let leftpadded : List (Symbol s) := unquotAndPad (leftmax + offset).toNat cfg.tape.left
  let rightpadded := unquotAndPad (rightmax - offset).toNat cfg.tape.right

  let left: List SVG.Elem := leftpadded.reverse |>.enum |>.map
    λ ⟨i, sym⟩ ↦ symToRec sym i depth

  let right := rightpadded |>.enum |>.map
    λ ⟨i, sym⟩ ↦ symToRec sym (leftpadded.length + i + 1) depth

  symToRec cfg.tape.head leftpadded.length depth ::
  se[[
    <rect width={{↑(size * 3 / 5)}} height={{↑(size * 3 / 5)}}
      x={{↑(leftpadded.length * size + size / 5)}} y={{↑(depth * size + size / 5)}}
      fill={{lColor cfg.state}}/>
  ]] :: left ++ right

private unsafe def toArray (leftmax rightmax: ℕ) (offset: ℤ): List (ℕ × Line l s) → List SVG.Elem
| [] => []
| (depth, cfg, dir) :: rest =>
    let noff := offset + match dir with
      | .left => -1
      | .right => 1
  configToRects offset leftmax rightmax depth cfg ++ toArray leftmax rightmax noff rest

unsafe def generate (depth: ℕ) (M: Machine l s): SVG.Doc :=
  let lines := getLines depth default M
  let (leftmax, rightmax) := getBounds 0 0 0 lines
  {
    width := ↑(size * (leftmax.natAbs + rightmax.natAbs + 1)),
    height := ↑(size * lines.length),
    elems := toArray leftmax.natAbs rightmax.natAbs 0 lines.enum
  }
