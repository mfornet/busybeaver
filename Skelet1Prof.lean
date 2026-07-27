import Busybeaver.Deciders.Skelet.Skelet1

/-! Untrusted profiling executable for the Skelet #1 `doit` run.
NOT part of the proof; used to size the chunked `decide` certificate.

Modes:
* `profile <fuel> <report>` — branch counts, tape sizes (default).
* `interuni <fromUni> <count>` — for `count` uni-intervals starting at the
  `fromUni`-th uni firing, print interval length (in fullsteps) and the
  left-head shape trace at each stride.
* `unilen` — plain-`step` length of one universal cycle (no uni shortcut).
* `intervals` — length (in fullsteps) of every inter-uni interval, plus the
  head-shape at each uni firing.
-/

open Deciders.Skelet.Skelet1

def symCountL : Lsym → Nat
  | .xs n | .Fs n | .Gs n | .Hs n => n
  | _ => 0

def symCountR : Rsym → Nat
  | .xs n | .Gs n => n
  | _ => 0

def maxCountOf (c : SConf) : Nat :=
  max (c.left.foldl (fun a s => max a (symCountL s)) 0)
      (c.right.foldl (fun a s => max a (symCountR s)) 0)

/-- Constructor-shape tag of a left symbol (ignore counts). -/
def tagL : Lsym → String
  | .xs _ => "x" | .D => "D" | .P => "P"
  | .C0 => "c0" | .C1 => "c1" | .C2 => "c2" | .C3 => "c3"
  | .F0 => "f0" | .F1 => "f1" | .F2 => "f2" | .F3 => "f3"
  | .G0 => "g0" | .G1 => "g1" | .G2 => "g2"
  | .Fs _ => "F" | .Gs _ => "G" | .Hs _ => "H"

def tagR : Rsym → String
  | .xs _ => "x" | .D => "D" | .C => "C" | .P => "P" | .Gs _ => "G"

def shapeOf (c : SConf) (k : Nat := 6) : String :=
  let d := match c.dir with | .left => "<" | .right => ">"
  let ls := String.intercalate "," ((c.left.take k).map tagL)
  let rs := String.intercalate "," ((c.right.take k).map tagR)
  s!"{d}[{ls}|{rs}]"

def profileMode (fuel report : Nat) : IO Unit := do
  let mut c := initial
  let mut nUni := 0; let mut nStride := 0
  let mut nSimpleL := 0; let mut nSimpleR := 0
  let mut maxL := 0; let mut maxR := 0; let mut maxCount := 0
  let mut done := false
  for i in [0:fuel] do
    if done then break
    if isCycling c then
      IO.println s!"CYCLING at fullstep {i}"
      done := true
      break
    if i % 4096 == 0 then
      maxL := max maxL c.left.length
      maxR := max maxR c.right.length
      maxCount := max maxCount (maxCountOf c)
    match tryUniCycle c with
    | some c' => nUni := nUni + 1; c := c'
    | none =>
      match tryStride c with
      | some c' => nStride := nStride + 1; c := c'
      | none =>
        match simpleStep c with
        | some c' =>
          if c.dir matches .left then nSimpleL := nSimpleL + 1 else nSimpleR := nSimpleR + 1
          c := c'
        | none => IO.println s!"STUCK at {i}"; done := true; break
    if (i+1) % report == 0 then
      IO.println s!"step {i+1}: uni={nUni} stride={nStride} sL={nSimpleL} sR={nSimpleR} maxL={maxL} maxR={maxR} maxCount={maxCount}"
      (← IO.getStdout).flush
  IO.println s!"END: uni={nUni} stride={nStride} sL={nSimpleL} sR={nSimpleR} maxL={maxL} maxR={maxR} maxCount={maxCount}"

/-- Lengths of all inter-uni intervals (fullsteps between consecutive uni
firings) + shape at each firing. -/
def intervalsMode (fuel : Nat) : IO Unit := do
  let mut c := initial
  let mut lastUniAt := 0
  let mut nUni := 0
  for i in [0:fuel] do
    if isCycling c then
      IO.println s!"CYCLING at {i}; lastUni at {lastUniAt}; tail={i - lastUniAt}"
      break
    match tryUniCycle c with
    | some c' =>
      let applied := match c with
        | ⟨.right, .D :: .C1 :: .xs xs :: l, r⟩ =>
          match stripPrefix Jconst l with
          | some _ => uniCycleCount xs r
          | none => 0
        | _ => 0
      IO.println s!"uni#{nUni} at {i} gap={i - lastUniAt} applied={applied}"
      nUni := nUni + 1
      lastUniAt := i
      c := c'
    | none =>
      match step c with
      | some c' => c := c'
      | none => IO.println s!"STUCK at {i}"; break
  IO.println s!"uni firings: {nUni}"

/-- Detailed shape trace of `count` inter-uni intervals starting after uni
firing number `fromUni`. -/
def interuniMode (fuel fromUni count : Nat) : IO Unit := do
  let mut c := initial
  let mut nUni := 0
  let mut tracing := false
  for i in [0:fuel] do
    if isCycling c then
      IO.println s!"CYCLING at {i}"
      break
    if nUni ≥ fromUni + count then break
    match tryUniCycle c with
    | some c' =>
      nUni := nUni + 1
      tracing := nUni ≥ fromUni && nUni < fromUni + count
      if tracing then
        IO.println s!"=== uni #{nUni} fired at step {i} (left len {c.left.length}, right len {c.right.length})"
      c := c'
    | none =>
      let kind := if (tryStride c).isSome then "STRIDE" else
        (if c.dir matches .left then "sl" else "sr")
      if tracing && kind == "STRIDE" then
        IO.println s!"  {i} {shapeOf c 8}"
      match step c with
      | some c' => c := c'
      | none => IO.println s!"STUCK at {i}"; break

/-- Plain-`step` length of one universal cycle: from the first uni-eligible
config, run WITHOUT the uni shortcut until the config is uni-eligible again
with exactly `uni_P` fewer `x`s.  Prints the step count. -/
def unilenMode (fuel : Nat) : IO Unit := do
  let mut c := initial
  -- find first uni-eligible config
  let mut i := 0
  while i < fuel do
    if (tryUniCycle c).isSome then break
    match step c with
    | some c' => c := c'; i := i + 1
    | none => IO.println "STUCK"; return
  IO.println s!"first uni-eligible at plain-step {i}: {shapeOf c 8}"
  let start := c
  let startXs := match start with
    | ⟨.right, _ :: _ :: .xs xs :: _, _⟩ => xs
    | _ => 0
  IO.println s!"start xs = {startXs}"
  -- now run plain steps until left head is D :: C1 :: xs (startXs - uni_P) :: J…
  let mut n := 0
  while n < fuel do
    match step c with
    | some c' =>
      c := c'
      n := n + 1
      match c with
      | ⟨.right, .D :: .C1 :: .xs xs :: l, _⟩ =>
        if xs == startXs - uni_P && (stripPrefix Jconst l).isSome then
          IO.println s!"one uni cycle completed in {n} plain steps"
          return
      | _ => pure ()
    | none => IO.println "STUCK"; return
  IO.println s!"no completion within {n} steps"

/-- Print every fullstep's kind+shape in a step range (uni shortcut active). -/
def traceMode (fuel from_ to_ : Nat) : IO Unit := do
  let mut c := initial
  for i in [0:fuel] do
    if i ≥ to_ then break
    if isCycling c then
      IO.println s!"CYCLING at {i}"
      break
    let tracing := i ≥ from_
    match tryUniCycle c with
    | some c' =>
      if tracing then IO.println s!"{i} UNI {shapeOf c 10} L={c.left.length} R={c.right.length}"
      c := c'
    | none =>
      match tryStride c with
      | some c' =>
        if tracing then IO.println s!"{i} STR {shapeOf c 10} L={c.left.length} R={c.right.length}"
        c := c'
      | none =>
        match simpleStep c with
        | some c' =>
          if tracing then IO.println s!"{i} sim {shapeOf c 10}"
          c := c'
        | none => IO.println s!"STUCK at {i}"; break

/-- Serialize a config compactly: one line per symbol, `tag count`. -/
def dumpConf (c : SConf) : String :=
  let l := c.left.map (fun s => match s with
    | .xs n => s!"x {n}" | .D => "D" | .P => "P"
    | .C0 => "c0" | .C1 => "c1" | .C2 => "c2" | .C3 => "c3"
    | .F0 => "f0" | .F1 => "f1" | .F2 => "f2" | .F3 => "f3"
    | .G0 => "g0" | .G1 => "g1" | .G2 => "g2"
    | .Fs n => s!"F {n}" | .Gs n => s!"G {n}" | .Hs n => s!"H {n}")
  let r := c.right.map (fun s => match s with
    | .xs n => s!"x {n}" | .D => "D" | .C => "C" | .P => "P" | .Gs n => s!"G {n}")
  let d := match c.dir with | .left => "L" | .right => "R"
  d ++ "\n" ++ String.intercalate "\n" l ++ "\n---\n" ++ String.intercalate "\n" r

/-- Dump the full config at a given step to a file. -/
def dumpMode (at_ : Nat) (path : String) : IO Unit := do
  let mut c := initial
  for _ in [0:at_] do
    match fullstep c with
    | some c' => c := c'
    | none => IO.println "STUCK"; return
  IO.FS.writeFile path (dumpConf c)
  IO.println s!"dumped step {at_}: L={c.left.length} R={c.right.length}"

/-- Constructor-and-small-count fingerprint of a step: head window shapes +
which branch fired.  Counts are abstracted except tiny ones (≤4), which are
structural (e.g. `x1` phase markers). -/
def fpL : Lsym → String
  | .xs n => if n ≤ 4 then s!"x{n}" else "x"
  | .D => "D" | .P => "P"
  | .C0 => "c0" | .C1 => "c1" | .C2 => "c2" | .C3 => "c3"
  | .F0 => "f0" | .F1 => "f1" | .F2 => "f2" | .F3 => "f3"
  | .G0 => "g0" | .G1 => "g1" | .G2 => "g2"
  | .Fs _ => "F" | .Gs _ => "G" | .Hs _ => "H"

def fpR : Rsym → String
  | .xs n => if n ≤ 4 then s!"x{n}" else "x"
  | .D => "D" | .C => "C" | .P => "P" | .Gs _ => "G"

def fingerprint (c : SConf) (branch : String) : String :=
  let d := match c.dir with | .left => "<" | .right => ">"
  let ls := String.intercalate "," ((c.left.take 4).map fpL)
  let rs := String.intercalate "," ((c.right.take 3).map fpR)
  s!"{branch}{d}[{ls}|{rs}]"

/-- Step-type alphabet and successor-branching statistics over the run. -/
def alphabetMode (fuel : Nat) : IO Unit := do
  let mut c := initial
  let mut counts : Std.HashMap String Nat := {}
  let mut succs : Std.HashMap String (Std.HashSet String) := {}
  let mut prev : String := ""
  let mut total := 0
  for i in [0:fuel] do
    if isCycling c then
      IO.println s!"CYCLING at {i}"
      break
    let branch := if (tryUniCycle c).isSome then "U"
      else if (tryStride c).isSome then "S" else "s"
    let fp := fingerprint c branch
    counts := counts.insert fp (counts.getD fp 0 + 1)
    if prev != "" then
      succs := succs.insert prev ((succs.getD prev {}).insert fp)
    prev := fp
    total := total + 1
    match fullstep c with
    | some c' => c := c'
    | none => IO.println s!"STUCK at {i}"; break
  IO.println s!"total steps: {total}, distinct step-types: {counts.size}"
  -- steps whose type has multiple observed successors = decision points
  let mut branchySteps := 0
  let mut branchyTypes := 0
  for (fp, cnt) in counts.toList do
    let ns := (succs.getD fp {}).size
    if ns > 1 then
      branchySteps := branchySteps + cnt
      branchyTypes := branchyTypes + 1
  IO.println s!"step-types with >1 successor: {branchyTypes}; steps at branchy types: {branchySteps}"
  let sorted := counts.toList.mergeSort (fun a b => a.2 ≥ b.2)
  for (fp, cnt) in sorted.take 60 do
    let ns := (succs.getD fp {}).size
    IO.println s!"{cnt}  succ={ns}  {fp}"

/-! ## Boundary encoder (mirrors `decodeConf` in Skelet1.lean) -/

partial def encVar (v : Nat) : List Nat :=
  if v < 8 then [v] else (8 + v % 8) :: encVar (v / 8)

def nibsToNat (l : List Nat) : Nat := l.foldr (fun nib acc => nib + 16 * acc) 0

def encLsym : Lsym → List Nat
  | .xs n => encVar 0 ++ encVar n
  | .D => encVar 1 | .P => encVar 2
  | .C0 => encVar 3 | .C1 => encVar 4 | .C2 => encVar 5 | .C3 => encVar 6
  | .F0 => encVar 7 | .F1 => encVar 8 | .F2 => encVar 9 | .F3 => encVar 10
  | .G0 => encVar 11 | .G1 => encVar 12 | .G2 => encVar 13
  | .Fs n => encVar 14 ++ encVar n
  | .Gs n => encVar 15 ++ encVar n
  | .Hs n => encVar 16 ++ encVar n

def encRsym : Rsym → List Nat
  | .xs n => encVar 0 ++ encVar n
  | .D => encVar 1 | .C => encVar 2 | .P => encVar 3
  | .Gs n => encVar 4 ++ encVar n

partial def chunks (k : Nat) : List α → List (List α)
  | [] => []
  | l => l.take k :: chunks k (l.drop k)

def encGroups (enc : α → List Nat) (syms : List α) : List Nat :=
  (chunks 48 syms).map fun g => nibsToNat (encVar g.length ++ g.flatMap enc)

def encodeConf (c : SConf) : Nat × List Nat × List Nat :=
  let d := match c.dir with | .left => 0 | .right => 1
  (d, encGroups encLsym c.left, encGroups encRsym c.right)

def natListLit (l : List Nat) : String :=
  "[" ++ String.intercalate ",\n  " (l.map toString) ++ "]"

def hexDigit : Nat → Char
  | 0 => '0' | 1 => '1' | 2 => '2' | 3 => '3'
  | 4 => '4' | 5 => '5' | 6 => '6' | 7 => '7'
  | 8 => '8' | 9 => '9' | 10 => 'a' | 11 => 'b'
  | 12 => 'c' | 13 => 'd' | 14 => 'e' | _ => 'f'

/-- Render the little-endian nibbles directly as a hexadecimal Lean literal.
This avoids constructing and decimal-printing enormous boundary naturals in
the untrusted generator. -/
def nibsHexLit (l : List Nat) : String :=
  let digits := l.reverse.dropWhile (fun n => n == 0)
  "0x" ++ String.ofList (if digits.isEmpty then ['0'] else digits.map hexDigit)

def encGroupsHex (enc : α → List Nat) (syms : List α) : List String :=
  (chunks 48 syms).map fun g => nibsHexLit (encVar g.length ++ g.flatMap enc)

def literalList (l : List String) : String :=
  "[" ++ String.intercalate ",\n  " l ++ "]"

/-- Render pure-count het symbols directly.  Direct boundary terms avoid the
decode-and-compare pass in every kernel checkpoint. -/
def hLSymLit : Lsym → String
  | .xs n => s!".xs (.pure {n})"
  | .D => ".D" | .P => ".P"
  | .C0 => ".C0" | .C1 => ".C1" | .C2 => ".C2" | .C3 => ".C3"
  | .F0 => ".F0" | .F1 => ".F1" | .F2 => ".F2" | .F3 => ".F3"
  | .G0 => ".G0" | .G1 => ".G1" | .G2 => ".G2"
  | .Fs n => s!".Fs (.pure {n})"
  | .Gs n => s!".Gs (.pure {n})"
  | .Hs n => s!".Hs (.pure {n})"

def hRSymLit : Rsym → String
  | .xs n => s!".xs (.pure {n})"
  | .D => ".D" | .C => ".C" | .P => ".P"
  | .Gs n => s!".Gs (.pure {n})"

def lSymLit : Lsym → String
  | .xs n => s!".xs {n}"
  | .D => ".D" | .P => ".P"
  | .C0 => ".C0" | .C1 => ".C1" | .C2 => ".C2" | .C3 => ".C3"
  | .F0 => ".F0" | .F1 => ".F1" | .F2 => ".F2" | .F3 => ".F3"
  | .G0 => ".G0" | .G1 => ".G1" | .G2 => ".G2"
  | .Fs n => s!".Fs {n}"
  | .Gs n => s!".Gs {n}"
  | .Hs n => s!".Hs {n}"

def symbolListLit (l : List String) : String :=
  "[" ++ String.intercalate ",\n  " l ++ "]"

/-- Emit a calibration chunk file: run to `at`, snapshot, run `K` more,
snapshot; verify decode∘encode round-trips natively; write the lemma file. -/
def emitcalMode (at_ K : Nat) (path : String) : IO Unit := do
  let mut c := initial
  for _ in [0:at_] do
    match fullstep c with
    | some c' => c := c'
    | none => IO.println "STUCK"; return
  let c0 := c
  let mut events : List Nat := []   -- reversed groups
  let mut acc : Nat := 0
  let mut accN : Nat := 0
  for _ in [0:K] do
    let ev : Nat := if (tryUniCycle c).isSome then 2
      else if (tryStride c).isSome then 1 else 0
    acc := acc + ev <<< (2 * accN)
    accN := accN + 1
    if accN == 64 then
      events := acc :: events
      acc := 0
      accN := 0
    match fullstep c with
    | some c' => c := c'
    | none => IO.println "STUCK in chunk"; return
  if accN != 0 then IO.println s!"WARN: K not divisible by 64 (tail {accN})"; return
  let evGroups := events.reverse
  let c1 := c
  let (d0, lg0, rg0) := encodeConf c0
  let (d1, lg1, rg1) := encodeConf c1
  -- native round-trip check
  if decodeConf d0 lg0 rg0 != c0 || decodeConf d1 lg1 rg1 != c1 then
    IO.println "ROUND-TRIP FAILURE"; return
  IO.println s!"round-trip ok; |L0|={c0.left.length} |R0|={c0.right.length} groups L={lg0.length} R={rg0.length}"
  let body := s!"import Busybeaver.Deciders.Skelet.Skelet1

namespace Deciders.Skelet.Skelet1

def calL0 : List ℕ := {natListLit lg0}
def calR0 : List ℕ := {natListLit rg0}
def calL1 : List ℕ := {natListLit lg1}
def calR1 : List ℕ := {natListLit rg1}
def calEv : List ℕ := {natListLit evGroups}

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
example : eqOConfF {lg1.length} {rg1.length}
    (stepsE {evGroups.length} calEv (decodeConfF {lg0.length} {rg0.length} {d0} calL0 calR0))
    {d1} calL1 calR1 = true := by decide +kernel

end Deciders.Skelet.Skelet1
"
  IO.FS.writeFile path body
  IO.println s!"wrote {path}"

/-! ## Het-window chunk emitter -/

def toH : Lsym → HLsym
  | .xs n => .xs (.pure n) | .D => .D | .P => .P
  | .C0 => .C0 | .C1 => .C1 | .C2 => .C2 | .C3 => .C3
  | .F0 => .F0 | .F1 => .F1 | .F2 => .F2 | .F3 => .F3
  | .G0 => .G0 | .G1 => .G1 | .G2 => .G2
  | .Fs n => .Fs (.pure n) | .Gs n => .Gs (.pure n) | .Hs n => .Hs (.pure n)

def toHR : Rsym → HRsym
  | .xs n => .xs (.pure n) | .D => .D | .C => .C | .P => .P
  | .Gs n => .Gs (.pure n)

def encHLsym : HLsym → List Nat
  | .xs (.pure n) => encVar 0 ++ encVar n
  | .D => encVar 1 | .P => encVar 2
  | .C0 => encVar 3 | .C1 => encVar 4 | .C2 => encVar 5 | .C3 => encVar 6
  | .F0 => encVar 7 | .F1 => encVar 8 | .F2 => encVar 9 | .F3 => encVar 10
  | .G0 => encVar 11 | .G1 => encVar 12 | .G2 => encVar 13
  | .Fs (.pure n) => encVar 14 ++ encVar n
  | .Gs (.pure n) => encVar 15 ++ encVar n
  | .Hs (.pure n) => encVar 16 ++ encVar n
  | .tailL => encVar 17
  | _ => []   -- het counts never occur in window boundaries

def encHRsym : HRsym → List Nat
  | .xs (.pure n) => encVar 0 ++ encVar n
  | .D => encVar 1 | .C => encVar 2 | .P => encVar 3
  | .Gs (.pure n) => encVar 4 ++ encVar n
  | .tailR => encVar 5
  | _ => []

def encodeHConf (c : HConf) : Nat × List Nat × List Nat :=
  let d := match c.dir with | .left => 0 | .right => 1
  (d, encGroups encHLsym c.left, encGroups encHRsym c.right)

/-- Emit a het-window chunk file for steps `[at, at+K)`. -/
def emitcalhMode (at_ K : Nat) (path : String) : IO Unit := do
  let mut c := initial
  for _ in [0:at_] do
    match fullstep c with
    | some c' => c := c'
    | none => IO.println "STUCK"; return
  let c0 := c
  let mut events : List Nat := []
  let mut acc : Nat := 0
  let mut accN : Nat := 0
  let mut minTouch : Nat := c0.left.length
  for _ in [0:K] do
    let ev : Nat := if (tryUniCycle c).isSome then 2
      else if (tryStride c).isSome then 1 else 0
    acc := acc + ev <<< (2 * accN)
    accN := accN + 1
    if accN == 64 then
      events := acc :: events
      acc := 0
      accN := 0
    if ev == 2 then
      -- a uni event consumes the 3-symbol head + 38-symbol J prefix and can
      -- merge into the symbol below; reads reach that deep too
      minTouch := min minTouch (c.left.length - 50)
    match fullstep c with
    | some c' =>
      minTouch := min minTouch (min c.left.length c'.left.length)
      c := c'
    | none => IO.println "STUCK in chunk"; return
  if accN != 0 then IO.println s!"K not divisible by 64"; return
  let evGroups := events.reverse
  let c1 := c
  let keep := if minTouch < 8 then 0 else minTouch - 8
  let tail0 := c0.left.drop (c0.left.length - keep)
  let tail1 := c1.left.drop (c1.left.length - keep)
  if tail0 != tail1 then IO.println "SUFFIX MISMATCH — window too small"; return
  let marker : List HLsym := if keep == 0 then [] else [.tailL]
  let win0 : List HLsym := (c0.left.take (c0.left.length - keep)).map toH ++ marker
  let win1 : List HLsym := (c1.left.take (c1.left.length - keep)).map toH ++ marker
  let h0 : HConf := ⟨c0.dir, win0, c0.right.map toHR⟩
  let h1 : HConf := ⟨c1.dir, win1, c1.right.map toHR⟩
  -- native validation of the het replay (step-by-step for diagnostics)
  let mut hc := h0
  let mut evIdx := 0
  let mut evFail := false
  for g in evGroups do
    if evFail then break
    let mut gg := g
    for _ in [0:64] do
      if evFail then break
      let ev := gg % 4
      gg := gg / 4
      match stepEH ev hc with
      | some hc' => hc := hc'
      | none =>
        IO.println s!"HET STEP FAILED at event index {evIdx}, ev={ev}"
        IO.println s!"  het left head: {(hc.left.take 8).map (fun s => match s with
          | .xs (.pure n) => s!"x{n}" | .D => "D" | .P => "P"
          | .C0 => "c0" | .C1 => "c1" | .C2 => "c2" | .C3 => "c3"
          | .tailL => "TAIL" | _ => "?")}"
        IO.println s!"  het right head: {(hc.right.take 6).map (fun s => match s with
          | .xs (.pure n) => s!"x{n}" | .D => "D" | .C => "C" | .P => "P" | _ => "?")}"
        IO.println s!"  het left len {hc.left.length}, right len {hc.right.length}"
        evFail := true
      evIdx := evIdx + 1
  if evFail then return
  if hc != h1 then IO.println "HET REPLAY MISMATCH"; return
  let (d0, lg0, rg0) := encodeHConf h0
  let (d1, lg1, rg1) := encodeHConf h1
  if decodeHConfF lg0.length rg0.length d0 lg0 rg0 != h0 ||
     decodeHConfF lg1.length rg1.length d1 lg1 rg1 != h1 then
    IO.println "ROUND-TRIP FAILURE"; return
  IO.println s!"ok: window {win0.length}/{win1.length} syms (keep {keep}), right {c0.right.length}, ev groups {evGroups.length}"
  let body := s!"import Busybeaver.Deciders.Skelet.Skelet1

namespace Deciders.Skelet.Skelet1

def chL0 : List ℕ := {natListLit lg0}
def chR0 : List ℕ := {natListLit rg0}
def chL1 : List ℕ := {natListLit lg1}
def chR1 : List ℕ := {natListLit rg1}
def chEv : List ℕ := {natListLit evGroups}

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
example : eqHOConfF {lg1.length} {rg1.length}
    (stepsEH {evGroups.length} chEv (decodeHConfF {lg0.length} {rg0.length} {d0} chL0 chR0))
    {d1} chL1 chR1 = true := by decide +kernel

end Deciders.Skelet.Skelet1
"
  IO.FS.writeFile path body
  IO.println s!"wrote {path}"

/-! ## Mass chunk emitter -/

/-- Successive symbolic configurations only rebuild a short prefix of their
left tapes.  Detect that shared suffix in constant bounded time, instead of
calling `List.length` on a huge tape after every event.  The fallback keeps the
untrusted generator robust if a future transition rebuilds more of the list. -/
unsafe def sharesTailWithin {α : Type} : Nat → List α → List α → Bool
  | 0, xs, ys => ptrEq xs ys
  | n + 1, xs, ys =>
    if ptrEq xs ys then true else
      match xs, ys with
      | _ :: xs, _ :: ys => sharesTailWithin n xs ys
      | _, _ => false

unsafe def leftLengthAfter {α : Type} (oldLen : Nat) (old new : List α) : Nat :=
  if sharesTailWithin 128 old new then oldLen
  else if sharesTailWithin 128 old (new.drop 1) then oldLen + 1
  else if sharesTailWithin 128 (old.drop 1) new then oldLen - 1
  else if sharesTailWithin 128 old (new.drop 2) then oldLen + 2
  else if sharesTailWithin 128 (old.drop 2) new then oldLen - 2
  else if sharesTailWithin 128 old (new.drop 3) then oldLen + 3
  else if sharesTailWithin 128 (old.drop 3) new then oldLen - 3
  else new.length

/-- Length of a physically shared suffix.  The trace evaluator is persistent,
so unchanged deep tape data normally has pointer identity.  Returning zero is
always safe when a transition happened to rebuild the list. -/
unsafe def sharedSuffixLenAux {α : Type} : Nat → List α → List α → Nat
  | n, xs, ys =>
    if ptrEq xs ys then n else
      match n, xs, ys with
      | n + 1, _ :: xs, _ :: ys => sharedSuffixLenAux n xs ys
      | _, _, _ => 0

unsafe def sharedSuffixLen {α : Type}
    (lenX lenY : Nat) (xs ys : List α) : Nat :=
  let n := min lenX lenY
  sharedSuffixLenAux n (xs.drop (lenX - n)) (ys.drop (lenY - n))

structure ChunkOut where
  idx : Nat
  startStep : Nat
  len : Nat
  keep : Nat
  rkeep : Nat
  cycled : Bool

/-- Emit one het-window chunk starting from `c0` for up to `K` steps (fewer
if cycling is hit); returns the end config and metadata, or none on failure. -/
unsafe def emitOneChunk (idx startStep K : Nat) (c0 : SConf) (dir : String)
    : IO (Option (SConf × ChunkOut)) := do
  let leftLen0 := c0.left.length
  let rightLen0 := c0.right.length
  let mut c := c0
  let mut leftLen := leftLen0
  let mut events : List Nat := []
  let mut acc : Nat := 0
  let mut accN : Nat := 0
  let mut minTouch : Nat := leftLen0
  let mut steps := 0
  let mut cycled := false
  for _ in [0:K] do
    if isCycling c then
      cycled := true
      break
    -- Compute the selected shortcut and its successor together.  Asking which
    -- shortcut fired and then calling `fullstep` used to evaluate the same
    -- expensive tape traversal twice at every generated event.
    let next : Option (Nat × SConf) :=
      match tryUniCycle c with
      | some c' => some (2, c')
      | none =>
        match tryStride c with
        | some c' => some (1, c')
        | none => (simpleStep c).map (fun c' => (0, c'))
    let some (ev, c') := next
      | IO.println s!"STUCK in chunk {idx}"; return none
    acc := acc + ev <<< (2 * accN)
    accN := accN + 1
    if accN == 64 then
      events := acc :: events
      acc := 0
      accN := 0
    let leftLen' := leftLengthAfter leftLen c.left c'.left
    if ev == 2 then
      minTouch := min minTouch (leftLen - 50)
    minTouch := min minTouch (min leftLen leftLen')
    c := c'
    leftLen := leftLen'
    steps := steps + 1
  let lastN := accN
  let lastG := acc
  let evGroups := events.reverse
  let c1 := c
  let leftLen1 := c1.left.length
  let rightLen1 := c1.right.length
  let keep0 := if minTouch < 8 then 0 else minTouch - 8
  -- Move the cut past any counted symbol.  Otherwise substitution can leave
  -- a smart constructor stuck at the opaque tail boundary.
  let isCounted : Lsym → Bool := fun s => match s with
    | .xs _ | .Fs _ | .Gs _ | .Hs _ => true | _ => false
  let countedAt (xs : List Lsym) (i : Nat) : Bool :=
    match xs[i]? with | some s => isCounted s | none => false
  let mut keep := keep0
  while keep > 0 &&
      (countedAt c0.left (leftLen0 - keep - 1) ||
       countedAt c1.left (leftLen1 - keep - 1)) do
    keep := keep - 1
  -- Right tapes stay below a thousand symbols on this trace.  Keeping them
  -- concrete makes checkpoint composition unary and, in measurements, is
  -- cheaper overall than introducing a second opaque-tail parameter.
  let rkeep := 0
  -- Direct constructor terms are measurably cheaper for the kernel than
  -- decoding packed naturals and then running a second fuelled comparison.
  let l0s := (c0.left.take (leftLen0 - keep)).map hLSymLit ++
    (if keep == 0 then [] else [".tailL"])
  let l1s := (c1.left.take (leftLen1 - keep)).map hLSymLit ++
    (if keep == 0 then [] else [".tailL"])
  let r0s := c0.right.map hRSymLit
  let r1s := c1.right.map hRSymLit
  let d0 := match c0.dir with | .left => ".left" | .right => ".right"
  let d1 := match c1.dir with | .left => ".left" | .right => ".right"
  let nm := s!"C{idx}"
  let stmt := if lastN == 0 then
    s!"stepsEH {evGroups.length} ev h0"
  else
    s!"(stepsEH {evGroups.length} ev h0).bind
      (stepsEH64 {lastN} {lastG})"
  let body := s!"import Busybeaver.Deciders.Skelet.Skelet1

namespace Deciders.Skelet.Skelet1.Cert.{nm}

def l0 : List HLsym := {symbolListLit l0s}
def r0 : List HRsym := {symbolListLit r0s}
def l1 : List HLsym := {symbolListLit l1s}
def r1 : List HRsym := {symbolListLit r1s}
def h0 : HConf := ⟨{d0}, l0, r0⟩
def h1 : HConf := ⟨{d1}, l1, r1⟩
def ev : List ℕ := {natListLit evGroups}
def keep : ℕ := {keep}
def rkeep : ℕ := {rkeep}
def leftLen0 : ℕ := {leftLen0}
def leftLen1 : ℕ := {leftLen1}
def rightLen0 : ℕ := {rightLen0}
def rightLen1 : ℕ := {rightLen1}

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem chunk : {stmt} = some h1 := by decide +kernel

def start (lt : List Lsym) : SConf := h0.subst 0 lt []
def finish (lt : List Lsym) : SConf := h1.subst 0 lt []

theorem reach (lt : List Lsym) :
    (start lt).lift -[M]->* (finish lt).lift :=
  stepsEH_spec {evGroups.length} chunk 0 lt []

end Deciders.Skelet.Skelet1.Cert.{nm}
"
  -- The final partial chunk composes its remaining events explicitly.
  let body := if lastN == 0 then body else
    s!"import Busybeaver.Deciders.Skelet.Skelet1

namespace Deciders.Skelet.Skelet1.Cert.{nm}

def l0 : List HLsym := {symbolListLit l0s}
def r0 : List HRsym := {symbolListLit r0s}
def l1 : List HLsym := {symbolListLit l1s}
def r1 : List HRsym := {symbolListLit r1s}
def h0 : HConf := ⟨{d0}, l0, r0⟩
def h1 : HConf := ⟨{d1}, l1, r1⟩
def ev : List ℕ := {natListLit evGroups}
def keep : ℕ := {keep}
def rkeep : ℕ := {rkeep}
def leftLen0 : ℕ := {leftLen0}
def leftLen1 : ℕ := {leftLen1}
def rightLen0 : ℕ := {rightLen0}
def rightLen1 : ℕ := {rightLen1}

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem chunk : ((stepsEH {evGroups.length} ev h0).bind
      (stepsEH64 {lastN} {lastG})) = some h1 := by decide +kernel

def start (lt : List Lsym) : SConf := h0.subst 0 lt []
def finish (lt : List Lsym) : SConf := h1.subst 0 lt []

theorem reach (lt : List Lsym) :
    (start lt).lift -[M]->* (finish lt).lift := by
  cases hm : stepsEH {evGroups.length} ev h0 with
  | none =>
      have hbad := chunk
      simp [hm] at hbad
  | some mid =>
      have ht : stepsEH64 {lastN} {lastG} mid =
          some h1 := by
        simpa [hm] using chunk
      exact (stepsEH_spec {evGroups.length} hm 0 lt []).trans
        (stepsEH64_spec {lastN} ht 0 lt [])

end Deciders.Skelet.Skelet1.Cert.{nm}
"
  IO.FS.writeFile (dir ++ s!"/{nm}.lean") body
  return some (c1, ⟨idx, startStep, steps, keep, rkeep, cycled⟩)

/-- Emit all chunks. -/
unsafe def emitallMode (K : Nat) (dir : String) : IO Unit := do
  IO.FS.createDirAll dir
  let mut c := initial
  let mut idx := 0
  let mut step := 0
  let mut manifest : List String := []
  while true do
    match ← emitOneChunk idx step K c dir with
    | none => IO.println "ABORT"; return
    | some (c1, md) =>
      manifest := s!"{md.idx} {md.startStep} {md.len} {md.keep} {md.rkeep} {if md.cycled then 1 else 0}" :: manifest
      c := c1
      idx := idx + 1
      step := step + md.len
      if md.cycled then
        IO.println s!"cycling reached at step {step}; {idx} chunks"
        break
      if idx % 100 == 0 then
        IO.println s!"chunk {idx} (step {step})"
        (← IO.getStdout).flush
  IO.FS.writeFile (dir ++ "/manifest.txt") (String.intercalate "\n" manifest.reverse)
  IO.println "done"

/-- Generate a disjoint chunk range.  This is deliberately resumable and lets
the untrusted source emitter use all cores; the generated proofs themselves
remain independently kernel checked. -/
unsafe def emitRangeMode (first count K : Nat) (dir : String) : IO Unit := do
  IO.FS.createDirAll dir
  let mut c := initial
  let startStep := first * K
  for _ in [0:startStep] do
    match fullstep c with
    | some c' => c := c'
    | none => IO.println "STUCK before range"; return
  let mut step := startStep
  for off in [0:count] do
    let idx := first + off
    match ← emitOneChunk idx step K c dir with
    | none => IO.println s!"ABORT range at {idx}"; return
    | some (c1, md) =>
      c := c1
      step := step + md.len
      if md.cycled then
        IO.println s!"range {first}: cycling at step {step}, chunk {idx}"
        return
  IO.println s!"range {first}: wrote {count} chunks"

/-- Pack several already-emitted checkpoint namespaces into one Lean module.
The theorems and names are unchanged; only process/import overhead is shared. -/
def packMode (count packSize : Nat) (dir : String) : IO Unit := do
  let packDir := dir ++ "/Pack"
  IO.FS.createDirAll packDir
  let packs := (count + packSize - 1) / packSize
  for p in [0:packs] do
    let first := p * packSize
    let stop := min count (first + packSize)
    let mut bodies : List String := []
    for i in [first:stop] do
      let src ← IO.FS.readFile (dir ++ s!"/C{i}.lean")
      -- Every raw module has exactly one import line.  Imports must precede
      -- declarations in the packed module, so retain a single shared import.
      let body := String.intercalate "\n" ((src.splitOn "\n").drop 1)
      bodies := body :: bodies
    let packed := "import Busybeaver.Deciders.Skelet.Skelet1\n\n" ++
      String.intercalate "\n" bodies.reverse
    IO.FS.writeFile (packDir ++ s!"/P{p}.lean") packed
  IO.println s!"wrote {packs} packed checkpoint modules"

/-- Pack a disjoint checkpoint range while retaining its global C/P indices.
Used for targeted performance validation before a full regeneration. -/
def packRangeMode (first count packSize : Nat) (dir : String) : IO Unit := do
  let packDir := dir ++ "/Pack"
  IO.FS.createDirAll packDir
  let firstPack := first / packSize
  let stop := first + count
  let stopPack := (stop + packSize - 1) / packSize
  for p in [firstPack:stopPack] do
    let chunkFirst := max first (p * packSize)
    let chunkStop := min stop ((p + 1) * packSize)
    let mut bodies : List String := []
    for i in [chunkFirst:chunkStop] do
      let src ← IO.FS.readFile (dir ++ s!"/C{i}.lean")
      let body := String.intercalate "\n" ((src.splitOn "\n").drop 1)
      bodies := body :: bodies
    let packed := "import Busybeaver.Deciders.Skelet.Skelet1\n\n" ++
      String.intercalate "\n" bodies.reverse
    IO.FS.writeFile (packDir ++ s!"/P{p}.lean") packed
  IO.println s!"wrote packs {firstPack}..{stopPack - 1}"

/-- Emit a parallel composition layer after all computational chunks exist.

Every segment proves a transformation for an *arbitrary* opaque left-tape
tail, so segments have no dependencies on one another.  Independent join
modules each combine 32 segments, and `All.lean` only has to compose the small
number of joins.  This replaces an 856-module linear import chain. -/
def emitChainMode (count blockSize packSize : Nat) (dir : String) : IO Unit := do
  let segmentDir := dir ++ "/Segment"
  let joinDir := dir ++ "/Join"
  IO.FS.createDirAll segmentDir
  IO.FS.createDirAll joinDir
  let blocks := (count + blockSize - 1) / blockSize

  for b in [0:blocks] do
    let first := b * blockSize
    let stop := min count (first + blockSize)
    let last := stop - 1
    let importStop := if stop < count then stop + 1 else stop
    let mut imports : List String := []
    if packSize == 1 then
      for i in [first:importStop] do
        imports := s!"import Skelet1Cert.C{i}" :: imports
    else
      let firstPack := first / packSize
      let stopPack := (importStop + packSize - 1) / packSize
      for p in [firstPack:stopPack] do
        imports := s!"import Skelet1Cert.Pack.P{p}" :: imports
    let mut decls : List String := []
    for i in [first:stop] do
      if i == first then
        decls := s!"theorem reach{i} (lt : List Lsym) :\n    (C{first}.start lt).lift -[M]->* (C{i}.finish lt).lift :=\n  C{i}.reach lt\n\n" :: decls
      else
        let prevTail := if i == first + 1 then "lt" else s!"ltail{i - 1} lt"
        decls := s!"def ltail{i} (lt : List Lsym) : List Lsym :=\n  (C{i - 1}.finish ({prevTail})).left.drop (C{i}.leftLen0 - C{i}.keep)\n\n" :: decls
        decls := s!"theorem bridge{i} (lt : List Lsym) :\n    C{i - 1}.finish ({prevTail}) = C{i}.start (ltail{i} lt) := by\n  rfl\n\n" :: decls
        decls := s!"theorem reach{i} (lt : List Lsym) :\n    (C{first}.start lt).lift -[M]->* (C{i}.finish (ltail{i} lt)).lift := by\n  have h := C{i}.reach (ltail{i} lt)\n  rw [← bridge{i} lt] at h\n  exact (reach{i - 1} lt).trans h\n\n" :: decls
    let lastTail := if last == first then "lt" else s!"ltail{last} lt"
    if stop < count then
      decls := s!"def nextTail (lt : List Lsym) : List Lsym :=\n  (C{last}.finish ({lastTail})).left.drop (C{stop}.leftLen0 - C{stop}.keep)\n\n" :: decls
      decls := s!"theorem exitBridge (lt : List Lsym) :\n    C{last}.finish ({lastTail}) = C{stop}.start (nextTail lt) := by\n  rfl\n\n" :: decls
      decls := s!"theorem reachNext (lt : List Lsym) :\n    (C{first}.start lt).lift -[M]->* (C{stop}.start (nextTail lt)).lift := by\n  have h := reach{last} lt\n  rw [exitBridge lt] at h\n  exact h\n\n" :: decls
    else
      decls := s!"def outTail (lt : List Lsym) : List Lsym := {lastTail}\n\n" :: decls
      decls := s!"theorem reachFinal (lt : List Lsym) :\n    (C{first}.start lt).lift -[M]->* (C{last}.finish (outTail lt)).lift :=\n  reach{last} lt\n\n" :: decls
    let body := String.intercalate "\n" imports.reverse ++
      s!"\n\nnamespace Deciders.Skelet.Skelet1.Cert.Segment.S{b}\n\nset_option maxRecDepth 100000\nset_option maxHeartbeats 0\n\n" ++
      String.join decls.reverse ++
      s!"end Deciders.Skelet.Skelet1.Cert.Segment.S{b}\n"
    IO.FS.writeFile (segmentDir ++ s!"/S{b}.lean") body

  let joinSize := 32
  let joins := (blocks + joinSize - 1) / joinSize
  for j in [0:joins] do
    let firstBlock := j * joinSize
    let stopBlock := min blocks (firstBlock + joinSize)
    let lastBlock := stopBlock - 1
    let firstChunk := firstBlock * blockSize
    let mut imports : List String := []
    for b in [firstBlock:stopBlock] do
      imports := s!"import Skelet1Cert.Segment.S{b}" :: imports
    let mut decls : List String := []
    for b in [firstBlock:stopBlock] do
      let inTail := if b == firstBlock then "lt" else s!"stail{b} lt"
      if b + 1 < blocks then
        decls := s!"def stail{b + 1} (lt : List Lsym) : List Lsym :=\n  S{b}.nextTail ({inTail})\n\n" :: decls
        if b == firstBlock then
          decls := s!"theorem reach{b} (lt : List Lsym) :\n    (C{firstChunk}.start lt).lift -[M]->* (C{(b + 1) * blockSize}.start (stail{b + 1} lt)).lift :=\n  S{b}.reachNext lt\n\n" :: decls
        else
          decls := s!"theorem reach{b} (lt : List Lsym) :\n    (C{firstChunk}.start lt).lift -[M]->* (C{(b + 1) * blockSize}.start (stail{b + 1} lt)).lift :=\n  (reach{b - 1} lt).trans (S{b}.reachNext ({inTail}))\n\n" :: decls
      else
        decls := s!"def outTail (lt : List Lsym) : List Lsym :=\n  S{b}.outTail ({inTail})\n\n" :: decls
        if b == firstBlock then
          decls := s!"theorem reachFinal (lt : List Lsym) :\n    (C{firstChunk}.start lt).lift -[M]->* (C{count - 1}.finish (outTail lt)).lift :=\n  S{b}.reachFinal lt\n\n" :: decls
        else
          decls := s!"theorem reachFinal (lt : List Lsym) :\n    (C{firstChunk}.start lt).lift -[M]->* (C{count - 1}.finish (outTail lt)).lift :=\n  (reach{b - 1} lt).trans (S{b}.reachFinal ({inTail}))\n\n" :: decls
    if stopBlock < blocks then
      decls := s!"def nextTail (lt : List Lsym) : List Lsym := stail{stopBlock} lt\n\n" :: decls
      decls := s!"theorem reachNext (lt : List Lsym) :\n    (C{firstChunk}.start lt).lift -[M]->* (C{stopBlock * blockSize}.start (nextTail lt)).lift :=\n  reach{lastBlock} lt\n\n" :: decls
    let body := String.intercalate "\n" imports.reverse ++
      s!"\n\nnamespace Deciders.Skelet.Skelet1.Cert.Join.J{j}\n\nset_option maxRecDepth 100000\nset_option maxHeartbeats 0\n\n" ++
      String.join decls.reverse ++
      s!"end Deciders.Skelet.Skelet1.Cert.Join.J{j}\n"
    IO.FS.writeFile (joinDir ++ s!"/J{j}.lean") body

  let last := count - 1
  let lastJoin := joins - 1
  let mut imports : List String := []
  for j in [0:joins] do
    imports := s!"import Skelet1Cert.Join.J{j}" :: imports
  let mut decls : List String := ["def joinTail0 : List Lsym := []\n\n"]
  for j in [0:joins] do
    let inTail := s!"joinTail{j}"
    if j + 1 < joins then
      decls := s!"def joinTail{j + 1} : List Lsym := J{j}.nextTail {inTail}\n\n" :: decls
      if j == 0 then
        decls := s!"theorem joinReach{j} :\n    (C0.start joinTail0).lift -[M]->* (C{(j + 1) * joinSize * blockSize}.start joinTail{j + 1}).lift :=\n  J{j}.reachNext joinTail0\n\n" :: decls
      else
        decls := s!"theorem joinReach{j} :\n    (C0.start joinTail0).lift -[M]->* (C{(j + 1) * joinSize * blockSize}.start joinTail{j + 1}).lift :=\n  joinReach{j - 1}.trans (J{j}.reachNext {inTail})\n\n" :: decls
  let prior := if lastJoin == 0 then
      s!"J0.reachFinal joinTail0"
    else
      s!"joinReach{lastJoin - 1}.trans (J{lastJoin}.reachFinal joinTail{lastJoin})"
  decls := s!"abbrev finalConf : SConf := C{last}.finish (J{lastJoin}.outTail joinTail{lastJoin})\n\n" :: decls
  decls := s!"theorem reachesFinal : initial.lift -[M]->* finalConf.lift := by\n  have h := {prior}\n  simpa [joinTail0, C0.start, initial] using h\n\n" :: decls
  decls := "theorem finalCycling : isCycling finalConf = true := by\n  rfl\n\n" :: decls
  decls := "theorem nonhalt : ¬ M.halts (default : Config 4 1) :=\n  Machine.halts.skip_evstep init'\n    (Machine.halts.skip_evstep reachesFinal (is_cycling_spec finalCycling))\n\n" :: decls
  let all := String.intercalate "\n" imports.reverse ++
    "\n\nnamespace Deciders.Skelet.Skelet1.Cert\n\nopen Turing TM.Table\n\nset_option maxRecDepth 100000\nset_option maxHeartbeats 0\n\n" ++
    String.join decls.reverse ++
    "end Deciders.Skelet.Skelet1.Cert\n"
  IO.FS.writeFile (dir ++ "/All.lean") all
  IO.println s!"wrote {blocks} independent segments, {joins} joins, and All.lean"

def checkpointKeep (dir : String) (idx : Nat) : IO Nat := do
  let src ← IO.FS.readFile (dir ++ s!"/C{idx}.lean")
  let some line := (src.splitOn "\n").find? (fun line => line.startsWith "def keep : ℕ := ")
    | throw <| IO.userError s!"missing keep declaration in C{idx}.lean"
  let rhs := (line.splitOn ":=").getD 1 "" |>.trimAscii.toString
  let some keep := rhs.toNat?
    | throw <| IO.userError s!"bad keep declaration in C{idx}.lean: {line}"
  return keep

/-- Emit compact, independently checkable concrete tape anchors.  Only the
preserved left suffix is serialized; the checkpoint already contains its
small changing prefix and complete right tape. -/
unsafe def emitAnchorsMode (count blockSize K : Nat) (dir : String) : IO Unit := do
  let anchorDir := dir ++ "/Anchor"
  IO.FS.createDirAll anchorDir
  let mut c := initial
  for idx in [0:count] do
    if idx % blockSize == 0 then
      let keep ← checkpointKeep dir idx
      let tail := c.left.drop (c.left.length - keep)
      let groups := encGroupsHex encLsym tail
      let b := idx / blockSize
      let body := s!"import Busybeaver.Deciders.Skelet.Skelet1

namespace Deciders.Skelet.Skelet1.Cert.Anchor.A{b}

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

def packed : List ℕ := {literalList groups}
def tail : List Lsym := (decodeConfF packed.length 0 0 packed []).left

end Deciders.Skelet.Skelet1.Cert.Anchor.A{b}
"
      IO.FS.writeFile (anchorDir ++ s!"/A{b}.lean") body
      if b % 50 == 0 then
        IO.println s!"anchor {b} at checkpoint {idx}, suffix {keep}"
        (← IO.getStdout).flush
    let mut cycled := false
    for _ in [0:K] do
      if !cycled then
        if isCycling c then
          cycled := true
        else
          match fullstep c with
          | some c' => c := c'
          | none => IO.println s!"STUCK before checkpoint {idx + 1}"; return
    if cycled && idx + 1 < count then
      IO.println s!"cycling reached early before checkpoint {idx + 1}"
      return
  IO.println s!"wrote {(count + blockSize - 1) / blockSize} concrete anchors"

/-- Compose checkpoint chunks through concrete packed anchors.  Segment
modules are independent and can be kernel checked in parallel. -/
def emitAnchoredChainMode (count blockSize packSize : Nat) (dir : String) : IO Unit := do
  let segmentDir := dir ++ "/AnchoredSegment"
  let joinDir := dir ++ "/AnchoredJoin"
  IO.FS.createDirAll segmentDir
  IO.FS.createDirAll joinDir
  let blocks := (count + blockSize - 1) / blockSize
  for b in [0:blocks] do
    let first := b * blockSize
    let stop := min count (first + blockSize)
    let last := stop - 1
    let importStop := if stop < count then stop + 1 else stop
    let mut imports : List String := [s!"import Skelet1Cert.Anchor.A{b}"]
    if stop < count then
      imports := s!"import Skelet1Cert.Anchor.A{b + 1}" :: imports
    if packSize == 1 then
      for i in [first:importStop] do
        imports := s!"import Skelet1Cert.C{i}" :: imports
    else
      let firstPack := first / packSize
      let stopPack := (importStop + packSize - 1) / packSize
      for p in [firstPack:stopPack] do
        imports := s!"import Skelet1Cert.Pack.P{p}" :: imports
    let mut decls : List String := []
    decls := s!"def ltail{first} : List Lsym := Anchor.A{b}.tail\n\n" :: decls
    decls := s!"theorem reach{first} :\n    (C{first}.start ltail{first}).lift -[M]->* (C{first}.finish ltail{first}).lift :=\n  C{first}.reach ltail{first}\n\n" :: decls
    for i in [first + 1:stop] do
      let prevTail := if i == first + 1 then s!"ltail{first}" else s!"ltail{i - 1}"
      decls := s!"def ltail{i} : List Lsym :=\n  (C{i - 1}.finish {prevTail}).left.drop (C{i}.leftLen0 - C{i}.keep)\n\n" :: decls
      decls := s!"theorem bridge{i} : C{i - 1}.finish {prevTail} = C{i}.start ltail{i} := by\n  rfl\n\n" :: decls
      decls := s!"theorem reach{i} :\n    (C{first}.start ltail{first}).lift -[M]->* (C{i}.finish ltail{i}).lift := by\n  have h := C{i}.reach ltail{i}\n  rw [← bridge{i}] at h\n  exact reach{i - 1}.trans h\n\n" :: decls
    let lastTail := if last == first then s!"ltail{first}" else s!"ltail{last}"
    if stop < count then
      decls := s!"theorem exitBridge :\n    C{last}.finish {lastTail} = C{stop}.start Anchor.A{b + 1}.tail := by\n  rfl\n\n" :: decls
      decls := s!"theorem reachNext :\n    (C{first}.start Anchor.A{b}.tail).lift -[M]->*\n      (C{stop}.start Anchor.A{b + 1}.tail).lift := by\n  have h := reach{last}\n  rw [exitBridge] at h\n  exact h\n\n" :: decls
    else
      decls := s!"abbrev finalConf : SConf := C{last}.finish {lastTail}\n\n" :: decls
      decls := s!"theorem reachFinal :\n    (C{first}.start Anchor.A{b}.tail).lift -[M]->* finalConf.lift :=\n  reach{last}\n\n" :: decls
      decls := "theorem finalCycling : isCycling finalConf = true := by\n  rfl\n\n" :: decls
    let body := String.intercalate "\n" imports.reverse ++
      s!"\n\nnamespace Deciders.Skelet.Skelet1.Cert.AnchoredSegment.S{b}\n\nset_option maxRecDepth 1000000\nset_option maxHeartbeats 0\n\n" ++
      String.join decls.reverse ++
      s!"end Deciders.Skelet.Skelet1.Cert.AnchoredSegment.S{b}\n"
    IO.FS.writeFile (segmentDir ++ s!"/S{b}.lean") body

  let joinSize := 32
  let joins := (blocks + joinSize - 1) / joinSize
  for j in [0:joins] do
    let firstBlock := j * joinSize
    let stopBlock := min blocks (firstBlock + joinSize)
    let lastBlock := stopBlock - 1
    let mut imports : List String := []
    for b in [firstBlock:stopBlock] do
      imports := s!"import Skelet1Cert.AnchoredSegment.S{b}" :: imports
    let firstChunk := firstBlock * blockSize
    let mut decls : List String := []
    for b in [firstBlock:stopBlock] do
      if b + 1 < blocks then
        if b == firstBlock then
          decls := s!"theorem reach{b} :\n    (C{firstChunk}.start Anchor.A{firstBlock}.tail).lift -[M]->*\n      (C{(b + 1) * blockSize}.start Anchor.A{b + 1}.tail).lift :=\n  S{b}.reachNext\n\n" :: decls
        else
          decls := s!"theorem reach{b} :\n    (C{firstChunk}.start Anchor.A{firstBlock}.tail).lift -[M]->*\n      (C{(b + 1) * blockSize}.start Anchor.A{b + 1}.tail).lift :=\n  reach{b - 1}.trans S{b}.reachNext\n\n" :: decls
      else
        if b == firstBlock then
          decls := s!"theorem reachFinal :\n    (C{firstChunk}.start Anchor.A{firstBlock}.tail).lift -[M]->* S{b}.finalConf.lift :=\n  S{b}.reachFinal\n\n" :: decls
        else
          decls := s!"theorem reachFinal :\n    (C{firstChunk}.start Anchor.A{firstBlock}.tail).lift -[M]->* S{b}.finalConf.lift :=\n  reach{b - 1}.trans S{b}.reachFinal\n\n" :: decls
    if stopBlock < blocks then
      decls := s!"theorem reachNext :\n    (C{firstChunk}.start Anchor.A{firstBlock}.tail).lift -[M]->*\n      (C{stopBlock * blockSize}.start Anchor.A{stopBlock}.tail).lift :=\n  reach{lastBlock}\n\n" :: decls
    let body := String.intercalate "\n" imports.reverse ++
      s!"\n\nnamespace Deciders.Skelet.Skelet1.Cert.AnchoredJoin.J{j}\n\n" ++
      String.join decls.reverse ++
      s!"end Deciders.Skelet.Skelet1.Cert.AnchoredJoin.J{j}\n"
    IO.FS.writeFile (joinDir ++ s!"/J{j}.lean") body

  let lastBlock := blocks - 1
  let lastJoin := joins - 1
  let mut imports : List String := []
  for j in [0:joins] do
    imports := s!"import Skelet1Cert.AnchoredJoin.J{j}" :: imports
  let mut decls : List String := []
  for j in [0:joins - 1] do
    if j == 0 then
      decls := s!"theorem joinReach0 :\n    (C0.start Anchor.A0.tail).lift -[M]->*\n      (C{joinSize * blockSize}.start Anchor.A{joinSize}.tail).lift :=\n  AnchoredJoin.J0.reachNext\n\n" :: decls
    else
      decls := s!"theorem joinReach{j} :\n    (C0.start Anchor.A0.tail).lift -[M]->*\n      (C{(j + 1) * joinSize * blockSize}.start Anchor.A{(j + 1) * joinSize}.tail).lift :=\n  joinReach{j - 1}.trans AnchoredJoin.J{j}.reachNext\n\n" :: decls
  let prior := if lastJoin == 0 then
      s!"AnchoredJoin.J0.reachFinal"
    else
      s!"joinReach{lastJoin - 1}.trans AnchoredJoin.J{lastJoin}.reachFinal"
  decls := s!"abbrev finalConf : SConf := AnchoredSegment.S{lastBlock}.finalConf\n\n" :: decls
  decls := s!"theorem reachesFinal : initial.lift -[M]->* finalConf.lift := by\n  have h := {prior}\n  simpa [Anchor.A0.tail, Anchor.A0.packed, decodeConfF, C0.start, initial] using h\n\n" :: decls
  decls := s!"theorem finalCycling : isCycling finalConf = true :=\n  AnchoredSegment.S{lastBlock}.finalCycling\n\n" :: decls
  decls := "theorem nonhalt : ¬ M.halts (default : Config 4 1) :=\n  Machine.halts.skip_evstep init'\n    (Machine.halts.skip_evstep reachesFinal (is_cycling_spec finalCycling))\n\n" :: decls
  let all := String.intercalate "\n" imports.reverse ++
    "\n\nnamespace Deciders.Skelet.Skelet1.Cert\n\nopen Turing TM.Table\n\n" ++
    String.join decls.reverse ++
    "end Deciders.Skelet.Skelet1.Cert\n"
  IO.FS.writeFile (dir ++ "/All.lean") all
  IO.println s!"wrote {blocks} anchored segments, {joins} joins, and All.lean"

def blockBaseKeep (dir : String) (first stop : Nat) : IO Nat := do
  let mut base ← checkpointKeep dir first
  for i in [first + 1:stop] do
    base := min base (← checkpointKeep dir i)
  return base

/-- Emit only the finite prefix of each block-entry tail that later steps in
the block may expose.  The much larger untouched suffix remains a parameter
of the proof and is never decoded or materialized. -/
unsafe def emitLocalAnchorsMode (count blockSize K : Nat) (dir : String) : IO Unit := do
  let anchorDir := dir ++ "/LocalAnchor"
  IO.FS.createDirAll anchorDir
  let mut c := initial
  for idx in [0:count] do
    if idx % blockSize == 0 then
      let stop := min count (idx + blockSize)
      let keep ← checkpointKeep dir idx
      let base ← blockBaseKeep dir idx stop
      let prefixLen := keep - base
      let pref := c.left.drop (c.left.length - keep) |>.take prefixLen
      let b := idx / blockSize
      let body := s!"import Busybeaver.Deciders.Skelet.Skelet1

namespace Deciders.Skelet.Skelet1.Cert.LocalAnchor.A{b}

def baseKeep : ℕ := {base}
def known : List Lsym := {symbolListLit (pref.map lSymLit)}

end Deciders.Skelet.Skelet1.Cert.LocalAnchor.A{b}
"
      IO.FS.writeFile (anchorDir ++ s!"/A{b}.lean") body
      if b % 50 == 0 then
        IO.println s!"local anchor {b}: keep {keep}, base {base}, prefix {prefixLen}"
        (← IO.getStdout).flush
    let mut cycled := false
    for _ in [0:K] do
      if !cycled then
        if isCycling c then
          cycled := true
        else
          match fullstep c with
          | some c' => c := c'
          | none => IO.println s!"STUCK before checkpoint {idx + 1}"; return
    if cycled && idx + 1 < count then
      IO.println s!"cycling reached early before checkpoint {idx + 1}"
      return
  IO.println s!"wrote {(count + blockSize - 1) / blockSize} local anchors"

/-- Emit independent locally-anchored segments.  Since block minima on this
trace are strictly increasing, a join can obtain the next (longer) opaque
suffix from its predecessor without inspecting unknown tape data. -/
def emitLocalChainMode (count blockSize packSize : Nat) (dir : String) : IO Unit := do
  let segmentDir := dir ++ "/LocalSegment"
  let joinDir := dir ++ "/LocalJoin"
  IO.FS.createDirAll segmentDir
  IO.FS.createDirAll joinDir
  let blocks := (count + blockSize - 1) / blockSize
  for b in [0:blocks] do
    let first := b * blockSize
    let stop := min count (first + blockSize)
    let last := stop - 1
    let mut imports : List String := [s!"import Skelet1Cert.LocalAnchor.A{b}"]
    if packSize == 1 then
      for i in [first:stop] do
        imports := s!"import Skelet1Cert.C{i}" :: imports
    else
      let firstPack := first / packSize
      let stopPack := (stop + packSize - 1) / packSize
      for p in [firstPack:stopPack] do
        imports := s!"import Skelet1Cert.Pack.P{p}" :: imports
    let mut decls : List String := []
    decls := ("def startTail (rest : List Lsym) : List Lsym :=\n  LocalAnchor.A" ++
      toString b ++ ".known ++ rest\n\n") :: decls
    decls := s!"abbrev startConf (rest : List Lsym) : SConf := C{first}.start (startTail rest)\n\n" :: decls
    decls := s!"theorem reach{first} (rest : List Lsym) :\n    (startConf rest).lift -[M]->* (C{first}.finish (startTail rest)).lift :=\n  C{first}.reach (startTail rest)\n\n" :: decls
    for i in [first + 1:stop] do
      let prevTail := if i == first + 1 then "startTail rest" else s!"ltail{i - 1} rest"
      decls := s!"def ltail{i} (rest : List Lsym) : List Lsym :=\n  (C{i - 1}.finish ({prevTail})).left.drop (C{i}.leftLen0 - C{i}.keep)\n\n" :: decls
      decls := s!"theorem bridge{i} (rest : List Lsym) :\n    C{i - 1}.finish ({prevTail}) = C{i}.start (ltail{i} rest) := by\n  rfl\n\n" :: decls
      decls := s!"theorem reach{i} (rest : List Lsym) :\n    (startConf rest).lift -[M]->* (C{i}.finish (ltail{i} rest)).lift := by\n  have h := C{i}.reach (ltail{i} rest)\n  rw [← bridge{i} rest] at h\n  exact (reach{i - 1} rest).trans h\n\n" :: decls
    let lastTail := if last == first then "startTail rest" else s!"ltail{last} rest"
    decls := s!"def endTail (rest : List Lsym) : List Lsym := {lastTail}\n\n" :: decls
    decls := s!"abbrev endConf (rest : List Lsym) : SConf := C{last}.finish (endTail rest)\n\n" :: decls
    decls := s!"theorem reach (rest : List Lsym) :\n    (startConf rest).lift -[M]->* (endConf rest).lift :=\n  reach{last} rest\n\n" :: decls
    if stop == count then
      decls := "theorem finalCycling (rest : List Lsym) : isCycling (endConf rest) = true := by\n  rfl\n\n" :: decls
    let body := String.intercalate "\n" imports.reverse ++
      s!"\n\nnamespace Deciders.Skelet.Skelet1.Cert.LocalSegment.S{b}\n\nset_option maxRecDepth 1000000\nset_option maxHeartbeats 0\n\n" ++
      String.join decls.reverse ++
      s!"end Deciders.Skelet.Skelet1.Cert.LocalSegment.S{b}\n"
    IO.FS.writeFile (segmentDir ++ s!"/S{b}.lean") body

  let joinSize := 32
  let joins := (blocks + joinSize - 1) / joinSize
  for j in [0:joins] do
    let firstBlock := j * joinSize
    let stopBlock := min blocks (firstBlock + joinSize)
    let lastBlock := stopBlock - 1
    let mut imports : List String := []
    for b in [firstBlock:stopBlock] do
      imports := s!"import Skelet1Cert.LocalSegment.S{b}" :: imports
    let mut decls : List String := []
    for b in [firstBlock:stopBlock] do
      let inRest := if b == firstBlock then "rest" else s!"rest{b} rest"
      if b == firstBlock then
        decls := s!"theorem reach{b} (rest : List Lsym) :\n    (S{b}.startConf rest).lift -[M]->* (S{b}.endConf rest).lift :=\n  S{b}.reach rest\n\n" :: decls
      else
        let prevRest := if b == firstBlock + 1 then "rest" else s!"rest{b - 1} rest"
        decls := s!"def rest{b} (rest : List Lsym) : List Lsym :=\n  (S{b - 1}.endConf ({prevRest})).left.drop\n    (C{b * blockSize}.leftLen0 - LocalAnchor.A{b}.baseKeep)\n\n" :: decls
        decls := s!"theorem bridge{b} (rest : List Lsym) :\n    S{b - 1}.endConf ({prevRest}) = S{b}.startConf (rest{b} rest) := by\n  rfl\n\n" :: decls
        decls := s!"theorem reach{b} (rest : List Lsym) :\n    (S{firstBlock}.startConf rest).lift -[M]->* (S{b}.endConf ({inRest})).lift := by\n  have h := S{b}.reach ({inRest})\n  rw [← bridge{b} rest] at h\n  exact (reach{b - 1} rest).trans h\n\n" :: decls
    let lastRest := if lastBlock == firstBlock then "rest" else s!"rest{lastBlock} rest"
    decls := s!"abbrev startConf (rest : List Lsym) : SConf := S{firstBlock}.startConf rest\n\n" :: decls
    decls := s!"abbrev endConf (rest : List Lsym) : SConf := S{lastBlock}.endConf ({lastRest})\n\n" :: decls
    decls := s!"theorem reach (rest : List Lsym) :\n    (startConf rest).lift -[M]->* (endConf rest).lift :=\n  reach{lastBlock} rest\n\n" :: decls
    if stopBlock == blocks then
      decls := s!"theorem finalCycling (rest : List Lsym) : isCycling (endConf rest) = true :=\n  S{lastBlock}.finalCycling ({lastRest})\n\n" :: decls
    let body := String.intercalate "\n" imports.reverse ++
      s!"\n\nnamespace Deciders.Skelet.Skelet1.Cert.LocalJoin.J{j}\n\nset_option maxRecDepth 1000000\nset_option maxHeartbeats 0\n\n" ++
      "open Deciders.Skelet.Skelet1.Cert.LocalSegment\n\n" ++
      String.join decls.reverse ++
      s!"end Deciders.Skelet.Skelet1.Cert.LocalJoin.J{j}\n"
    IO.FS.writeFile (joinDir ++ s!"/J{j}.lean") body

  let lastJoin := joins - 1
  let mut imports : List String := []
  for j in [0:joins] do
    imports := s!"import Skelet1Cert.LocalJoin.J{j}" :: imports
  let mut decls : List String := ["def topRest0 : List Lsym := []\n\n"]
  for j in [0:joins] do
    let inRest := s!"topRest{j}"
    if j == 0 then
      decls := "theorem topReach0 :\n    (LocalJoin.J0.startConf topRest0).lift -[M]->*\n      (LocalJoin.J0.endConf topRest0).lift :=\n  LocalJoin.J0.reach topRest0\n\n" :: decls
    else
      let firstBlock := j * joinSize
      let firstChunk := firstBlock * blockSize
      decls := s!"def topRest{j} : List Lsym :=\n  (LocalJoin.J{j - 1}.endConf topRest{j - 1}).left.drop\n    (C{firstChunk}.leftLen0 - LocalAnchor.A{firstBlock}.baseKeep)\n\n" :: decls
      decls := s!"theorem topBridge{j} :\n    LocalJoin.J{j - 1}.endConf topRest{j - 1} =\n      LocalJoin.J{j}.startConf {inRest} := by\n  rfl\n\n" :: decls
      decls := s!"theorem topReach{j} :\n    (LocalJoin.J0.startConf topRest0).lift -[M]->*\n      (LocalJoin.J{j}.endConf {inRest}).lift := by\n  have h := LocalJoin.J{j}.reach {inRest}\n  rw [← topBridge{j}] at h\n  exact topReach{j - 1}.trans h\n\n" :: decls
  decls := s!"abbrev finalConf : SConf := LocalJoin.J{lastJoin}.endConf topRest{lastJoin}\n\n" :: decls
  decls := s!"theorem reachesFinal : initial.lift -[M]->* finalConf.lift := by\n  have h := topReach{lastJoin}\n  simpa [topRest0, LocalJoin.J0.startConf, LocalSegment.S0.startConf,\n    LocalSegment.S0.startTail, LocalAnchor.A0.known, C0.start, C0.h0,\n    C0.l0, C0.r0, HConf.subst, substL, substR, initial] using h\n\n" :: decls
  decls := s!"theorem finalCycling : isCycling finalConf = true :=\n  LocalJoin.J{lastJoin}.finalCycling topRest{lastJoin}\n\n" :: decls
  decls := "theorem nonhalt : ¬ M.halts (default : Config 4 1) :=\n  Machine.halts.skip_evstep init'\n    (Machine.halts.skip_evstep reachesFinal (is_cycling_spec finalCycling))\n\n" :: decls
  let all := String.intercalate "\n" imports.reverse ++
    "\n\nnamespace Deciders.Skelet.Skelet1.Cert\n\nopen Turing TM.Table\n\nset_option maxRecDepth 1000000\nset_option maxHeartbeats 0\n\n" ++
    String.join decls.reverse ++
    "end Deciders.Skelet.Skelet1.Cert\n"
  IO.FS.writeFile (dir ++ "/All.lean") all
  IO.println s!"wrote {blocks} local segments, {joins} joins, and All.lean"

/-- Calibration emitter for a single flat local segment.  Unlike the recursive
`ltail` chain, every checkpoint tail is a short concrete prefix appended to
the same opaque `rest`, so bridge reduction is linear in the block size. -/
unsafe def emitFlatBlockMode (first count K blockId packSize : Nat)
    (dir : String) : IO Unit := do
  let stop := first + count
  let base ← blockBaseKeep dir first stop
  let mut c := initial
  for _ in [0:first * K] do
    match fullstep c with
    | some c' => c := c'
    | none => IO.println "STUCK before flat block"; return
  let dataDir := dir ++ "/FlatData"
  let segmentDir := dir ++ "/FlatSegment"
  IO.FS.createDirAll dataDir
  IO.FS.createDirAll segmentDir
  let mut dataDecls : List String := [s!"def baseKeep : ℕ := {base}\n\n"]
  for i in [first:stop] do
    let keep ← checkpointKeep dir i
    let known := c.left.drop (c.left.length - keep) |>.take (keep - base)
    dataDecls := s!"def known{i} : List Lsym := {symbolListLit (known.map lSymLit)}\n\n" ::
      dataDecls
    if i + 1 < stop then
      for _ in [0:K] do
        match fullstep c with
        | some c' => c := c'
        | none => IO.println s!"STUCK in flat block at {i}"; return
  let dataBody := s!"import Busybeaver.Deciders.Skelet.Skelet1

namespace Deciders.Skelet.Skelet1.Cert.FlatData.D{blockId}

set_option maxRecDepth 1000000

{String.join dataDecls.reverse}end Deciders.Skelet.Skelet1.Cert.FlatData.D{blockId}
"
  IO.FS.writeFile (dataDir ++ s!"/D{blockId}.lean") dataBody

  let mut imports : List String := [s!"import Skelet1Cert.FlatData.D{blockId}"]
  let firstPack := first / packSize
  let stopPack := (stop + packSize - 1) / packSize
  for p in [firstPack:stopPack] do
    imports := s!"import Skelet1Cert.Pack.P{p}" :: imports
  let mut decls : List String := []
  for i in [first:stop] do
    decls := s!"def tail{i} (rest : List Lsym) : List Lsym := D{blockId}.known{i} ++ rest\n\n" ::
      decls
    if i == first then
      decls := s!"theorem reach{i} (rest : List Lsym) :
    (C{i}.start (tail{i} rest)).lift -[M]->* (C{i}.finish (tail{i} rest)).lift :=
  C{i}.reach (tail{i} rest)

" :: decls
    else
      decls := s!"theorem bridge{i} (rest : List Lsym) :
    C{i - 1}.finish (tail{i - 1} rest) = C{i}.start (tail{i} rest) := by
  rfl

" :: decls
      decls := s!"theorem reach{i} (rest : List Lsym) :
    (C{first}.start (tail{first} rest)).lift -[M]->*
      (C{i}.finish (tail{i} rest)).lift := by
  have h := C{i}.reach (tail{i} rest)
  rw [← bridge{i} rest] at h
  exact (reach{i - 1} rest).trans h

" :: decls
  let last := stop - 1
  decls := s!"abbrev startConf (rest : List Lsym) : SConf := C{first}.start (tail{first} rest)

abbrev endConf (rest : List Lsym) : SConf := C{last}.finish (tail{last} rest)

theorem reach (rest : List Lsym) :
    (startConf rest).lift -[M]->* (endConf rest).lift :=
  reach{last} rest

" :: decls
  let segmentBody := String.intercalate "\n" imports.reverse ++
    s!"\n\nnamespace Deciders.Skelet.Skelet1.Cert.FlatSegment.S{blockId}\n\nset_option maxRecDepth 1000000\nset_option maxHeartbeats 0\n\n" ++
    String.join decls.reverse ++
    s!"end Deciders.Skelet.Skelet1.Cert.FlatSegment.S{blockId}\n"
  IO.FS.writeFile (segmentDir ++ s!"/S{blockId}.lean") segmentBody
  IO.println s!"wrote flat block {blockId}: checkpoints {first}..{stop - 1}, base {base}"

unsafe def main (args : List String) : IO Unit := do
  let mode := args[0]?.getD "profile"
  match mode with
  | "emitall" =>
    let k := (args[1]?).bind (·.toNat?) |>.getD 4992
    let dir := args[2]?.getD "Skelet1Cert"
    emitallMode k dir
  | "emitchain" =>
    let count := (args[1]?).bind (·.toNat?) |>.getD 0
    let blockSize := (args[2]?).bind (·.toNat?) |>.getD 100
    let dir := args[3]?.getD "Skelet1Cert"
    let packSize := (args[4]?).bind (·.toNat?) |>.getD 1
    emitChainMode count blockSize packSize dir
  | "emitanchors" =>
    let count := (args[1]?).bind (·.toNat?) |>.getD 0
    let blockSize := (args[2]?).bind (·.toNat?) |>.getD 200
    let k := (args[3]?).bind (·.toNat?) |>.getD 1024
    let dir := args[4]?.getD "Skelet1Cert"
    emitAnchorsMode count blockSize k dir
  | "emitchainanchored" =>
    let count := (args[1]?).bind (·.toNat?) |>.getD 0
    let blockSize := (args[2]?).bind (·.toNat?) |>.getD 200
    let dir := args[3]?.getD "Skelet1Cert"
    let packSize := (args[4]?).bind (·.toNat?) |>.getD 1
    emitAnchoredChainMode count blockSize packSize dir
  | "emitlocalanchors" =>
    let count := (args[1]?).bind (·.toNat?) |>.getD 0
    let blockSize := (args[2]?).bind (·.toNat?) |>.getD 200
    let k := (args[3]?).bind (·.toNat?) |>.getD 1024
    let dir := args[4]?.getD "Skelet1Cert"
    emitLocalAnchorsMode count blockSize k dir
  | "emitchainlocal" =>
    let count := (args[1]?).bind (·.toNat?) |>.getD 0
    let blockSize := (args[2]?).bind (·.toNat?) |>.getD 200
    let dir := args[3]?.getD "Skelet1Cert"
    let packSize := (args[4]?).bind (·.toNat?) |>.getD 1
    emitLocalChainMode count blockSize packSize dir
  | "emitflatblock" =>
    let first := (args[1]?).bind (·.toNat?) |>.getD 0
    let count := (args[2]?).bind (·.toNat?) |>.getD 100
    let k := (args[3]?).bind (·.toNat?) |>.getD 1024
    let blockId := (args[4]?).bind (·.toNat?) |>.getD 0
    let dir := args[5]?.getD "Skelet1Cert"
    let packSize := (args[6]?).bind (·.toNat?) |>.getD 4
    emitFlatBlockMode first count k blockId packSize dir
  | "pack" =>
    let count := (args[1]?).bind (·.toNat?) |>.getD 0
    let packSize := (args[2]?).bind (·.toNat?) |>.getD 8
    let dir := args[3]?.getD "Skelet1Cert"
    packMode count packSize dir
  | "packrange" =>
    let first := (args[1]?).bind (·.toNat?) |>.getD 0
    let count := (args[2]?).bind (·.toNat?) |>.getD 0
    let packSize := (args[3]?).bind (·.toNat?) |>.getD 4
    let dir := args[4]?.getD "Skelet1Cert"
    packRangeMode first count packSize dir
  | "emitrange" =>
    let first := (args[1]?).bind (·.toNat?) |>.getD 0
    let count := (args[2]?).bind (·.toNat?) |>.getD 0
    let k := (args[3]?).bind (·.toNat?) |>.getD 4992
    let dir := args[4]?.getD "Skelet1Cert"
    emitRangeMode first count k dir
  | "emitcalh" =>
    let at_ := (args[1]?).bind (·.toNat?) |>.getD 44000000
    let k := (args[2]?).bind (·.toNat?) |>.getD 10048
    let path := args[3]?.getD "/tmp/skelet1calh.lean"
    emitcalhMode at_ k path
  | "emitcal" =>
    let at_ := (args[1]?).bind (·.toNat?) |>.getD 44000000
    let k := (args[2]?).bind (·.toNat?) |>.getD 10000
    let path := args[3]?.getD "/tmp/skelet1cal.lean"
    emitcalMode at_ k path
  | "alphabet" =>
    let fuel := (args[1]?).bind (·.toNat?) |>.getD 88000000
    alphabetMode fuel
  | "dump" =>
    let at_ := (args[1]?).bind (·.toNat?) |>.getD 40000000
    let path := args[2]?.getD "/tmp/skelet1conf.txt"
    dumpMode at_ path
  | "trace" =>
    let from_ := (args[1]?).bind (·.toNat?) |>.getD 0
    let to_ := (args[2]?).bind (·.toNat?) |>.getD (from_ + 200)
    traceMode 88000000 from_ to_
  | "profile" =>
    let fuel := (args[1]?).bind (·.toNat?) |>.getD 88000000
    let report := (args[2]?).bind (·.toNat?) |>.getD 4000000
    profileMode fuel report
  | "intervals" => intervalsMode 88000000
  | "interuni" =>
    let fromUni := (args[1]?).bind (·.toNat?) |>.getD 100
    let count := (args[2]?).bind (·.toNat?) |>.getD 2
    interuniMode 88000000 fromUni count
  | "unilen" => unilenMode 300000000
  | _ => IO.println s!"unknown mode {mode}"
