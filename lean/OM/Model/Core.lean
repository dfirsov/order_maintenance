import OM.Model.Top

/-!
# Level F: the insert-only core (`prototype/core.py`)

Elements → groups → chunks, guarded label writes, group and chunk splits, the reservation
process, and FALLBACK.
-/

namespace OM.Model

/-! ### Allocation -/

def newElem (g lab h : Nat) : CM Nat := do
  let s ← get
  let i := s.E.size
  set { s with E := s.E.push { grp := g, lab := lab, h := h } }
  return i

def newGroup (c : Nat) : CM Nat := do
  let s ← get
  match s.freeG with
  | i :: rest =>
    set { s with freeG := rest, Gs := s.Gs.set! i { chk := c } }
    return i
  | [] =>
    let i := s.Gs.size
    set { s with Gs := s.Gs.push { chk := c } }
    return i

/-- Chunks are never freed: emptied ones stay as DEAD tombstones until the next rebuild. -/
def newChunk : CM Nat := do
  let s ← get
  let i := s.C.size
  set { s with C := s.C.push {} }
  return i

/-! ### Label primitives (guarded) -/

def between (a b : Nat) (why : String) : CM Nat := do
  if a + 1 ≥ b then guard why
  return (a + b) / 2

def after (a D B : Nat) (why : String) : CM Nat := do
  let v := a + D
  if v ≥ 1 <<< B || v ≤ a then guard why
  return v

def before (b D : Nat) (why : String) : CM Nat := do
  if b < D || D == 0 then guard why
  return b - D

/-! ### Queries -/

def key (e : Nat) : CM (Nat × Nat × Nat) := do
  let x ← getE e
  let g ← getG x.grp
  return ((← getC g.chk).tag, g.lab, x.lab)

def keyLt : Nat × Nat × Nat → Nat × Nat × Nat → Bool
  | (a, b, c), (a', b', c') => a < a' || (a == a' && (b < b' || (b == b' && c < c')))

def order (x y : Nat) : CM Bool := return keyLt (← key x) (← key y)

def markDead (x : Nat) : CM Unit := modE x fun e => { e with live := false }

/-! ### Chunk sizes -/

def chunkSize (c : Nat) (inc : Bool) : CM Unit := do
  let C ← getC c
  let new := if inc then C.size + 1 else C.size - 1
  modC c fun C => { C with size := new }
  if C.st == .quiet then pqAdjust c C.size new

/-! ### Element insertion -/

def insertElem (x h : Nat) : CM Nat := do
  let P ← getP
  let ex ← getE x
  let g := ex.grp
  let G ← getG g
  let lab ← if x == G.last then after ex.lab P.D_e P.B_e "elem: no room after last"
    else between ex.lab (← getE ex.next).lab "elem: no room between"
  -- mutate
  let y ← newElem g lab h
  modE y fun e => { e with prev := x, next := ex.next }
  if ex.next != NIL then modE ex.next fun e => { e with prev := y }
  modE x fun e => { e with next := y }
  if (← get).tail == x then modify fun s => { s with tail := y }
  if G.last == x then modG g fun G => { G with last := y }
  modG g fun G => { G with size := G.size + 1 }
  modify fun s => { s with count := s.count + 1 }
  chunkSize G.chk true
  return y

/-! ### Group splits -/

def startGroupSplit (g : Nat) : CM Unit := do
  let P ← getP
  let G ← getG g
  if g == NIL || !G.alive then guard "group: split of a dead group"
  let c := G.chk
  let C ← getC c
  let labL ← if g == C.first then before G.lab P.D_g "group: no room before first"
    else between (← getG G.prev).lab G.lab "group: no room left"
  let labR ← if g == C.last then after G.lab P.D_g P.B_g "group: no room after last"
    else between G.lab (← getG G.next).lab "group: no room right"
  -- mutate
  let gl ← newGroup c
  let gr ← newGroup c
  modG gl fun X => { X with lab := labL, st := .overflow, src := g, prev := G.prev, next := g }
  if G.prev != NIL then modG G.prev fun X => { X with next := gl }
  else modify fun s => { s with firstGroup := gl }
  modG gr fun X => { X with lab := labR, st := .overflow, src := g, prev := g, next := G.next }
  if G.next != NIL then modG G.next fun X => { X with prev := gr }
  modG g fun X => { X with prev := gl, next := gr, st := .splitting, l := gl, r := gr }
  if C.first == g then modC c fun X => { X with first := gl }
  if C.last == g then modC c fun X => { X with last := gr }

def removeGroup (g : Nat) : CM Unit := do
  let P ← getP
  let G ← getG g
  let c := G.chk
  let C ← getC c
  if G.prev != NIL then modG G.prev fun X => { X with next := G.next }
  else modify fun s => { s with firstGroup := G.next }
  if G.next != NIL then modG G.next fun X => { X with prev := G.prev }
  if C.first == g && C.last == g then modC c fun X => { X with first := NIL, last := NIL }
  else if C.first == g then modC c fun X => { X with first := G.next }
  else if C.last == g then modC c fun X => { X with last := G.prev }
  let mut quiet : List Nat := []
  for s in [G.l, G.r] do
    let S ← getG s
    if S.st == .overflow && S.src == g then
      modG s fun X => { X with st := .quiet, src := NIL }
      quiet := quiet ++ [s]
  modG g fun X => { X with alive := false, next := NIL, prev := NIL }
  modify fun s => { s with freeG := g :: s.freeG }
  for s in quiet do
    if (← getG s).size ≥ P.G then startGroupSplit s

/-- One move of a splitting group. Returns `false` once `g` is gone. -/
def groupSplitStep (g : Nat) : CM Bool := do
  let P ← getP
  let G ← getG g
  if g == NIL || !G.alive then guard "group split: dead group"
  if G.first == NIL then
    removeGroup g
    return false
  let gl := G.l
  let gr := G.r
  let Lg ← getG gl
  let Rg ← getG gr
  let center := 1 <<< (P.B_e - 1)
  let (e, lab, dst) ← if Lg.size ≤ Rg.size then do
      if Lg.next != g then guard "group split: left sibling not adjacent"
      let e := G.first
      let lab ← if Lg.first == NIL then pure center
        else after (← getE Lg.last).lab P.D_e P.B_e "elem: push-back room"
      -- mutate
      if G.first == G.last then modG g fun X => { X with first := NIL, last := NIL }
      else
        let nx := (← getE e).next
        modG g fun X => { X with first := nx }
      if Lg.first == NIL then modG gl fun X => { X with first := e }
      modG gl fun X => { X with last := e }
      pure (e, lab, gl)
    else do
      if Rg.prev != g then guard "group split: right sibling not adjacent"
      let e := G.last
      let lab ← if Rg.first == NIL then pure center
        else before (← getE Rg.first).lab P.D_e "elem: push-front room"
      if G.first == G.last then modG g fun X => { X with first := NIL, last := NIL }
      else
        let pv := (← getE e).prev
        modG g fun X => { X with last := pv }
      if Rg.first == NIL then modG gr fun X => { X with last := e }
      modG gr fun X => { X with first := e }
      pure (e, lab, gr)
  modE e fun X => { X with grp := dst, lab := lab }
  modG g fun X => { X with size := X.size - 1 }
  modG dst fun X => { X with size := X.size + 1 }
  let D ← getG dst
  if D.chk != G.chk then
    -- unreachable under invariant F (family moves)
    chunkSize D.chk true
    chunkSize G.chk false
  return true

def driveGroupFrom (s : Nat) : CM Unit := do
  for _ in List.range ((← getP).K_G) do
    if !(← groupSplitStep s) then return

def driveGroup (g : Nat) : CM Unit := do
  let G ← getG g
  match G.st with
  | .splitting => driveGroupFrom g
  | .overflow => driveGroupFrom G.src
  | _ => pure ()

/-! ### Chunk splits -/

/-- The groups that one chunk-split move takes from the left/right end of chunk `x`: a whole
family `(gl, g, gr)` of a splitting group, or one group (invariant F). -/
def unit (x : Nat) (left : Bool) : CM (List Nat) := do
  let X ← getC x
  let g0 := if left then X.first else X.last
  let G0 ← getG g0
  if G0.st != .overflow then return [g0]
  let S ← getG G0.src
  let u := if left && S.l == g0 then [g0, G0.src, S.r]
    else if !left && S.r == g0 then [S.l, G0.src, g0]
    else [g0]
  if u.length == 1 then return u
  for (a, b) in u.zip u.tail do
    if (← getG a).next != b || (← getG b).chk != x then
      guard "chunk split: family not contiguous in chunk"
  return u

def removeChunk (x : Nat) : CM Unit := do
  modC x fun X => { X with st := .dead }
  let X ← getC x
  for s in [X.l, X.r] do
    let S ← getC s
    if S.st == .overflow && S.src == x then
      modC s fun X => { X with st := .quiet, src := NIL }
      pqEnterIfAbove s

def chunkSplitStep (x : Nat) : CM Bool := do
  let P ← getP
  let X ← getC x
  if X.first == NIL then
    removeChunk x
    return false
  let y := X.l
  let z := X.r
  let Y ← getC y
  let Z ← getC z
  let center := 1 <<< (P.B_g - 1)
  let left := Y.size ≤ Z.size
  let u ← unit x left
  let mut labs : List Nat := []
  if left then
    if Y.next != x then guard "chunk split: left sibling not adjacent"
    let yl := (← getG Y.last).lab
    let mut prev : Option Nat := if Y.first == NIL then none else some yl
    for _ in u do
      let l ← match prev with
        | none => pure center
        | some p => after p P.D_g P.B_g "group: push-back room"
      prev := some l
      labs := labs ++ [l]
  else
    if Z.prev != x then guard "chunk split: right sibling not adjacent"
    let zf := (← getG Z.first).lab
    let mut nxt : Option Nat := if Z.first == NIL then none else some zf
    for _ in u do
      let l ← match nxt with
        | none => pure center
        | some n => before n P.D_g "group: push-front room"
      nxt := some l
      labs := labs ++ [l]
    labs := labs.reverse
  -- mutate
  let first := u.headD NIL
  let last := u.getLastD NIL
  let dst ← if left then do
      if X.last == last then modC x fun X => { X with first := NIL, last := NIL }
      else
        let nx := (← getG last).next
        modC x fun X => { X with first := nx }
      if Y.first == NIL then modC y fun X => { X with first := first }
      modC y fun X => { X with last := last }
      pure y
    else do
      if X.first == first then modC x fun X => { X with first := NIL, last := NIL }
      else
        let pv := (← getG first).prev
        modC x fun X => { X with last := pv }
      if Z.first == NIL then modC z fun X => { X with last := last }
      modC z fun X => { X with first := first }
      pure z
  let mut moved := 0
  for (gg, lab) in u.zip labs do
    modG gg fun X => { X with chk := dst, lab := lab }
    moved := moved + (← getG gg).size
  -- x is SPLITTING and dst is OVERFLOW: neither is in the priority queue
  modC x fun X => { X with size := X.size - moved }
  modC dst fun X => { X with size := X.size + moved }
  return true

def driveChunkFrom (s : Nat) : CM Unit := do
  for _ in List.range ((← getP).K_C) do
    if !(← chunkSplitStep s) then return

def driveChunk (c : Nat) : CM Unit := do
  let C ← getC c
  match C.st with
  | .splitting => driveChunkFrom c
  | .overflow => driveChunkFrom C.src
  | _ => pure ()

/-! ### Reservation -/

def reservation (k : Nat) : CM Unit := do
  for _ in List.range (k) do
    match (← get).resJob with
    | none =>
      if ← pqEmpty then return
      let x ← pqPopMax
      if x == NIL || x ≥ (← get).C.size then guard "reservation: invalid chunk"
      let y ← newChunk
      let z ← newChunk
      let X ← getC x
      modC y fun C => { C with prev := X.prev, next := x }
      if X.prev != NIL then modC X.prev fun C => { C with next := y }
      else modify fun s => { s with firstChunk := y }
      modC z fun C => { C with prev := x, next := X.next }
      if X.next != NIL then modC X.next fun C => { C with prev := z }
      modC x fun C => { C with prev := y, next := z }
      let job ← insertAround x y z
      modC x fun C => { C with st := .splitting, l := y, r := z }
      modC y fun C => { C with st := .overflow, src := x }
      modC z fun C => { C with st := .overflow, src := x }
      modify fun s => { s with resJob := some job }
    | some job =>
      let r ← jobStep job
      modify fun s => { s with resJob := r }

/-! ### FALLBACK -/

/-- The element list, from the sentinel. -/
def elements : CM (List Nat) := do
  let s ← get
  let mut out : Array Nat := #[]
  let mut e := s.head
  for _ in List.range (s.E.size) do
    if e == NIL then break
    out := out.push e
    e := (s.E.getX e).next
  return out.toList

/-- Synchronous rebuild of groups, chunks and tags from the element list. -/
def fallback : CM Unit := do
  let P ← getP
  modify fun s => { s with fallbacks := s.fallbacks + 1 }
  let seq ← elements
  modify fun s => { s with
    Gs := #[default], C := #[default], freeG := [],
    pqHead := #[], pqNext := #[], pqPrev := #[], pqWhere := #[], nbNext := #[], nbPrev := #[],
    pqHi := 0, pqLo := 0, resJob := none }
  let gs := max 1 (P.G / 2)
  let gpc := max 1 ((P.T / 2) / gs)
  let chunks := chunksOf gpc (chunksOf gs seq)
  let mut prevC := NIL
  let mut prevG := NIL
  for cgroups in chunks do
    let c ← newChunk
    modC c fun C => { C with prev := prevC }
    if prevC != NIL then modC prevC fun C => { C with next := c }
    let stepG := (1 <<< P.B_g) / (cgroups.length + 1)
    let mut j := 0
    for elems in cgroups do
      let g ← newGroup c
      modG g fun G => { G with lab := (j + 1) * stepG, prev := prevG }
      if prevG != NIL then modG prevG fun G => { G with next := g }
      let stepE := (1 <<< P.B_e) / (elems.length + 1)
      let mut k := 0
      for el in elems do
        modE el fun e => { e with grp := g, lab := (k + 1) * stepE }
        k := k + 1
      modG g fun G => { G with
        first := elems.headD NIL, last := elems.getLastD NIL,
        size := elems.length }
      if j == 0 then modC c fun C => { C with first := g }
      modC c fun C => { C with last := g, size := C.size + elems.length }
      prevG := g
      j := j + 1
    prevC := c
  modify fun s => { s with firstChunk := 1, firstGroup := 1 }
  relabelAll

/-! ### Insertion with background work -/

def background (y : Nat) : CM Unit := do
  let P ← getP
  let g := (← getE y).grp
  let G ← getG g
  if G.st == .quiet && G.size ≥ P.G then startGroupSplit g
  driveGroup (← getE y).grp
  driveChunk (← getG (← getE y).grp).chk
  reservation P.K_R

/-- Run `act`; on a failed guard run `handler` from the state reached (bugs propagate). -/
def onGuard {α : Type} (act : CM α) (handler : CM α) : CM α :=
  tryCatch act fun
    | .guard _ => handler
    | e => throw e

def insertAfter (x h : Nat) : CM Nat := do
  let y ← onGuard (insertElem x h) (do fallback; insertElem x h)
  onGuard (background y) fallback
  return y

/-! ### Construction -/

/-- A fresh core (`Core.__init__`). With `lazy`, the top structure is built later, one
`prepareStep` at a time. -/
def initCore (lazy : Bool) : CM Unit := do
  let P ← getP
  let c ← newChunk
  let g ← newGroup c
  modify fun s => { s with
    prep := some { chunk := c, below := c, path := Array.replicate (P.H + 1) NIL } }
  if lazy then
    modify fun s => { s with ready := false }
  else
    for _ in List.range (P.H + 1) do
      if ← initStep then break
    modify fun s => { s with ready := true }
  modG g fun G => { G with lab := 1 <<< (P.B_g - 1) }
  modC c fun C => { C with first := g, last := g }
  let hd ← newElem g (1 <<< (P.B_e - 1)) 0
  modE hd fun e => { e with live := false }
  modG g fun G => { G with first := hd, last := hd, size := 1 }
  modC c fun C => { C with size := 1 }
  modify fun s => { s with firstGroup := g, firstChunk := c, tail := hd, head := hd, count := 1 }

/-- One step of deferred initialization; `true` once the core is ready. -/
def prepareStep : CM Bool := do
  if !(← get).ready then
    if ← initStep then modify fun s => { s with ready := true }
  return (← get).ready

end OM.Model
