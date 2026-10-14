import OM.Model.Top

/-!
# Level F: the insert-only core (`prototype/core.py`)

Elements → groups → chunks, guarded label writes, group and chunk splits, the reservation
process, and FALLBACK.
-/

namespace OM.Model

/-! ### Allocation -/

def newElem (g lab h : Nat) : CM Nat :=
  modifyGet fun s => (s.E.size, { s with E := s.E.push { grp := g, lab := lab, h := h } })

def newGroup (c : Nat) : CM Nat :=
  modifyGet fun s => match s.freeG with
    | i :: rest => (i, { s with freeG := rest, Gs := s.Gs.set! i { chk := c } })
    | [] => (s.Gs.size, { s with Gs := s.Gs.push { chk := c } })

/-- Chunks are never freed: emptied ones stay as DEAD tombstones until the next rebuild. -/
def newChunk : CM Nat :=
  modifyGet fun s => (s.C.size, { s with C := s.C.push {} })

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

/-- Link a new element `y` (the next free index) with label `lab` and handle `h` right after
`x`, in `x`'s group. -/
def linkElem (s : Core) (x y lab h : Nat) : Core :=
  let ex := s.E.getX x
  let g := ex.grp
  let E1 := s.E.push { grp := g, lab := lab, h := h, prev := x, next := ex.next }
  let E2 := if ex.next != NIL then E1.modify ex.next (fun e => { e with prev := y }) else E1
  { s with
    E := E2.modify x (fun e => { e with next := y })
    tail := if s.tail == x then y else s.tail
    Gs := s.Gs.modify g (fun G => { G with last := if G.last == x then y else G.last,
                                            size := G.size + 1 })
    count := s.count + 1 }

def insertElem (x h : Nat) : CM Nat := do
  let P ← getP
  let ex ← getE x
  let g := ex.grp
  let G ← getG g
  let lab ← if x == G.last then after ex.lab P.D_e P.B_e "elem: no room after last"
    else between ex.lab (← getE ex.next).lab "elem: no room between"
  -- mutate (the chunk's size is updated by `background`, so that nothing after the
  -- mutation can fail a guard: the caller retries the insertion only on such a failure)
  let y := (← get).E.size
  modify (linkElem · x y lab h)
  return y

/-! ### Group splits -/

/-- Link new groups `gl` (label `labL`) and `gr` (label `labR`) right before and after `g`, in
the group list and in `g`'s chunk, as the overflow siblings of `g`. -/
def linkGroupPair (s : Core) (g gl gr labL labR : Nat) : Core :=
  let G := s.Gs.getX g
  let c := G.chk
  let C := s.C.getX c
  let A0 := s.Gs.modify gl fun X =>
    { X with lab := labL, st := .overflow, src := g, prev := G.prev, next := g }
  let A1 := if G.prev != NIL then A0.modify G.prev (fun X => { X with next := gl }) else A0
  let A2 := A1.modify gr fun X =>
    { X with lab := labR, st := .overflow, src := g, prev := g, next := G.next }
  let A3 := if G.next != NIL then A2.modify G.next (fun X => { X with prev := gr }) else A2
  let C1 := if C.first == g then s.C.modify c (fun X => { X with first := gl }) else s.C
  { s with
    Gs := A3.modify g fun X => { X with prev := gl, next := gr, st := .splitting, l := gl, r := gr }
    C := if C.last == g then C1.modify c (fun X => { X with last := gr }) else C1
    firstGroup := if G.prev != NIL then s.firstGroup else gl }

/-- Unlink group `g` from the group list and from its chunk, and free it. -/
def unlinkGroup (s : Core) (g : Nat) : Core :=
  let G := s.Gs.getX g
  let c := G.chk
  let C := s.C.getX c
  let A1 := if G.prev != NIL then s.Gs.modify G.prev (fun X => { X with next := G.next }) else s.Gs
  let A2 := if G.next != NIL then A1.modify G.next (fun X => { X with prev := G.prev }) else A1
  { s with
    Gs := A2.modify g fun X => { X with alive := false, next := NIL, prev := NIL }
    C := if C.first == g && C.last == g then s.C.modify c (fun X => { X with first := NIL, last := NIL })
      else if C.first == g then s.C.modify c (fun X => { X with first := G.next })
      else if C.last == g then s.C.modify c (fun X => { X with last := G.prev })
      else s.C
    firstGroup := if G.prev != NIL then s.firstGroup else G.next
    freeG := g :: s.freeG }

/-- Move element `e`, the first of group `g`, to the end of group `gl` with label `lab`. -/
def moveFirstLeft (s : Core) (g gl e lab : Nat) : Core :=
  let G := s.Gs.getX g
  let A1 := s.Gs.modify g fun X =>
    if G.first == G.last then { X with first := NIL, last := NIL }
    else { X with first := (s.E.getX e).next }
  { s with
    Gs := A1.modify gl fun X => { X with first := if X.first == NIL then e else X.first, last := e }
    E := s.E.modify e fun X => { X with grp := gl, lab := lab } }

/-- Move element `e`, the last of group `g`, to the front of group `gr` with label `lab`. -/
def moveLastRight (s : Core) (g gr e lab : Nat) : Core :=
  let G := s.Gs.getX g
  let A1 := s.Gs.modify g fun X =>
    if G.first == G.last then { X with first := NIL, last := NIL }
    else { X with last := (s.E.getX e).prev }
  { s with
    Gs := A1.modify gr fun X => { X with last := if X.first == NIL then e else X.last, first := e }
    E := s.E.modify e fun X => { X with grp := gr, lab := lab } }

/-- A label for a new group right before `g` in its chunk. -/
def labBefore (g : Nat) : CM Nat := do
  let P ← getP
  let G ← getG g
  let C ← getC G.chk
  if g == C.first then before G.lab P.D_g "group: no room before first"
  else between (← getG G.prev).lab G.lab "group: no room left"

/-- A label for a new group right after `g` in its chunk. -/
def labAfter (g : Nat) : CM Nat := do
  let P ← getP
  let G ← getG g
  let C ← getC G.chk
  if g == C.last then after G.lab P.D_g P.B_g "group: no room after last"
  else between G.lab (← getG G.next).lab "group: no room right"

def startGroupSplit (g : Nat) : CM Unit := do
  let G ← getG g
  require (g != NIL && g < (← get).Gs.size && G.alive) "group: split of a dead group"
  let labL ← labBefore g
  let labR ← labAfter g
  -- mutate
  let gl ← newGroup G.chk
  let gr ← newGroup G.chk
  modify (linkGroupPair · g gl gr labL labR)

def removeGroup (g : Nat) : CM Unit := do
  let P ← getP
  let G ← getG g
  modify (unlinkGroup · g)
  let mut quiet : List Nat := []
  for s in [G.l, G.r] do
    let S ← getG s
    if S.st == .overflow && S.src == g then
      modG s fun X => { X with st := .quiet, src := NIL }
      quiet := quiet ++ [s]
  for s in quiet do
    if (← getG s).size ≥ P.G then startGroupSplit s

/-- One move of a splitting group. Returns `false` once `g` is gone. -/
def groupSplitStep (g : Nat) : CM Bool := do
  let P ← getP
  let G ← getG g
  require (g != NIL && g < (← get).Gs.size && G.alive) "group split: dead group"
  if G.first == NIL then
    removeGroup g
    return false
  let gl := G.l
  let gr := G.r
  let Lg ← getG gl
  let Rg ← getG gr
  let center := 1 <<< (P.B_e - 1)
  let dst ← if Lg.size ≤ Rg.size then do
      require (Lg.next == g) "group split: left sibling not adjacent"
      let lab ← if Lg.first == NIL then pure center
        else after (← getE Lg.last).lab P.D_e P.B_e "elem: push-back room"
      modify (moveFirstLeft · g gl G.first lab)
      pure gl
    else do
      require (Rg.prev == g) "group split: right sibling not adjacent"
      let lab ← if Rg.first == NIL then pure center
        else before (← getE Rg.first).lab P.D_e "elem: push-front room"
      modify (moveLastRight · g gr G.last lab)
      pure gr
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

/-- Labels for `k` groups appended after a group labelled `prev` (`none`: the receiving chunk
is empty; start at the centre). -/
def pushBackLabs (center D B : Nat) : Option Nat → Nat → CM (List Nat)
  | _, 0 => pure []
  | prev, k + 1 => do
    let l ← match prev with
      | none => pure center
      | some p => after p D B "group: push-back room"
    return l :: (← pushBackLabs center D B (some l) k)

/-- Labels for `k` groups prepended before a group labelled `nxt`, in list order. -/
def pushFrontLabs (center D : Nat) : Option Nat → Nat → CM (List Nat)
  | _, 0 => pure []
  | nxt, k + 1 => do
    let l ← match nxt with
      | none => pure center
      | some n => before n D "group: push-front room"
    return (← pushFrontLabs center D (some l) k) ++ [l]

/-- Move the groups `u`, a prefix of chunk `x`, to the end of chunk `y`, with labels `labs`. -/
def moveGroupsLeft (s : Core) (x y : Nat) (u labs : List Nat) : Core :=
  let X := s.C.getX x
  let first := u.headD NIL
  let last := u.getLastD NIL
  let C1 := s.C.modify x fun Z =>
    if X.last == last then { Z with first := NIL, last := NIL }
    else { Z with first := (s.Gs.getX last).next }
  { s with
    C := C1.modify y fun Z => { Z with first := if Z.first == NIL then first else Z.first, last := last }
    Gs := (u.zip labs).foldl (fun a p => a.modify p.1 fun G => { G with chk := y, lab := p.2 }) s.Gs }

/-- Move the groups `u`, a suffix of chunk `x`, to the front of chunk `z`, with labels `labs`. -/
def moveGroupsRight (s : Core) (x z : Nat) (u labs : List Nat) : Core :=
  let X := s.C.getX x
  let first := u.headD NIL
  let last := u.getLastD NIL
  let C1 := s.C.modify x fun Z =>
    if X.first == first then { Z with first := NIL, last := NIL }
    else { Z with last := (s.Gs.getX first).prev }
  { s with
    C := C1.modify z fun Z => { Z with last := if Z.first == NIL then last else Z.last, first := first }
    Gs := (u.zip labs).foldl (fun a p => a.modify p.1 fun G => { G with chk := z, lab := p.2 }) s.Gs }

/-- Chunk sizes after moving the groups `u` from `x` to `dst`. -/
def moveSizes (x dst : Nat) (u : List Nat) : CM Unit := do
  let s ← get
  let moved := (u.map fun g => (s.Gs.getX g).size).sum
  -- x is SPLITTING and dst is OVERFLOW: neither is in the priority queue
  modC x fun X => { X with size := X.size - moved }
  modC dst fun X => { X with size := X.size + moved }

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
  if left then
    require (Y.next == x) "chunk split: left sibling not adjacent"
    let yl := (← getG Y.last).lab
    let labs ← pushBackLabs center P.D_g P.B_g (if Y.first == NIL then none else some yl) u.length
    modify (moveGroupsLeft · x y u labs)
    moveSizes x y u
  else
    require (Z.prev == x) "chunk split: right sibling not adjacent"
    let zf := (← getG Z.first).lab
    let labs ← pushFrontLabs center P.D_g (if Z.first == NIL then none else some zf) u.length
    modify (moveGroupsRight · x z u labs)
    moveSizes x z u
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

/-- Link new chunks `y` and `z` right before and after `x` in the chunk list. -/
def linkChunkPair (s : Core) (x y z : Nat) : Core :=
  let X := s.C.getX x
  let C1 := s.C.modify y (fun C => { C with prev := X.prev, next := x })
  let C2 := if X.prev != NIL then C1.modify X.prev (fun C => { C with next := y }) else C1
  let C3 := C2.modify z (fun C => { C with prev := x, next := X.next })
  let C4 := if X.next != NIL then C3.modify X.next (fun C => { C with prev := z }) else C3
  { s with
    C := C4.modify x (fun C => { C with prev := y, next := z })
    firstChunk := if X.prev != NIL then s.firstChunk else y }

def reservation (k : Nat) : CM Unit := do
  for _ in List.range (k) do
    match (← get).resJob with
    | none =>
      if ← pqEmpty then return
      let x ← pqPopMax
      require (x != NIL && x < (← get).C.size) "reservation: invalid chunk"
      let y ← newChunk
      let z ← newChunk
      modify (linkChunkPair · x y z)
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
  chunkSize (← getG (← getE y).grp).chk true
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
