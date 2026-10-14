import OM.Model.Core

/-!
# Level F: the full structure (`prototype/wrapper.py`)

Deletion by tombstones and growth by incremental global rebuilding on top of the insert-only
core. `cur` answers all queries. When `cur` is half full, or too few of its elements are live,
a fresh core `nxt` is prepared and then filled in the background, `K_B` steps per operation.

Handles are the insertion counter, so the `k`-th insertion returns handle `k`, exactly the
element names of `OM.Spec`.

The parameters of a new core are given by a function `mk : Nat → Params` of the capacity.
-/

namespace OM.Model

def N_MIN : Nat := 64

structure OM where
  cur : Core
  /-- Handle → element index in `cur` (0: absent). -/
  curIdx : Array Nat := #[]
  nxt : Option Core := none
  nxtIdx : Array Nat := #[]
  cursor : Nat := NIL
  /-- Copying starts only once `nxt` is fully prepared. -/
  cursorSet : Bool := false
  live : Nat := 0
  nextHandle : Nat := 0
  rebuilds : Nat := 0
  KB : Nat
  deriving Inhabited

abbrev WM := Except Err

def runCore {α : Type} (c : Core) (act : CM α) : WM (α × Core) :=
  match act.run c with
  | .ok a s => .ok (a, s)
  | .error e _ => .error e

/-- Run a core action on `cur`. The core is moved out of `om` first, so that its arrays stay
unshared and are updated in place by compiled code. -/
def OM.onCur {α : Type} (om : OM) (act : CM α) : WM (α × OM) := do
  let cur := om.cur
  let om := { om with cur := default }
  let (a, cur) ← runCore cur act
  return (a, { om with cur := cur })

def newCore (P : Params) (lazy : Bool) : WM Core :=
  Prod.snd <$> runCore { P := P } (initCore lazy)

def OM.init (mk : Nat → Params) (KB : Nat) : WM OM := do
  return { cur := ← newCore (mk N_MIN) false, KB := KB }

/-- Capacity of the next core (`docs/PROOF.md` §2.7, Lemma W). -/
def OM.nextCapacity (om : OM) : Nat :=
  let prep := om.cur.P.L + 2
  let mirrored := (om.cur.count + prep) / (om.KB - 1) + 1
  4 * max (om.live + mirrored) 16

/-- Copy one element of `cur` at the cursor into `nxt`, if it is live. -/
def copyAtCursor (om : OM) (nxt : Core) : WM (OM × Core) := do
  let e := om.cur.E.getX om.cursor
  let mut om := om
  let mut nxt := nxt
  if e.live then
    if om.nxtIdx.getX e.h != 0 then throw (.bug "cursor met an already-copied element")
    let (y, n') ← runCore nxt (insertAfter nxt.tail e.h)
    nxt := n'
    om := { om with nxtIdx := om.nxtIdx.setX e.h y }
  return ({ om with cursor := e.next }, nxt)

/-- The rebuild's share of one operation: exactly `K_B` steps (`wrapper.py` `_rebuild_step`). -/
def OM.rebuildStep (mk : Nat → Params) (om : OM) : WM OM := do
  match om.nxt with
  | none =>
    let N := om.cur.P.N
    if om.cur.count ≥ N / 2 || (N > N_MIN && om.live < N / 8) then
      let nxt ← newCore (mk om.nextCapacity) true
      return { om with nxt := some nxt, nxtIdx := #[], cursorSet := false,
                       rebuilds := om.rebuilds + 1 }
    return om
  | some nxt0 =>
    let mut om := { om with nxt := none }
    let mut nxt := nxt0
    let mut budget := om.KB
    -- each iteration spends one unit of budget, except the one that sets the cursor
    for _ in [0:om.KB + 1] do
      if budget == 0 then break
      if !om.cursorSet then
        let (ready, n') ← runCore nxt prepareStep
        nxt := n'
        if ready then
          om := { om with cursor := (om.cur.E.getX om.cur.head).next, cursorSet := true }
        else
          budget := budget - 1
        continue
      if om.cursor != NIL then
        let (om', n') ← copyAtCursor om nxt
        om := om'
        nxt := n'
        budget := budget - 1
      if om.cursor == NIL then
        -- swap: nxt replaces cur
        return { om with cur := nxt, curIdx := om.nxtIdx, nxt := none, nxtIdx := #[] }
    return { om with nxt := some nxt }

def OM.insert (mk : Nat → Params) (om : OM) (hx : Option Nat) : WM (Nat × OM) := do
  let hy := om.nextHandle
  let xi := match hx with
    | none => om.cur.head
    | some x => om.curIdx.getX x
  let (y, om) ← om.onCur (insertAfter xi hy)
  let mut om := { om with nextHandle := hy + 1, curIdx := om.curIdx.setX hy y }
  if let some nxt := om.nxt then
    let copied := match hx with
      | none => true
      | some x => om.nxtIdx.getX x != 0
    if om.cursorSet && copied then
      om := { om with nxt := none }
      let xn := match hx with
        | none => nxt.head
        | some x => om.nxtIdx.getX x
      let (y', n') ← runCore nxt (insertAfter xn hy)
      om := { om with nxt := some n', nxtIdx := om.nxtIdx.setX hy y' }
  om := { om with live := om.live + 1 }
  return (hy, ← om.rebuildStep mk)

def OM.delete (mk : Nat → Params) (om : OM) (x : Nat) : WM OM := do
  let (_, om) ← om.onCur (markDead (om.curIdx.getX x))
  let mut om := { om with curIdx := om.curIdx.setX x 0 }
  if let some nxt := om.nxt then
    let xn := om.nxtIdx.getX x
    if xn != 0 then
      om := { om with nxt := none }
      let (_, n') ← runCore nxt (markDead xn)
      om := { om with nxt := some n', nxtIdx := om.nxtIdx.setX x 0 }
  om := { om with live := om.live - 1 }
  om.rebuildStep mk

def OM.order (om : OM) (x y : Nat) : WM Bool :=
  Prod.fst <$> runCore om.cur (OM.Model.order (om.curIdx.getX x) (om.curIdx.getX y))

end OM.Model
