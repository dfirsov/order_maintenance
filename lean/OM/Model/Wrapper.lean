import OM.Model.Core
import OM.Spec

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
  if e.live then
    let (y, n') ← runCore nxt (insertAfter nxt.tail e.h)
    return ({ om with nxtIdx := om.nxtIdx.setX e.h y, cursor := e.next }, n')
  else
    return ({ om with cursor := e.next }, nxt)

/-- `nxt` replaces `cur`. -/
def OM.swap (om : OM) (nxt : Core) : OM :=
  { om with cur := nxt, curIdx := om.nxtIdx, nxt := none, nxtIdx := #[] }

/-- The rebuild loop, with `budget` steps left: each iteration spends one unit, except the one
that sets the cursor (`fuel` bounds the iterations). -/
def rebuildLoop (om : OM) (nxt : Core) : Nat → Nat → WM OM
  | 0, _ => return { om with nxt := some nxt }
  | fuel + 1, budget =>
    if budget = 0 then return { om with nxt := some nxt }
    else if !om.cursorSet then do
      let (ready, n') ← runCore nxt prepareStep
      if ready then
        rebuildLoop { om with cursor := (om.cur.E.getX om.cur.head).next, cursorSet := true } n'
          fuel budget
      else rebuildLoop om n' fuel (budget - 1)
    else if om.cursor = NIL then return om.swap nxt
    else do
      let (om', n') ← copyAtCursor om nxt
      if om'.cursor = NIL then return om'.swap n'
      else rebuildLoop om' n' fuel (budget - 1)

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
  | some nxt0 => rebuildLoop { om with nxt := none } nxt0 (om.KB + 1) om.KB

/-- Mirror an insertion into `nxt`, if its anchor is already copied. -/
def OM.mirrorInsert (om : OM) (hx : Option Nat) (hy : Nat) : WM OM :=
  match om.nxt with
  | none => return om
  | some nxt =>
    let copied := match hx with
      | none => true
      | some x => om.nxtIdx.getX x != 0
    if om.cursorSet && copied then do
      let om := { om with nxt := none }
      let xn := match hx with
        | none => nxt.head
        | some x => om.nxtIdx.getX x
      let (y', n') ← runCore nxt (insertAfter xn hy)
      return { om with nxt := some n', nxtIdx := om.nxtIdx.setX hy y' }
    else return om

/-- Mirror a deletion into `nxt`, if the element is already copied. -/
def OM.mirrorDelete (om : OM) (x : Nat) : WM OM :=
  match om.nxt with
  | none => return om
  | some nxt =>
    let xn := om.nxtIdx.getX x
    if xn != 0 then do
      let om := { om with nxt := none }
      let (_, n') ← runCore nxt (markDead xn)
      return { om with nxt := some n', nxtIdx := om.nxtIdx.setX x 0 }
    else return om

def OM.insert (mk : Nat → Params) (om : OM) (hx : Option Nat) : WM (Nat × OM) := do
  let hy := om.nextHandle
  let xi := match hx with
    | none => om.cur.head
    | some x => om.curIdx.getX x
  let (y, om) ← om.onCur (insertAfter xi hy)
  let om ← { om with nextHandle := hy + 1, curIdx := om.curIdx.setX hy y }.mirrorInsert hx hy
  return (hy, ← { om with live := om.live + 1 }.rebuildStep mk)

def OM.delete (mk : Nat → Params) (om : OM) (x : Nat) : WM OM := do
  let (_, om) ← om.onCur (markDead (om.curIdx.getX x))
  let om ← { om with curIdx := om.curIdx.setX x 0 }.mirrorDelete x
  { om with live := om.live - 1 }.rebuildStep mk

def OM.order (om : OM) (x y : Nat) : WM Bool :=
  Prod.fst <$> runCore om.cur (OM.Model.order (om.curIdx.getX x) (om.curIdx.getX y))

/-- One operation of the specification's interface. The `k`-th insertion returns handle `k`,
which is the specification's name for the new element. -/
def OM.apply (mk : Nat → Params) (om : OM) : _root_.OM.Spec.Op → WM (_root_.OM.Spec.Ans × OM)
  | .insertFirst => do
    let (_, om) ← om.insert mk none
    return (.inserted, om)
  | .insertAfter x => do
    let (_, om) ← om.insert mk (some x)
    return (.inserted, om)
  | .delete x => do
    let om ← om.delete mk x
    return (.deleted, om)
  | .order x y => do
    let b ← om.order x y
    return (.bool b, om)

/-- The answers to a sequence of operations. -/
def OM.runOps (mk : Nat → Params) : OM → List _root_.OM.Spec.Op → WM (List _root_.OM.Spec.Ans)
  | _, [] => pure []
  | om, op :: ops => do
    let (a, om) ← om.apply mk op
    let as ← OM.runOps mk om ops
    return a :: as

end OM.Model
