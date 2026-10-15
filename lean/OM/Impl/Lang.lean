import OM.Model.Wrapper
import OM.Machine.Logic

/-!
# M6: the core language

A small language for the core's code, with two semantics:
* `evalF` runs on Level F's `Core` (this file);
* `compile` translates to a machine `Stmt` over a fixed memory layout (`Compile.lean`).

`Sim.lean` proves once that the two agree, with the machine cost computed from the source.
Each Level F function is then written in this language, and an agreement lemma shows that
`evalF` computes what the Level F function computes.

All values are `Nat`. A record field is read as a number: `Bool` fields as 0/1 (with `dead`
for `alive`, so that every default record reads 0), `St` as 0–3. A write that the encoding
cannot represent (a `Bool` field set to 5, an index past the capacity) is a **bug** of the
source program: `evalF` returns `.bug`, and the agreement lemmas show that it never happens.
-/

namespace OM.Impl

open OM.Model
open OM.Machine (Reg BinOp UnOp)

/-! ### Encodings of small types -/

def b2n (b : Bool) : Nat := if b then 1 else 0

def _root_.OM.Model.St.toN : St → Nat
  | .quiet => 0 | .overflow => 1 | .splitting => 2 | .dead => 3

def _root_.OM.Model.St.ofN : Nat → St
  | 0 => .quiet | 1 => .overflow | 2 => .splitting | _ => .dead

theorem _root_.OM.Model.St.ofN_toN (x : St) : St.ofN x.toN = x := by cases x <;> rfl
theorem _root_.OM.Model.St.toN_ofN {v : Nat} (h : v ≤ 3) : (St.ofN v).toN = v := by
  rcases v with _ | _ | _ | _ | v <;> first | rfl | omega

/-! ### Fields -/

inductive EF | next | prev | grp | lab | dead | h
  deriving DecidableEq, Repr
inductive GF | next | prev | first | last | chk | lab | size | st | src | l | r | dead
  deriving DecidableEq, Repr
inductive CF | next | prev | first | last | size | st | src | l | r | tag | dead
  deriving DecidableEq, Repr
inductive NF | height | livePar | weight | first | last | draining | t1 | t2 | overflow | dead
  deriving DecidableEq, Repr
/-- Plain arrays of numbers, extended on write (`Array.setX`). -/
inductive AF | pqHead | pqNext | pqPrev | pqWhere | nbNext | nbPrev | lpar
  deriving DecidableEq, Repr
/-- Scalars of the core. -/
inductive SF | count | head | tail | firstGroup | firstChunk | notReady | fallbacks | pqHi | pqLo
  | pqScan
  deriving DecidableEq, Repr
/-- Record counts (read only; `push` extends them). -/
inductive Tbl | E | G | C | N
  deriving DecidableEq, Repr
/-- Parameters (read only). -/
inductive PF | N | L | G | T | theta | Be | Bg | De | Dg | KG | KC | KR | a | s | beta | H
  deriving DecidableEq, Repr

inductive Fld
  | e (k : EF) | g (k : GF) | c (k : CF) | n (k : NF) | a (k : AF) | s (k : SF)
  deriving DecidableEq, Repr

section fields

def EF.get (x : Elem) : EF → Nat
  | .next => x.next | .prev => x.prev | .grp => x.grp | .lab => x.lab
  | .dead => b2n !x.live | .h => x.h

def EF.set (x : Elem) (v : Nat) : EF → Elem
  | .next => { x with next := v } | .prev => { x with prev := v } | .grp => { x with grp := v }
  | .lab => { x with lab := v } | .dead => { x with live := v == 0 } | .h => { x with h := v }

def EF.ok (v : Nat) : EF → Bool
  | .dead => decide (v ≤ 1) | _ => true

def GF.get (x : Group) : GF → Nat
  | .next => x.next | .prev => x.prev | .first => x.first | .last => x.last | .chk => x.chk
  | .lab => x.lab | .size => x.size | .st => x.st.toN | .src => x.src | .l => x.l | .r => x.r
  | .dead => b2n !x.alive

def GF.set (x : Group) (v : Nat) : GF → Group
  | .next => { x with next := v } | .prev => { x with prev := v } | .first => { x with first := v }
  | .last => { x with last := v } | .chk => { x with chk := v } | .lab => { x with lab := v }
  | .size => { x with size := v } | .st => { x with st := St.ofN v } | .src => { x with src := v }
  | .l => { x with l := v } | .r => { x with r := v } | .dead => { x with alive := v == 0 }

def GF.ok (v : Nat) : GF → Bool
  | .st => v ≤ 3 | .dead => decide (v ≤ 1) | _ => true

def CF.get (x : Chunk) : CF → Nat
  | .next => x.next | .prev => x.prev | .first => x.first | .last => x.last | .size => x.size
  | .st => x.st.toN | .src => x.src | .l => x.l | .r => x.r | .tag => x.tag | .dead => b2n !x.alive

def CF.set (x : Chunk) (v : Nat) : CF → Chunk
  | .next => { x with next := v } | .prev => { x with prev := v } | .first => { x with first := v }
  | .last => { x with last := v } | .size => { x with size := v } | .st => { x with st := St.ofN v }
  | .src => { x with src := v } | .l => { x with l := v } | .r => { x with r := v }
  | .tag => { x with tag := v } | .dead => { x with alive := v == 0 }

def CF.ok (v : Nat) : CF → Bool
  | .st => v ≤ 3 | .dead => decide (v ≤ 1) | _ => true

def NF.get (x : Node) : NF → Nat
  | .height => x.height | .livePar => x.livePar | .weight => x.weight | .first => x.first
  | .last => x.last | .draining => b2n x.draining | .t1 => x.t1 | .t2 => x.t2
  | .overflow => x.overflowOf | .dead => b2n !x.alive

def NF.set (x : Node) (v : Nat) : NF → Node
  | .height => { x with height := v } | .livePar => { x with livePar := v }
  | .weight => { x with weight := v } | .first => { x with first := v } | .last => { x with last := v }
  | .draining => { x with draining := v != 0 } | .t1 => { x with t1 := v } | .t2 => { x with t2 := v }
  | .overflow => { x with overflowOf := v } | .dead => { x with alive := v == 0 }

def NF.ok (v : Nat) : NF → Bool
  | .draining => v ≤ 1 | .dead => decide (v ≤ 1) | _ => true

def AF.get (s : Core) : AF → Array Nat
  | .pqHead => s.pqHead | .pqNext => s.pqNext | .pqPrev => s.pqPrev | .pqWhere => s.pqWhere
  | .nbNext => s.nbNext | .nbPrev => s.nbPrev | .lpar => s.lpar

def AF.set (s : Core) (a : Array Nat) : AF → Core
  | .pqHead => { s with pqHead := a } | .pqNext => { s with pqNext := a }
  | .pqPrev => { s with pqPrev := a } | .pqWhere => { s with pqWhere := a }
  | .nbNext => { s with nbNext := a } | .nbPrev => { s with nbPrev := a }
  | .lpar => { s with lpar := a }

def SF.get (s : Core) : SF → Nat
  | .count => s.count | .head => s.head | .tail => s.tail | .firstGroup => s.firstGroup
  | .firstChunk => s.firstChunk | .notReady => b2n !s.ready | .fallbacks => s.fallbacks
  | .pqHi => s.pqHi | .pqLo => s.pqLo | .pqScan => s.pqScan

def SF.set (s : Core) (v : Nat) : SF → Core
  | .count => { s with count := v } | .head => { s with head := v } | .tail => { s with tail := v }
  | .firstGroup => { s with firstGroup := v } | .firstChunk => { s with firstChunk := v }
  | .notReady => { s with ready := v == 0 } | .fallbacks => { s with fallbacks := v }
  | .pqHi => { s with pqHi := v } | .pqLo => { s with pqLo := v } | .pqScan => { s with pqScan := v }

def SF.ok (v : Nat) : SF → Bool
  | .notReady => decide (v ≤ 1) | _ => true

def Tbl.size (s : Core) : Tbl → Nat
  | .E => s.E.size | .G => s.Gs.size | .C => s.C.size | .N => s.nodes.size

def Tbl.push (s : Core) : Tbl → Core
  | .E => { s with E := s.E.push default } | .G => { s with Gs := s.Gs.push default }
  | .C => { s with C := s.C.push default } | .N => { s with nodes := s.nodes.push default }

def PF.get (P : Params) : PF → Nat
  | .N => P.N | .L => P.L | .G => P.G | .T => P.T | .theta => P.theta | .Be => P.B_e | .Bg => P.B_g
  | .De => P.D_e | .Dg => P.D_g | .KG => P.K_G | .KC => P.K_C | .KR => P.K_R | .a => P.a
  | .s => P.s | .beta => P.beta | .H => P.H

end fields

/-- The capacities of the machine arrays: records of each table, and plain arrays. -/
structure Caps where
  tbl : Tbl → Nat
  arr : AF → Nat

def Fld.tbl? : Fld → Option Tbl
  | .e _ => some .E | .g _ => some .G | .c _ => some .C | .n _ => some .N | _ => none

/-- The capacity of a field's machine array (1 for a scalar). -/
def Fld.cap (κ : Caps) : Fld → Nat
  | .e _ => κ.tbl .E | .g _ => κ.tbl .G | .c _ => κ.tbl .C | .n _ => κ.tbl .N
  | .a k => κ.arr k | .s _ => 1

/-- The value of field `f` of record `i` (index ignored for a scalar). -/
def Fld.get (s : Core) (i : Nat) : Fld → Nat
  | .e k => k.get (s.E.getX i) | .g k => k.get (s.Gs.getX i) | .c k => k.get (s.C.getX i)
  | .n k => k.get (s.nodes.getX i) | .a k => (k.get s).getX i | .s k => k.get s

/-- Write field `f` of record `i`; `none` if the encoding cannot represent the result. -/
def Fld.set (κ : Caps) (s : Core) (i v : Nat) : Fld → Option Core
  | .e k => if i < s.E.size ∧ k.ok v = true then some { s with E := s.E.modify i (k.set · v) } else none
  | .g k => if i < s.Gs.size ∧ k.ok v = true then some { s with Gs := s.Gs.modify i (k.set · v) } else none
  | .c k => if i < s.C.size ∧ k.ok v = true then some { s with C := s.C.modify i (k.set · v) } else none
  | .n k => if i < s.nodes.size ∧ k.ok v = true then some { s with nodes := s.nodes.modify i (k.set · v) }
    else none
  | .a k => if i < κ.arr k then some (k.set s ((k.get s).setX i v)) else none
  | .s k => if i < 1 ∧ k.ok v = true then some (k.set s v) else none

/-! ### Syntax -/

inductive Exp where
  | lit (n : Nat)
  | var (x : Reg)
  /-- Field `f` of record `i`. -/
  | rd (f : Fld) (i : Exp)
  /-- The number of records of a table. -/
  | size (t : Tbl)
  | prm (k : PF)
  | bin (op : BinOp) (a b : Exp)
  | un (op : UnOp) (a : Exp)
  deriving Repr, Inhabited

inductive Stm where
  | skip
  | assign (x : Reg) (e : Exp)
  | wr (f : Fld) (i e : Exp)
  /-- Append a default record to table `t`; its index goes to `x`. -/
  | push (t : Tbl) (x : Reg)
  | seq (s t : Stm)
  | ite (c : Exp) (s t : Stm)
  | loop (x : Reg) (n : Exp) (b : Stm)
  | call (name : String) (params : List Reg) (body : Stm) (rets : List Reg) (args : List Exp)
      (dsts : List Reg)
  /-- A failed guard. -/
  | fail
  /-- A state the source program never reaches (an assertion of Level F). -/
  | bug
  | catch (s h : Stm)
  deriving Repr, Inhabited

/-! ### Semantics on Level F -/

abbrev Loc := Reg → Nat

def Exp.ev (κ : Caps) (s : Core) (L : Loc) : Exp → Option Nat
  | .lit n => some n
  | .var x => some (L x)
  | .rd f i => (i.ev κ s L).bind fun j => if j < f.cap κ then some (f.get s j) else none
  | .size t => some (t.size s)
  | .prm k => some (k.get s.P)
  | .bin op a b => (a.ev κ s L).bind fun x => (b.ev κ s L).bind fun y => op.eval x y
  | .un op a => (a.ev κ s L).map op.eval

def evList (κ : Caps) (s : Core) (L : Loc) (es : List Exp) : Option (List Nat) := es.mapM (·.ev κ s L)

/-- The number of machine steps to evaluate an expression (that of its compiled form). -/
def Exp.cost : Exp → Nat
  | .lit _ | .var _ => 1
  | .rd _ i => 1 + i.cost
  | .size _ | .prm _ => 2
  | .bin _ a b => 1 + a.cost + b.cost
  | .un _ a => 1 + a.cost

def costList (es : List Exp) : Nat := (es.map Exp.cost).sum

/-- An outcome with the number of machine steps taken. -/
inductive Res where
  | ok (s : Core) (L : Loc) (c : Nat)
  | fail (s : Core) (L : Loc) (c : Nat)
  | bug

def Res.addCost (c : Nat) : Res → Res
  | .ok s L c' => .ok s L (c + c')
  | .fail s L c' => .fail s L (c + c')
  | .bug => .bug

def Res.bind (r : Res) (g : Core → Loc → Res) : Res :=
  match r with
  | .ok s L c => (g s L).addCost c
  | r => r

/-- The steps of `push`: read the count, write it back plus one. -/
def pushCost : Nat := 8

def runForF (f : Core → Loc → Res) (x : Reg) : Nat → Nat → Core → Loc → Res
  | _, 0, s, L => .ok s L 0
  | k, n + 1, s, L => ((f s (OM.Machine.State.upd L x k)).addCost 1).bind (runForF f x (k + 1) n)

def evalF (κ : Caps) : Stm → Core → Loc → Res
  | .skip, s, L => .ok s L 1
  | .assign x e, s, L =>
    match e.ev κ s L with
    | some v => .ok s (OM.Machine.State.upd L x v) (1 + e.cost)
    | none => .bug
  | .wr f i e, s, L =>
    match i.ev κ s L, e.ev κ s L with
    | some j, some v => match f.set κ s j v with
      | some s' => .ok s' L (1 + i.cost + e.cost)
      | none => .bug
    | _, _ => .bug
  | .push t x, s, L =>
    if t.size s < κ.tbl t then .ok (t.push s) (OM.Machine.State.upd L x (t.size s)) pushCost
    else .bug
  | .seq c d, s, L => (evalF κ c s L).bind (evalF κ d)
  | .ite c t f, s, L =>
    match c.ev κ s L with
    | some v => ((if v ≠ 0 then evalF κ t else evalF κ f) s L).addCost (1 + c.cost)
    | none => .bug
  | .loop x n b, s, L =>
    match n.ev κ s L with
    | some k => (runForF (evalF κ b) x 0 k s L).addCost (1 + n.cost)
    | none => .bug
  | .call _ ps b rs args ds, s, L =>
    match evList κ s L args with
    | some vs =>
      match evalF κ b s (OM.Machine.State.setLocs (fun _ => 0) ps vs) with
      | .ok s' L' c => .ok s' (OM.Machine.State.setLocs L ds (rs.map L'))
          (1 + costList args + ds.length + c)
      | .fail s' _ c => .fail s' L (1 + costList args + ds.length + c)
      | .bug => .bug
    | none => .bug
  | .fail, s, L => .fail s L 1
  | .bug, _, _ => .bug
  | .catch c h, s, L =>
    match evalF κ c s L with
    | .fail s' L' n => (evalF κ h s' L').addCost (1 + n)
    | .ok s' L' n => .ok s' L' (1 + n)
    | .bug => .bug

end OM.Impl
