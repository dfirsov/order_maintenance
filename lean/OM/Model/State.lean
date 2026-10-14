/-!
# Level F: state

The functional model of the algorithm (`docs/LEAN.md` §4), a transliteration of the Python
prototype (`prototype/core.py`, `pq.py`, `top_wbbt.py`, `wrapper.py`). It is executable and is
tested against the prototype by trace replay (`OM/Test/Replay.lean`).

Conventions:
* Records live in arrays and refer to each other by index. Index 0 is a dummy and `NIL = 0`, so
  every real index is positive (the prototype uses 0-based indices and `NIL = -1`).
* Code runs in `EStateM Err Core`. A failed guard throws `Err.guard` and *keeps* the state
  reached, exactly like the prototype's exceptions; the caller then runs FALLBACK, which
  rebuilds everything from the element list. `Err.bug` marks a situation in which the prototype
  would crash (an assertion, a missing key); the tests check that it never occurs.
* Instrumentation of the prototype is omitted.
-/

namespace OM.Model

abbrev NIL : Nat := 0

/-- Parameters of one core (`prototype/core.py` `Params`, plus the top structure's). -/
structure Params where
  N : Nat
  L : Nat
  G : Nat
  T : Nat
  theta : Nat
  B_e : Nat
  B_g : Nat
  D_e : Nat
  D_g : Nat
  K_G : Nat
  K_C : Nat
  K_R : Nat
  a : Nat
  s : Nat
  beta : Nat
  H : Nat
  deriving Repr, Inhabited

inductive St where
  | quiet | overflow | splitting | dead
  deriving DecidableEq, Repr, Inhabited

structure Elem where
  next : Nat := NIL
  prev : Nat := NIL
  grp : Nat := NIL
  lab : Nat := 0
  live : Bool := true
  h : Nat := 0
  deriving Repr, Inhabited

structure Group where
  next : Nat := NIL
  prev : Nat := NIL
  first : Nat := NIL
  last : Nat := NIL
  chk : Nat := NIL
  lab : Nat := 0
  size : Nat := 0
  st : St := .quiet
  src : Nat := NIL
  l : Nat := NIL
  r : Nat := NIL
  alive : Bool := true
  deriving Repr, Inhabited

structure Chunk where
  next : Nat := NIL
  prev : Nat := NIL
  first : Nat := NIL
  last : Nat := NIL
  size : Nat := 0
  st : St := .quiet
  src : Nat := NIL
  l : Nat := NIL
  r : Nat := NIL
  tag : Nat := 0
  alive : Bool := true
  deriving Repr, Inhabited

inductive Side where
  | left | right
  deriving DecidableEq, Repr, Inhabited

/-- A node of the top tree (`prototype/top_wbbt.py` `Node`). The prototype's `lab` dictionary
and `order` list are merged into `table`: the entries with their labels, in label order. -/
structure Node where
  height : Nat := 0
  livePar : Nat := NIL
  children : List Nat := []
  weight : Nat := 0
  table : List (Nat × Nat) := []
  inTables : List Nat := []
  first : Nat := NIL
  last : Nat := NIL
  draining : Bool := false
  t1 : Nat := NIL
  t2 : Nat := NIL
  side : List (Nat × Side) := []
  overflowOf : Nat := NIL
  alive : Bool := true
  deriving Repr, Inhabited

/-- The program counter of a top-structure job (`top_wbbt.py` `_job`, a Python generator).
Each constructor is a point where the generator is suspended. -/
inductive JobPc where
  /-- Before copying level `j` of `x`'s path. -/
  | copy (j : Nat)
  /-- At the head of the upward walk; `none` means "start from `lpar[y]`". -/
  | walk (v : Option Nat)
  /-- Right after `_start_drain(v)` (its `yield`). -/
  | afterDrain (v up : Nat)
  /-- Inside the sweep funding loop of `v`, after `k` sweep steps. -/
  | fund (v up src k : Nat)
  deriving Repr, Inhabited

structure Job where
  x : Nat
  y : Nat
  z : Nat
  pc : JobPc
  deriving Repr, Inhabited

/-- Deferred construction of the top structure (`init_steps`, a Python generator). -/
structure Prep where
  chunk : Nat
  /-- The next height to build (starts at 1; `H + 1` means "finish"). -/
  h : Nat := 1
  below : Nat
  tag : Nat := 0
  path : Array Nat
  deriving Repr, Inhabited

/-- One insert-only core with its priority queue and top structure. -/
structure Core where
  P : Params
  E : Array Elem := #[default]
  Gs : Array Group := #[default]
  C : Array Chunk := #[default]
  freeG : List Nat := []
  count : Nat := 0
  head : Nat := NIL
  tail : Nat := NIL
  firstGroup : Nat := NIL
  firstChunk : Nat := NIL
  ready : Bool := true
  prep : Option Prep := none
  resJob : Option Job := none
  fallbacks : Nat := 0
  -- priority queue (`pq.py`): buckets by size, each a doubly linked list of chunks, pushed and
  -- popped at the head; non-empty buckets form a sorted doubly linked list
  pqHead : Array Nat := #[]
  pqNext : Array Nat := #[]
  pqPrev : Array Nat := #[]
  /-- The bucket of a chunk in the queue, 0 if absent (sizes in the queue exceed `theta ≥ 1`). -/
  pqWhere : Array Nat := #[]
  nbNext : Array Nat := #[]
  nbPrev : Array Nat := #[]
  /-- Largest and smallest non-empty bucket, 0 if the queue is empty. -/
  pqHi : Nat := 0
  pqLo : Nat := 0
  pqScan : Nat := 0
  -- top structure (`top_wbbt.py`)
  nodes : Array Node := #[default]
  path : Array (Array Nat) := #[]
  cin : Array (List Nat) := #[]
  lpar : Array Nat := #[]
  deriving Inhabited

inductive Err where
  | guard (msg : String)
  | bug (msg : String)
  deriving Repr, Inhabited

abbrev CM := EStateM Err Core

/-! ### Arrays as total maps -/

/-- Write `v` at `i`, extending the array with defaults if needed. -/
def _root_.Array.setX {α : Type} [Inhabited α] (a : Array α) (i : Nat) (v : α) : Array α :=
  if i < a.size then a.set! i v else (a ++ Array.replicate (i - a.size) default).push v

def _root_.Array.getX {α : Type} [Inhabited α] (a : Array α) (i : Nat) : α := a.getD i default

/-! ### Accessors -/

def guard {α : Type} (msg : String) : CM α := throw (.guard msg)
def bug {α : Type} (msg : String) : CM α := throw (.bug msg)

@[inline] def getE (i : Nat) : CM Elem := return (← get).E.getX i
@[inline] def getG (i : Nat) : CM Group := return (← get).Gs.getX i
@[inline] def getC (i : Nat) : CM Chunk := return (← get).C.getX i
@[inline] def getN (i : Nat) : CM Node := return (← get).nodes.getX i
@[inline] def getP : CM Params := return (← get).P

@[inline] def modE (i : Nat) (f : Elem → Elem) : CM Unit :=
  modify fun s => { s with E := s.E.modify i f }
@[inline] def modG (i : Nat) (f : Group → Group) : CM Unit :=
  modify fun s => { s with Gs := s.Gs.modify i f }
@[inline] def modC (i : Nat) (f : Chunk → Chunk) : CM Unit :=
  modify fun s => { s with C := s.C.modify i f }
@[inline] def modN (i : Nat) (f : Node → Node) : CM Unit :=
  modify fun s => { s with nodes := s.nodes.modify i f }

/-! ### Small list helpers -/

/-- The position of `x` in `l`, if present. -/
def _root_.List.idx? (l : List Nat) (x : Nat) : Option Nat := l.findIdx? (· == x)

/-- Replace the first occurrence of `x` by the list `ys`. -/
def _root_.List.replace1 (l : List Nat) (x : Nat) (ys : List Nat) : List Nat :=
  match l with
  | [] => []
  | a :: t => if a = x then ys ++ t else a :: t.replace1 x ys

/-- Remove the first occurrence of `x`. -/
def _root_.List.remove1 (l : List Nat) (x : Nat) : List Nat := l.erase x

def lookup {β : Type} (l : List (Nat × β)) (k : Nat) : Option β := (l.find? (·.1 == k)).map (·.2)

def Node.lab? (n : Node) (e : Nat) : Option Nat := lookup n.table e
def Node.order (n : Node) : List Nat := n.table.map (·.1)

end OM.Model
