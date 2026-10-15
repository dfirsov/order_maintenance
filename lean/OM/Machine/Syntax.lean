/-
The machine language (`docs/LEAN.md` §3): a small imperative language over a word RAM.

* Words are `Nat`. The interpreter does not truncate; it records the largest value ever
  computed (`State.peak`), and the word-size theorem bounds that value separately.
* Memory is a finite set of named arrays (named by numbers), each with a capacity set by `alloc`.
* Locals are per procedure call.
* There is no `while` and no recursion. A call carries the callee's body as a subterm, so a
  procedure cannot call itself: the syntax tree would be infinite. Every program terminates by
  construction, and `exec` is a structurally recursive total function.
-/

namespace OM.Machine

/-- Local variable names. -/
abbrev Reg := String

/-- Array names: numbers, so that distinct arrays are told apart by arithmetic. -/
abbrev Arr := Nat

inductive BinOp where
  | add | sub | mul | div | mod | shl | shr | lt | le | eq | and | or
  deriving DecidableEq, Repr

inductive UnOp where
  | not | msb
  deriving DecidableEq, Repr

inductive Expr where
  | lit (n : Nat)
  | var (x : Reg)
  | load (a : Arr) (i : Expr)
  | bin (op : BinOp) (e₁ e₂ : Expr)
  | un (op : UnOp) (e : Expr)
  deriving Repr, Inhabited

inductive Stmt where
  | skip
  | assign (x : Reg) (e : Expr)
  | store (a : Arr) (i e : Expr)
  /-- Give array `a` capacity `n` (the value of the expression), all cells reading 0.
  One step: constant-time-initializable arrays. -/
  | alloc (a : Arr) (n : Expr)
  | seq (s t : Stmt)
  | ite (c : Expr) (s t : Stmt)
  /-- `for x < n do s`: `n` is evaluated once; iteration `k` sets `x := k` first. -/
  | loop (x : Reg) (n : Expr) (body : Stmt)
  /-- Call a procedure with formal parameters `params`, body `body` and result locals `rets`.
  The arguments are evaluated in the caller's frame, the body runs in a fresh frame, and the
  results are copied back to `dsts`. -/
  | call (name : String) (params : List Reg) (body : Stmt) (rets : List Reg)
      (args : List Expr) (dsts : List Reg)
  /-- A failed algorithmic guard: aborts up to the nearest `catch`. -/
  | fail
  /-- `catch s h`: run `s`; if it executes `fail`, run the handler `h` on the state reached. -/
  | catch (s h : Stmt)
  deriving Repr, Inhabited

/-- A procedure declaration; `Proc.invoke` turns it into a `call` statement. -/
structure Proc where
  name : String
  params : List Reg
  rets : List Reg
  body : Stmt

def Proc.invoke (p : Proc) (args : List Expr) (dsts : List Reg) : Stmt :=
  .call p.name p.params p.body p.rets args dsts

/-! ### Concrete syntax -/

instance {n : Nat} : OfNat Expr n := ⟨.lit n⟩
instance : Coe Reg Expr := ⟨.var⟩
instance : Add Expr := ⟨.bin .add⟩
instance : Sub Expr := ⟨.bin .sub⟩
instance : Mul Expr := ⟨.bin .mul⟩
instance : Div Expr := ⟨.bin .div⟩
instance : Mod Expr := ⟨.bin .mod⟩

/-- Shift left: `a <<< b` is `a * 2^b`. -/
instance : ShiftLeft Expr := ⟨.bin .shl⟩
/-- Shift right: `a >>> b` is `a / 2^b`. -/
instance : ShiftRight Expr := ⟨.bin .shr⟩
/-- Comparisons return 1 or 0. -/
infix:50 " <ₑ " => Expr.bin BinOp.lt
infix:50 " ≤ₑ " => Expr.bin BinOp.le
infix:50 " =ₑ " => Expr.bin BinOp.eq
infixr:35 " &&ₑ " => Expr.bin BinOp.and
infixr:30 " ||ₑ " => Expr.bin BinOp.or
prefix:max "!ₑ" => Expr.un UnOp.not
notation:max a "[[" i "]]" => Expr.load a i

@[simp] theorem Expr.ofNat_def (n : Nat) : (OfNat.ofNat n : Expr) = .lit n := rfl
@[simp] theorem Expr.add_def (a b : Expr) : a + b = .bin .add a b := rfl
@[simp] theorem Expr.sub_def (a b : Expr) : a - b = .bin .sub a b := rfl
@[simp] theorem Expr.mul_def (a b : Expr) : a * b = .bin .mul a b := rfl
@[simp] theorem Expr.div_def (a b : Expr) : a / b = .bin .div a b := rfl
@[simp] theorem Expr.mod_def (a b : Expr) : a % b = .bin .mod a b := rfl
@[simp] theorem Expr.shl_def (a b : Expr) : a <<< b = .bin .shl a b := rfl
@[simp] theorem Expr.shr_def (a b : Expr) : a >>> b = .bin .shr a b := rfl

infixr:20 " ;; " => Stmt.seq
infix:40 " ::= " => Stmt.assign

end OM.Machine
