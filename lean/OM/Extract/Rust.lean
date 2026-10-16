import OM.Impl.TheoremsM
import Std.Data.HashMap

/-!
# Printing the machine program as Rust

`OM.Machine.Stmt` is printed as Rust, statement for statement. The printer is trusted (not
verified), so it is kept direct:

* a machine local `x` becomes a Rust variable `l_x` (in a procedure) or a field `t.l_x` (in the
  top-level frame, which persists between operations, as in `exec`);
* machine array `a` becomes a dense index into the runtime's memory (the array's number is kept
  in a comment);
* every statement first adds its own cost to `m.cost`, exactly as `exec` charges it, so the Rust
  code counts the same steps; every expression node records its value in `m.peak` (`maxv`);
* a `call` becomes a call of a Rust function; each distinct callee (parameters, results and
  body, compared by their printed text) is printed once;
* `fail` returns `Err(Fail)`, which propagates to the nearest `catch` (a closure) or out of the
  procedure; a machine error (an access beyond the capacity, a subtraction below 0) panics.

The runtime (`rust/src/rt.rs`) implements the words (arbitrary precision), the arrays and the
operators with the semantics of `Exec.lean`.
-/

namespace OM.Extract

open OM.Machine

structure Gen where
  fns : Array String := #[]
  idx : Std.HashMap String Nat := {}
  arrs : Std.HashMap Nat Nat := {}
  arrList : Array Nat := #[]

abbrev GenM := StateM Gen

/-- A Rust identifier for machine local `x`. -/
def ident (x : Reg) : String :=
  "l_" ++ String.join (x.toList.map fun c =>
    if c.isAlphanum then c.toString else "_u" ++ toString c.toNat ++ "_")

/-- The dense index of machine array `a`. -/
def arrId (a : Arr) : GenM String := do
  let g ← get
  match g.arrs.get? a with
  | some i => return s!"{i}/*a{a}*/"
  | none =>
    let i := g.arrList.size
    set { g with arrs := g.arrs.insert a i, arrList := g.arrList.push a }
    return s!"{i}/*a{a}*/"

def binName : BinOp → String
  | .add => "Add" | .sub => "Sub" | .mul => "Mul" | .div => "Div" | .mod => "Mod"
  | .shl => "Shl" | .shr => "Shr" | .lt => "Lt" | .le => "Le" | .eq => "Eq"
  | .and => "And" | .or => "Or"

def unName : UnOp → String
  | .not => "Not" | .msb => "Msb"

def litW (n : Nat) : String :=
  if n < 2 ^ 64 then s!"W::S({n})" else s!"W::big(\"{n}\")"

/-- An expression, evaluated left to right; `loc` renders a local. -/
def expr (loc : Reg → String) : Expr → GenM String
  | .lit n => return s!"pk({litW n}, m)"
  | .var x => return s!"pk({loc x}.clone(), m)"
  | .load a i => do return s!"load({← arrId a}, {← expr loc i}, m)"
  | .bin op a b => do return s!"bin(Op::{binName op}, {← expr loc a}, {← expr loc b}, m)"
  | .un op a => do return s!"un(Uop::{unName op}, {← expr loc a}, m)"

/-- The locals a statement mentions (callee bodies excluded; they have their own frames). -/
partial def exprLocals : Expr → List Reg
  | .lit _ => []
  | .var x => [x]
  | .load _ i => exprLocals i
  | .bin _ a b => exprLocals a ++ exprLocals b
  | .un _ a => exprLocals a

partial def stmtLocals : Stmt → List Reg
  | .skip | .fail => []
  | .assign x e => x :: exprLocals e
  | .store _ i e => exprLocals i ++ exprLocals e
  | .alloc _ n => exprLocals n
  | .seq s t => stmtLocals s ++ stmtLocals t
  | .ite c s t => exprLocals c ++ stmtLocals s ++ stmtLocals t
  | .loop x n b => x :: exprLocals n ++ stmtLocals b
  | .call _ _ _ _ args ds => (args.flatMap exprLocals) ++ ds
  | .catch s h => stmtLocals s ++ stmtLocals h

def dedup (l : List Reg) : List Reg := l.foldl (fun acc x => if acc.contains x then acc else acc ++ [x]) []

def ind (n : Nat) : String := "".pushn ' ' (2 * n)

mutual
/-- A statement. `loc` renders a local; `d` is the indentation depth. -/
partial def stmt (loc : Reg → String) (d : Nat) : Stmt → GenM String
  | .skip => return s!"{ind d}m.cost += 1;\n"
  | .assign x e => do
    return s!"{ind d}m.cost += {1 + e.cost};\n{ind d}{loc x} = {← expr loc e};\n"
  | .store a i e => do
    return s!"{ind d}m.cost += {1 + i.cost + e.cost};\n{ind d}\{ let i = {← expr loc i}; let v = {← expr loc e}; store({← arrId a}, i, v, m); }\n"
  | .alloc a n => do
    return s!"{ind d}m.cost += {1 + n.cost};\n{ind d}\{ let k = {← expr loc n}; alloc({← arrId a}, k, m); }\n"
  | .seq s t => do return (← stmt loc d s) ++ (← stmt loc d t)
  | .ite c s t => do
    return s!"{ind d}m.cost += {1 + c.cost};\n{ind d}if {← expr loc c}.nz() \{\n{← stmt loc (d + 1) s}{ind d}} else \{\n{← stmt loc (d + 1) t}{ind d}}\n"
  | .loop x n b => do
    return s!"{ind d}m.cost += {1 + n.cost};\n{ind d}\{ let n = {← expr loc n}.as_u64(); for k in 0..n \{\n{ind (d + 1)}m.cost += 1;\n{ind (d + 1)}{loc x} = W::S(k);\n{← stmt loc (d + 1) b}{ind d}} }\n"
  | .call _ ps body rs args ds => do
    let f ← proc ps body rs args.length
    let mut s := s!"{ind d}m.cost += {1 + costList args + ds.length};\n{ind d}\{\n"
    let mut i := 0
    for a in args do
      s := s ++ s!"{ind (d + 1)}let a{i} = {← expr loc a};\n"
      i := i + 1
    let argl := ", ".intercalate ((List.range args.length).map fun j => s!"a{j}")
    s := s ++ s!"{ind (d + 1)}let r = {f}([{argl}], m)?;\n"
    let mut j := 0
    for (x, _) in ds.zip rs do
      s := s ++ s!"{ind (d + 1)}{loc x} = r[{j}].clone();\n"
      j := j + 1
    return s ++ s!"{ind d}}\n"
  | .fail => return s!"{ind d}m.cost += 1;\n{ind d}return Err(Fail);\n"
  | .catch c h => do
    return s!"{ind d}m.cost += 1;\n{ind d}let r: R<()> = (|| -> R<()> \{\n{← stmt loc (d + 1) c}{ind (d + 1)}Ok(())\n{ind d}})();\n{ind d}if r.is_err() \{\n{← stmt loc (d + 1) h}{ind d}}\n"

/-- The Rust function of a callee: parameters, results and body. Returns its name. -/
partial def proc (ps : List Reg) (body : Stmt) (rs : List Reg) (nargs : Nat) : GenM String := do
  let txt ← stmt ident 1 body
  let key := s!"{ps}|{rs}|{nargs}\n{txt}"
  match (← get).idx.get? key with
  | some i => return s!"f{i}"
  | none =>
    let i := (← get).fns.size
    modify fun g => { g with idx := g.idx.insert key i, fns := g.fns.push "" }
    let locs := dedup (ps ++ rs ++ stmtLocals body)
    let mut s := s!"#[allow(unused_mut, unused_variables, unused_assignments, non_snake_case, unreachable_code)]\nfn f{i}(args: [W; {nargs}], m: &mut M) -> R<[W; {rs.length}]> \{\n"
    for x in locs do
      s := s ++ s!"  let mut {ident x}: W = W::S(0);\n"
    let mut j := 0
    for (p, _) in ps.zip (List.range nargs) do
      s := s ++ s!"  {ident p} = args[{j}].clone();\n"
      j := j + 1
    s := s ++ txt
    let rl := ", ".intercalate (rs.map fun x => s!"{ident x}.clone()")
    s := s ++ s!"  Ok([{rl}])\n}\n"
    modify fun g => { g with fns := g.fns.set! i s }
    return s!"f{i}"
end

/-- A top-level program: it runs in the persistent top-level frame `t`. -/
def topFn (name : String) (c : Stmt) : GenM String := do
  let body ← stmt (fun x => "t." ++ ident x) 1 c
  return s!"#[allow(unused_mut, unused_variables, unreachable_code)]\npub fn {name}(t: &mut Top, m: &mut M) -> R<()> \{\n{body}  Ok(())\n}\n"

/-- The generated module: the top-level frame, the four programs, the procedures. -/
def crate : String := Id.run do
  let progs : List (String × Stmt) :=
    [("init_ws", OM.Impl.initWS), ("insert_ws", OM.Impl.insertWS), ("delete_ws", OM.Impl.deleteWS),
     ("order_ws", OM.Impl.orderWS)]
  let act : GenM (List String) := progs.mapM fun (n, c) => topFn n c
  let (tops, g) := act.run {}
  let topLocs := dedup (["kb", "hx", "x", "y", "r", "hy"] ++ progs.flatMap fun (_, c) => stmtLocals c)
  let mut s := "// Generated by `lake exe extract` from the machine programs of `OM/Impl` (do not edit).\n"
  s := s ++ "use crate::rt::*;\n\n"
  s := s ++ s!"/// The number of machine arrays the program uses.\npub const NARR: usize = {g.arrList.size};\n"
  s := s ++ s!"/// Their machine numbers.\npub const ARRS: [u64; {g.arrList.size}] = [{", ".intercalate (g.arrList.toList.map toString)}];\n\n"
  s := s ++ "/// The top-level frame: the locals of the top-level programs.\n#[derive(Clone, Default)]\n#[allow(non_snake_case)]\npub struct Top {\n"
  for x in topLocs do
    s := s ++ s!"  pub {ident x}: W,\n"
  s := s ++ "}\n\n"
  for t in tops do
    s := s ++ t ++ "\n"
  for f in g.fns do
    s := s ++ f ++ "\n"
  return s

end OM.Extract
