import OM.Extract.Rust

/-!
# Experiments (not verified): a linear `startDrain` and other parameter profiles

`lake env lean --run ../experiments/worst-case/Splice.lean OUT.rs (orig|lin) [kR a s cT hd]`
writes the generated module with the verified `startDrain` (`orig`) or the linear one (`lin`, the
same code as `../linear-drain-start/LinSD.lean`), and optionally the parameter profile
`K_R = kR`, `a`, `s`, `T = cT·L²`, `θ = 2T/3`, `H = L/hd + 1` (and `s + 1` in the node
capacity), rewritten in the parameter computation (`paramsS`, `OM/Impl/Params.lean`) wherever
the program computes it. With `orig` and no profile the output equals `rust/src/gen.rs`.
-/

namespace OM.Impl
open OM.Model
open OM.Machine (Reg BinOp UnOp)

/-- Side list by appending (table entries are distinct, so `assocSet` always appends). -/
def sideBodyL : Stm :=
  "e" ::= .lrd .table false "v" "j" ;;
  .ite ("e" =ₑ "b") ("sd" ::= 1) .skip ;;
  .lgrow .side "v" "e" "sd"

/-- Child test by the live-parent pointer; the side of entry `j` is at index `j`. -/
def fixCL : Exp := ((.rd (.n .livePar) "e" =ₑ "v") ||ₑ (!ₑ (.rd (.n .first) "e" =ₑ 0))) &&ₑ .rd (.n .draining) "e"
def fixBodyL : Stm :=
  "e" ::= .lrd .table false "v" "j" ;;
  .ite fixCL
    ((lookupP .side).call [.var "v", .rd (.n .t1) "e"] ["f", "x"] ;;
     .ite "f" (.lwr .side true "v" "j" "x") .fail)
    .skip

def drainSideSL : Stm :=
  .lclear .side "v" ;; "sd" ::= 0 ;; "n" ::= .llen .table "v" ;;
  .loop "j" "n" sideBodyL ;;
  .ite (1 <ₑ .rd (.n .height) "v") (.loop "j" "n" fixBodyL) .skip

def selEL : Exp := ((("h" =ₑ 1) ||ₑ "c") ||ₑ (!ₑ (.rd (.n .first) "e" =ₑ 0))) &&ₑ ("f" &&ₑ ("x" =ₑ "sd"))
def childE : Exp := .rd (.n .livePar) "e" =ₑ "v"
/-- `selS` with the child test by live parent and the side read at index `j` (search as fallback). -/
def selSL : Stm :=
  "c" ::= childE ;;
  .ite (.lrd .side false "v" "j" =ₑ "e") ("f" ::= 1 ;; "x" ::= .lrd .side true "v" "j")
    ((lookupP .side).call [.var "v", .var "e"] ["f", "x"]) ;;
  "q" ::= selEL

def cntBodyL : Stm := "e" ::= .lrd .table false "v" "j" ;; selSL ;; .ite "q" ("cnt" ::= "cnt" + 1) .skip
def bldBodyL : Stm :=
  "e" ::= .lrd .table false "v" "j" ;; selSL ;;
  .ite "q" ("idx" ::= "idx" + 1 ;; .lgrow .table "w" "e" ("idx" * "st")) .skip
def tabSL : Stm :=
  "nt" ::= .llen .table "v" ;;
  "cnt" ::= 0 ;; .loop "j" "nt" cntBodyL ;;
  "st" ::= .bin .shl 1 (.prm .beta) / ("cnt" + 1) ;;
  "idx" ::= 0 ;; .loop "j" "nt" bldBodyL
def newTabSL : Stm := "a" ::= .var "v" ;; copyS .inTab ;; tabSL
def stage3SL : Stm :=
  "w" ::= .var "v1" ;; "sd" ::= 0 ;; newTabSL ;; "w" ::= .var "v2" ;; "sd" ::= 1 ;; newTabSL

def sdMainL : Stm :=
  .ite ("k" <ₑ "nk") ("b" ::= .lrd .children false "v" "k") ("b" ::= 0) ;;
  drainSideSL ;; newNodesS ;; insS ;; stage3SL ;; stage4S ;; stage56S ;; stage7S ;; stage8S
def startDrainSL : Stm :=
  "h" ::= .rd (.n .height) "v" ;; "nk" ::= .llen .children "v" ;;
  .ite ("nk" <ₑ 2) .skip (drainCutS ;; .ite sdCond .skip sdMainL)

end OM.Impl

namespace OM.Extract
open OM.Machine

def old0 : String := toString (repr (OM.Impl.startDrainS.compile 0 OM.Impl.κ₀))
def old1 : String := toString (repr (OM.Impl.startDrainS.compile 1 OM.Impl.κ₀))

/-- Replace the body of every call of `startDrain`; counts (core 0, core 1, unmatched). -/
partial def substSD : OM.Machine.Stmt → StateM (Nat × Nat × Nat) OM.Machine.Stmt
  | .seq a b => return .seq (← substSD a) (← substSD b)
  | .ite c a b => return .ite c (← substSD a) (← substSD b)
  | .loop x n b => return .loop x n (← substSD b)
  | .catch a b => return .catch (← substSD a) (← substSD b)
  | .call nm ps b rs as ds => do
    if nm == "startDrain" then
      let r := toString (repr b)
      if r == old0 then
        modify fun (a, b, c) => (a + 1, b, c)
        return .call nm ps (OM.Impl.startDrainSL.compile 0 OM.Impl.κ₀) rs as ds
      else if r == old1 then
        modify fun (a, b, c) => (a, b + 1, c)
        return .call nm ps (OM.Impl.startDrainSL.compile 1 OM.Impl.κ₀) rs as ds
      else
        modify fun (a, b, c) => (a, b, c + 1)
        return .call nm ps b rs as ds
    else return .call nm ps (← substSD b) rs as ds
  | s => return s


/-! ### A parameter profile: rewrite the parameter array and the expressions derived from it -/

partial def eqE : Expr → Expr → Bool
  | .lit a, .lit b => a == b
  | .var a, .var b => a == b
  | .load a i, .load b j => a == b && eqE i j
  | .bin o a b, .bin p c d => reprStr o == reprStr p && eqE a c && eqE b d
  | .un o a, .un p b => reprStr o == reprStr p && eqE a b
  | _, _ => false

open OM.Impl in
def eT' (cT : Nat) : Expr := .bin .mul (.bin .mul (.lit cT) eL) eL
open OM.Impl in
def eth' (cT : Nat) : Expr := .bin .div (.bin .mul (.lit 2) (eT' cT)) (.lit 3)
open OM.Impl in
def eH' (hd : Nat) : Expr := .bin .add (.bin .div eL (.lit hd)) (.lit 1)
open OM.Impl in
def enb' (hd s : Nat) : Expr := .bin .add (.bin .add (eH' hd) (.lit 2))
  (.bin .mul (.bin .add (.bin .add (eH' hd) (.lit 1)) (.bin .add (.bin .mul (eH' hd) (.lit (s + 1))) (.lit 1))) OM.Impl.ecb)

structure Prof where
  kR : Nat
  a : Nat
  s : Nat
  cT : Nat
  hd : Nat

open OM.Impl in
partial def rwE (p : Prof) (e : Expr) : Expr :=
  if eqE e enb then enb' p.hd p.s
  else if eqE e eT then eT' p.cT
  else if eqE e eth then eth' p.cT
  else if eqE e eH then eH' p.hd
  else match e with
    | .load a i => .load a (rwE p i)
    | .bin o a b => .bin o (rwE p a) (rwE p b)
    | .un o a => .un o (rwE p a)
    | e => e

open OM.Impl in
/-- Rewrite every expression, and the stores of `K_R`, `a`, `s` into a parameter array. -/
partial def rwS (p : Prof) : Stmt → Stmt
  | .assign x e => .assign x (rwE p e)
  | .store a i e =>
    match i, e with
    | .lit k, .lit _ =>
      if k == PF.KR.idx then .store a i (.lit p.kR)
      else if k == PF.a.idx then .store a i (.lit p.a)
      else if k == PF.s.idx then .store a i (.lit p.s)
      else .store a i e
    | _, _ => .store a (rwE p i) (rwE p e)
  | .alloc a n => .alloc a (rwE p n)
  | .seq a b => .seq (rwS p a) (rwS p b)
  | .ite c a b => .ite (rwE p c) (rwS p a) (rwS p b)
  | .loop x n b => .loop x (rwE p n) (rwS p b)
  | .call nm ps b rs as ds => .call nm ps (rwS p b) rs (as.map (rwE p)) ds
  | .catch a b => .catch (rwS p a) (rwS p b)
  | s => s

def crateV (lin : Bool) (prof : Option Prof) : String × (Nat × Nat × Nat) := Id.run do
  let progs0 : List (String × Stmt) :=
    [("init_ws", OM.Impl.initWS), ("insert_ws", OM.Impl.insertWS), ("delete_ws", OM.Impl.deleteWS),
     ("order_ws", OM.Impl.orderWS)]
  let sub : StateM (Nat × Nat × Nat) (List (String × Stmt)) :=
    progs0.mapM fun (p : String × Stmt) => do return (p.1, ← if lin then substSD p.2 else pure p.2)
  let (progs1, cnt) := sub.run (0, 0, 0)
  let progs := match prof with
    | some pr => progs1.map fun (p : String × Stmt) => (p.1, rwS pr p.2)
    | none => progs1
  let act : GenM (List String) := progs.mapM fun (n, c) => topFn n c
  let (tops, g) := act.run {}
  let topLocs := dedup (["kb", "hx", "x", "y", "r", "hy"] ++ progs.flatMap fun (_, c) => stmtLocals c)
  let mut s := "// Generated by `lake exe extract` from the machine programs of `OM/Impl` (do not edit).\n"
  s := s ++ s!"// EXPERIMENT: linear startDrain {lin}, profile {(prof.map fun p => s!"K_R={p.kR} a={p.a} s={p.s} T={p.cT}L^2 H=L/{p.hd}+1")}.\n"
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
  return (s, cnt)

end OM.Extract

/-- `Splice OUT lin|orig [kR a s cT hd]` -/
def main (args : List String) : IO Unit := do
  let out := args.headD "gen.rs"
  let lin := args.getD 1 "orig" == "lin"
  let prof : Option OM.Extract.Prof := match args.drop 2 |>.map String.toNat! with
    | [kR, a, s, cT, hd] => some { kR, a, s, cT, hd }
    | _ => none
  let (s, (a, b, c)) := OM.Extract.crateV lin prof
  IO.FS.writeFile out s
  IO.println s!"wrote {out}; startDrain replaced: {a}+{b}, unmatched {c}"
