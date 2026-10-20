import OM.Extract.Rust

/-!
# Experiment (not verified): `startDrain` without the quadratic list searches

Spliced into the extracted machine program in place of the verified `startDrainS`
(`OM/Impl/StartDrain.lean`); the proofs and the repository's program are unchanged. Three changes,
each relying on an invariant that is not proved here:

* the side list is built by appending (`sideBodyL`): table entries are distinct, so `assocSet`
  always appends;
* the side of the table entry at index `j` is read at index `j` of the side list, which is built in
  table order (`selSL`, `fixBodyL`; `selSL` checks the key and falls back to the search);
* above height 1, "`e` is a child of `v`" is tested by `e`'s live parent (`childE`, `fixCL`)
  instead of a search of `v`'s children.

Run from `lean/`: `lake env lean --run ../experiments/linear-drain-start/LinSD.lean OUT.rs`
(writes the generated module with the variant).
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

def crateL : String × (Nat × Nat × Nat) := Id.run do
  let progs0 : List (String × Stmt) :=
    [("init_ws", OM.Impl.initWS), ("insert_ws", OM.Impl.insertWS), ("delete_ws", OM.Impl.deleteWS),
     ("order_ws", OM.Impl.orderWS)]
  let sub : StateM (Nat × Nat × Nat) (List (String × Stmt)) :=
    progs0.mapM fun (p : String × Stmt) => do return (p.1, ← substSD p.2)
  let (progs, cnt) := sub.run (0, 0, 0)
  let act : GenM (List String) := progs.mapM fun (n, c) => topFn n c
  let (tops, g) := act.run {}
  let topLocs := dedup (["kb", "hx", "x", "y", "r", "hy"] ++ progs.flatMap fun (_, c) => stmtLocals c)
  let mut s := "// Generated by `lake exe extract` from the machine programs of `OM/Impl` (do not edit).\n"
  s := s ++ "// EXPERIMENT: startDrain replaced by the unverified linear version (LinSD.lean).\n"
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

def main (args : List String) : IO Unit := do
  let (s, (a, b, c)) := OM.Extract.crateL
  IO.FS.writeFile (args.headD "gen_lin.rs") s
  IO.println s!"startDrain calls replaced: core 0: {a}, core 1: {b}, unmatched: {c}"
