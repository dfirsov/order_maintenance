import OM.Impl.Notation

/-!
# M6: concrete syntax for the core language

`cm{ … }` writes a statement of the core language and `cme{ … }` an expression:

```
cm{ gp := G[g].prev
    if gp ≠ 0 then G[gp].next := gl
    if C[c].first = g then C[c].first := gl else { x := 1; fail }
    labL ← labBeforeP(g) }
```

Statements are separated by newlines (aligned) or `;`, and `{ … }` groups them. This is
notation only: each form expands to the constructor term written with the helpers of
`Notation.lean` (`Exp.gF`, `Stm.wgF`, `;;`, `::=`, `=ₑ`, …), so the proofs see the same terms.

* Registers are identifiers: `x` is `.var "x"`. `P.k` is parameter `k`, `S.k` is scalar `k`.
* `E[i].f`, `G[i].f`, `C[i].f`, `N[i].f` are field `f` of record `i` of a table;
  `a[i]` is cell `i` of the core array `a` (`AF`).
* `k[i]` with `k : LK` is a list: `len k[i]`, `k[i][j].fst`, `append k[i] (a, b)`, `pop k[i]`;
  `k` is an `LK` constructor or a Lean variable.
* `x := new T` appends a fresh record to table `T`; `x ← p(args)` calls procedure `p`.
* `for x < n do s` is the bounded loop, `try s catch h` the handler.
* `O.k` is field `k` of the pending job or path preparation, `size T` the number of records of
  table `T`, `path(c, j)` level `j` of chunk `c`'s path; `max(a, b)`, `msb(a)`, and `a ∸ b` is
  truncated subtraction (`Exp.monus`). The other statements of `Stm` (`pcSet(…)`,
  `prepCommit`, …) keep their constructor names.
* `skip`, `fail` and `bug` are the statements of those names; any other bare identifier in
  statement position is a `Stm` defined elsewhere, and `‹t›` embeds a Lean term (an `Exp`, a
  `Stm`, or a field name).
* `x ← ‹q›(args)`, `(x, y) ← ‹q›(args)` and `call ‹q›(args)` call a procedure given by a
  Lean term `q : Proc` (e.g. `‹findP k›`, a procedure family applied to its list kind).
* `‹r› := e` assigns to the register named by the Lean term `r : Reg` (a parameter of the
  definition), as `‹r›` reads it.
* Comparisons, `!`, `&&`, `||` return 0 or 1, as `<ₑ`, `!ₑ`, … do.
-/

namespace OM.Impl.CM

open Lean

declare_syntax_cat cmF
declare_syntax_cat cmE (behavior := both)
declare_syntax_cat cmS (behavior := both)

open Lean.Parser in
/-- Statements separated by `;` or by line breaks at the same column. -/
def cmSeq := leading_parser sepBy1Indent (categoryParser `cmS 0) "; "

syntax (name := fId) ident : cmF
syntax (name := fTm) "‹" term "›" : cmF

syntax (name := eNum) num : cmE
syntax (name := eVar) ident : cmE
syntax (name := ePar) "(" cmE ")" : cmE
syntax (name := eTm) "‹" term "›" : cmE
syntax (name := eFld) ident "[" cmE "]" "." cmF : cmE
syntax (name := eArr) ident "[" cmE "]" : cmE
syntax (name := eLst) ident "[" cmE "]" "[" cmE "]" "." cmF : cmE
syntax (name := eLen) &"len" ident "[" cmE "]" : cmE
syntax (name := eSize) &"size" ident : cmE
syntax (name := ePath) &"path" "(" cmE ", " cmE ")" : cmE
syntax (name := eMax) &"max" "(" cmE ", " cmE ")" : cmE
syntax (name := eMsb) &"msb" "(" cmE ")" : cmE
-- The operand is at `lead` (not `max`) precedence: the forms that start with an identifier
-- (`x`, `G[i].f`, …) sit at `lead`, so `!x` and `!G[i].f` parse without parentheses.
syntax:max (name := eNot) "!" cmE:lead : cmE
syntax:75 (name := eShl) cmE:75 " <<< " cmE:76 : cmE
syntax:75 (name := eShr) cmE:75 " >>> " cmE:76 : cmE
syntax:70 (name := eMul) cmE:70 " * " cmE:71 : cmE
syntax:70 (name := eDiv) cmE:70 " / " cmE:71 : cmE
syntax:70 (name := eMod) cmE:70 " % " cmE:71 : cmE
syntax:65 (name := eAdd) cmE:65 " + " cmE:66 : cmE
syntax:65 (name := eSub) cmE:65 " - " cmE:66 : cmE
syntax:65 (name := eMonus) cmE:65 " ∸ " cmE:66 : cmE
syntax:50 (name := eLt) cmE:51 " < " cmE:51 : cmE
syntax:50 (name := eLe) cmE:51 " ≤ " cmE:51 : cmE
syntax:50 (name := eEq) cmE:51 " = " cmE:51 : cmE
syntax:50 (name := eNe) cmE:51 " ≠ " cmE:51 : cmE
syntax:35 (name := eAnd) cmE:36 " && " cmE:35 : cmE
syntax:30 (name := eOr) cmE:31 " || " cmE:30 : cmE

syntax (name := sId) ident : cmS
syntax (name := sTm) "‹" term "›" : cmS
syntax (name := sBlk) "{" cmSeq "}" : cmS
syntax (name := sAsg) ident " := " cmE : cmS
syntax (name := sAsgT) "‹" term "›" " := " cmE : cmS
syntax (name := sNew) ident " := " &"new" ident : cmS
syntax (name := sFld) ident "[" cmE "]" "." cmF " := " cmE : cmS
syntax (name := sArr) ident "[" cmE "]" " := " cmE : cmS
syntax (name := sLst) ident "[" cmE "]" "[" cmE "]" "." cmF " := " cmE : cmS
syntax (name := sApp) &"append" ident "[" cmE "]" " (" cmE ", " cmE ")" : cmS
syntax (name := sPop) &"pop" ident "[" cmE "]" : cmS
syntax (name := sClr) &"clear" ident "[" cmE "]" : cmS
syntax (name := sIf) "if " cmE " then " cmS (" else " cmS)? : cmS
syntax (name := sFor) "for " ident " < " cmE " do " cmS : cmS
syntax (name := sTry) "try " cmS " catch " cmS : cmS
syntax (name := sPath) &"path" "(" cmE ", " cmE ")" " := " cmE : cmS
syntax (name := sCon) ident "(" cmE,* ")" : cmS
syntax (name := sCall1) ident " ← " ident "(" cmE,* ")" : cmS
syntax (name := sCallN) "(" ident,* ")" " ← " ident "(" cmE,* ")" : cmS
syntax (name := sCall0) &"call" ident "(" cmE,* ")" : cmS
syntax (name := sCall1T) ident " ← " "‹" term "›" "(" cmE,* ")" : cmS
syntax (name := sCallNT) "(" ident,* ")" " ← " "‹" term "›" "(" cmE,* ")" : cmS
syntax (name := sCall0T) &"call" "‹" term "›" "(" cmE,* ")" : cmS

/-- `ns.f` for a field identifier `f`, or the embedded term. -/
def expF (ns : Name) (f : Syntax) : MacroM Term :=
  match f.getKind with
  | ``fId => pure (mkIdent (ns ++ f[0].getId))
  | ``fTm => pure ⟨f[1]⟩
  | _ => Macro.throwErrorAt f "unexpected field"

/-- The single name component of an identifier, as a string. -/
def str (x : Syntax) : Term := Syntax.mkStrLit x.getId.toString

/-- `P.k` and `S.k`: the table prefix and the field. -/
def dotted (x : Syntax) : Option (String × Name) :=
  match x.getId with
  | .str (.str .anonymous p) k => some (p, .mkSimple k)
  | _ => none

def isLK (k : Syntax) : Bool :=
  k.getId ∈ [`children, `table, `inTab, `side, `cin, `freeG]

/-- A list kind: an `LK` constructor, or else a Lean variable of type `LK`. -/
def lk (k : Syntax) : Term := if isLK k then mkIdent (`OM.Impl.LK ++ k.getId) else ⟨k⟩

def sndOf (f : Syntax) : MacroM Term :=
  match f.getKind, f[0].getId with
  | ``fId, `fst => `(false)
  | ``fId, `snd => `(true)
  | _, _ => Macro.throwErrorAt f "expected `fst` or `snd`"

def bin (op : Name) (a b : Term) : MacroM Term :=
  `(OM.Impl.Exp.bin $(mkIdent (`OM.Machine.BinOp ++ op)) $a $b)

partial def expE (s : Syntax) : MacroM Term := do
  match s.getKind with
  | ``eNum => `(($(⟨s[0]⟩) : OM.Impl.Exp))
  | ``eVar =>
    match dotted s[0] with
    | some ("P", k) => `(OM.Impl.Exp.prm $(mkIdent (`OM.Impl.PF ++ k)))
    | some ("S", k) => `(OM.Impl.Exp.sc $(mkIdent (`OM.Impl.SF ++ k)))
    | some ("O", k) => `(OM.Impl.Exp.opt $(mkIdent (`OM.Impl.OF ++ k)))
    | _ => `(OM.Impl.Exp.var $(str s[0]))
  | ``ePar => expE s[1]
  | ``eTm => `(($(⟨s[1]⟩) : OM.Impl.Exp))
  | ``eFld =>
    let i ← expE s[2]
    match s[0].getId with
    | `E => `(OM.Impl.Exp.eF $(← expF `OM.Impl.EF s[5]) $i)
    | `G => `(OM.Impl.Exp.gF $(← expF `OM.Impl.GF s[5]) $i)
    | `C => `(OM.Impl.Exp.cF $(← expF `OM.Impl.CF s[5]) $i)
    | `N => `(OM.Impl.Exp.rd (OM.Impl.Fld.n $(← expF `OM.Impl.NF s[5])) $i)
    | _ => Macro.throwErrorAt s[0] "expected a table: E, G, C or N"
  | ``eArr =>
    if isLK s[0] then Macro.throwErrorAt s "a list is not a value; use `len` or `[j].fst`"
    `(OM.Impl.Exp.rd (OM.Impl.Fld.a $(mkIdent (`OM.Impl.AF ++ s[0].getId))) $(← expE s[2]))
  | ``eLst => `(OM.Impl.Exp.lrd $(lk s[0]) $(← sndOf s[8]) $(← expE s[2]) $(← expE s[5]))
  | ``eLen => `(OM.Impl.Exp.llen $(lk s[1]) $(← expE s[3]))
  | ``eSize => `(OM.Impl.Exp.size $(mkIdent (`OM.Impl.Tbl ++ s[1].getId)))
  | ``ePath => `(OM.Impl.Exp.prd $(← expE s[2]) $(← expE s[4]))
  | ``eMax => `(OM.Impl.Exp.max $(← expE s[2]) $(← expE s[4]))
  | ``eMsb => `(OM.Impl.Exp.un OM.Machine.UnOp.msb $(← expE s[2]))
  | ``eMonus => `(OM.Impl.Exp.monus $(← expE s[0]) $(← expE s[2]))
  | ``eNot => `(OM.Impl.Exp.un OM.Machine.UnOp.not $(← expE s[1]))
  | ``eShl => bin `shl (← expE s[0]) (← expE s[2])
  | ``eShr => bin `shr (← expE s[0]) (← expE s[2])
  | ``eMul => `(($(← expE s[0]) * $(← expE s[2]) : OM.Impl.Exp))
  | ``eDiv => `(($(← expE s[0]) / $(← expE s[2]) : OM.Impl.Exp))
  | ``eMod => `(($(← expE s[0]) % $(← expE s[2]) : OM.Impl.Exp))
  | ``eAdd => `(($(← expE s[0]) + $(← expE s[2]) : OM.Impl.Exp))
  | ``eSub => `(($(← expE s[0]) - $(← expE s[2]) : OM.Impl.Exp))
  | ``eLt => bin `lt (← expE s[0]) (← expE s[2])
  | ``eLe => bin `le (← expE s[0]) (← expE s[2])
  | ``eEq => bin `eq (← expE s[0]) (← expE s[2])
  | ``eNe => do `(OM.Impl.Exp.un OM.Machine.UnOp.not $(← bin `eq (← expE s[0]) (← expE s[2])))
  | ``eAnd => bin `and (← expE s[0]) (← expE s[2])
  | ``eOr => bin `or (← expE s[0]) (← expE s[2])
  | _ => Macro.throwErrorAt s "unexpected expression"

def expArgs (args : Syntax) : MacroM Term := do
  let es ← args.getSepArgs.mapM expE
  `([$es,*])

/-- `p.call [args] [dsts]`. -/
def call (p args : Syntax) (ds : Array Syntax) : MacroM Term := do
  let p : Term := ⟨p⟩
  let as ← expArgs args
  let ds : Array Term := ds.map str
  `(OM.Impl.Proc.call $p $as [$ds,*])

mutual

partial def expSeq (ss : Array Syntax) : MacroM Term := do
  let some last := ss.back? | Macro.throwError "empty block"
  ss.pop.foldrM (fun s acc => do `(OM.Impl.Stm.seq $(← expS s) $acc)) (← expS last)

partial def expS (s : Syntax) : MacroM Term := do
  match s.getKind with
  | ``sId =>
    match s[0].getId with
    | `skip => `(OM.Impl.Stm.skip)
    | `fail => `(OM.Impl.Stm.fail)
    | `bug => `(OM.Impl.Stm.bug)
    | `prepCommit => `(OM.Impl.Stm.prepCommit)
    | `jobClear => `(OM.Impl.Stm.jobClear)
    | _ => pure ⟨s[0]⟩
  | ``sTm => `(($(⟨s[1]⟩) : OM.Impl.Stm))
  | ``sBlk => expSeq s[1][0].getSepArgs
  | ``sAsg =>
    match dotted s[0] with
    | some ("S", k) => `(OM.Impl.Stm.wsc $(mkIdent (`OM.Impl.SF ++ k)) $(← expE s[2]))
    | _ => `(OM.Impl.Stm.assign $(str s[0]) $(← expE s[2]))
  | ``sAsgT => `(OM.Impl.Stm.assign $(⟨s[1]⟩) $(← expE s[4]))
  | ``sNew => `(OM.Impl.Stm.push $(mkIdent (`OM.Impl.Tbl ++ s[3].getId)) $(str s[0]))
  | ``sFld =>
    let i ← expE s[2]
    let e ← expE s[7]
    match s[0].getId with
    | `E => `(OM.Impl.Stm.weF $(← expF `OM.Impl.EF s[5]) $i $e)
    | `G => `(OM.Impl.Stm.wgF $(← expF `OM.Impl.GF s[5]) $i $e)
    | `C => `(OM.Impl.Stm.wcF $(← expF `OM.Impl.CF s[5]) $i $e)
    | `N => `(OM.Impl.Stm.wr (OM.Impl.Fld.n $(← expF `OM.Impl.NF s[5])) $i $e)
    | _ => Macro.throwErrorAt s[0] "expected a table: E, G, C or N"
  | ``sArr =>
    let a := mkIdent (`OM.Impl.AF ++ s[0].getId)
    `(OM.Impl.Stm.wr (OM.Impl.Fld.a $a) $(← expE s[2]) $(← expE s[5]))
  | ``sLst =>
    `(OM.Impl.Stm.lwr $(lk s[0]) $(← sndOf s[8]) $(← expE s[2]) $(← expE s[5]) $(← expE s[10]))
  | ``sApp => `(OM.Impl.Stm.lgrow $(lk s[1]) $(← expE s[3]) $(← expE s[6]) $(← expE s[8]))
  | ``sPop => `(OM.Impl.Stm.lshrink $(lk s[1]) $(← expE s[3]))
  | ``sClr => `(OM.Impl.Stm.lclear $(lk s[1]) $(← expE s[3]))
  | ``sIf =>
    let c ← expE s[1]
    let t ← expS s[3]
    let e ← if s[4].getNumArgs == 0 then `(OM.Impl.Stm.skip) else expS s[4][1]
    `(OM.Impl.Stm.ite $c $t $e)
  | ``sFor => `(OM.Impl.Stm.loop $(str s[1]) $(← expE s[3]) $(← expS s[5]))
  | ``sTry => `(OM.Impl.Stm.catch $(← expS s[1]) $(← expS s[3]))
  | ``sPath => `(OM.Impl.Stm.pwr $(← expE s[2]) $(← expE s[4]) $(← expE s[7]))
  | ``sCon =>
    unless s[0].getId ∈ [`rowReset, `prepInit, `prepSet, `prepPath, `jobSet, `pcSet] do
      Macro.throwErrorAt s[0] "not a statement constructor; call a procedure with `call p(…)`"
    let args ← s[2].getSepArgs.mapM expE
    `($(mkIdent (`OM.Impl.Stm ++ s[0].getId)) $args*)
  | ``sCall1 => call s[2] s[4] #[(s[0])]
  | ``sCallN => call s[4] s[6] s[1].getSepArgs
  | ``sCall0 => call s[1] s[3] #[]
  | ``sCall1T => call s[3] s[6] #[(s[0])]
  | ``sCallNT => call s[5] s[8] s[1].getSepArgs
  | ``sCall0T => call s[2] s[5] #[]
  | _ => Macro.throwErrorAt s "unexpected statement"

end

syntax (name := cmStm) "cm{" cmSeq "}" : term
syntax (name := cmExp) "cme{" cmE "}" : term

@[macro cmStm] def expandStm : Macro := fun s => expSeq s[1][0].getSepArgs
@[macro cmExp] def expandExp : Macro := fun s => expE s[1]

end OM.Impl.CM
