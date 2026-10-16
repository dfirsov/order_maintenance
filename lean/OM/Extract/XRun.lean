import OM.Impl.TheoremsM

/-!
# Cross-check: the machine semantics itself on an operation file

    lake exe xrun OPS.txt

Runs `initWS` and then `opS op` for each operation of the file with the machine's own semantics
(`OM.Machine.exec`), and prints one line per step of the run: the cost, the answer and the bit
length of the largest value computed so far. `rust/src/bin/xrun.rs` prints the same lines for the
generated Rust code, so the two outputs must be identical.

File format, one operation per line: `f` (insert first), `a X` (insert after X), `d X` (delete X),
`o X Y` (order).
-/

open OM.Machine OM.Impl

def bits (n : Nat) : Nat := if n = 0 then 0 else Nat.log2 n + 1

def parseOp (l : String) : Option OM.Spec.Op :=
  match (l.splitOn " ").filter (· ≠ "") with
  | ["f"] => some .insertFirst
  | ["a", x] => x.toNat?.map .insertAfter
  | ["d", x] => x.toNat?.map .delete
  | ["o", x, y] => do some (.order (← x.toNat?) (← y.toNat?))
  | _ => none

def ansStr : OM.Spec.Op → State → String
  | .insertFirst, m | .insertAfter _, m => s!"h{m.loc "hy"}"
  | .delete _, _ => "-"
  | .order _ _, m => if m.loc "r" ≠ 0 then "true" else "false"

def statusStr : Status → String
  | .ok => "ok" | .fail => "fail" | .err => "err"

def main (args : List String) : IO Unit := do
  let ops ← (← IO.FS.lines (args.headD "ops.txt")).toList.filterMapM fun l => pure (parseOp l)
  let m0 : State := { State.init with loc := State.upd State.init.loc "kb" 4 }
  let o := exec initWS m0
  IO.println s!"init {statusStr o.status} {o.cost} {bits o.st.peak}"
  let mut m := o.st
  for op in ops do
    let o := exec (opS op) m
    IO.println s!"{statusStr o.status} {o.cost} {ansStr op o.st} {bits o.st.peak}"
    m := o.st
