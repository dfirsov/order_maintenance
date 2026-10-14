import Lean.Data.Json
import OM.Model

/-!
# Trace replay: Level F against the Python prototype

    lake exe replay TRACE.jsonl...

Reads traces written by `prototype/trace.py`, runs the Level F model on the same operations,
and checks every answer, every inserted key, every counter and every state digest. Stops at the
first mismatch of a trace and exits with code 1 if any trace failed.
-/

open Lean OM.Model

namespace OM.Test

def MOD : Nat := 2 ^ 61 - 1

def digestCore (c : Core) : Except String Nat :=
  match (do
      let es ← elements
      let mut h := 0
      for e in es do
        let (a, b, d) ← key e
        for v in [a, b, d] do
          h := (h * 1000003 + v) % MOD
      return h : CM Nat).run c with
  | .ok h _ => .ok h
  | .error e _ => .error s!"digest: {repr e}"

def digests (om : OM) : Except String (Nat × Int) := do
  let d1 ← digestCore om.cur
  let d2 : Int ← match om.nxt with
    | some n => if om.cursorSet then (Int.ofNat <$> digestCore n) else pure (-1)
    | none => pure (-1)
  return (d1, d2)

def getNat (j : Json) (i : Nat) : Except String Nat := do
  (← j.getArrVal? i).getNat?

def getInt (j : Json) (i : Nat) : Except String Int := do
  (← j.getArrVal? i).getInt?

def parseParams (j : Json) : Except String Params := do
  let f (k : String) : Except String Nat := j.getObjValAs? Nat k
  return { N := ← f "N", L := ← f "L", G := ← f "G", T := ← f "T", theta := ← f "theta",
           B_e := ← f "B_e", B_g := ← f "B_g", D_e := ← f "D_e", D_g := ← f "D_g",
           K_G := ← f "K_G", K_C := ← f "K_C", K_R := ← f "K_R", a := ← f "a", s := ← f "s",
           beta := ← f "beta", H := ← f "H" }

def liftW {α : Type} (x : WM α) : Except String α :=
  match x with
  | .ok a => .ok a
  | .error (.guard m) => .error s!"uncaught guard failure: {m}"
  | .error (.bug m) => .error s!"model bug (the prototype would crash): {m}"

def expect {α : Type} [BEq α] [Repr α] (what : String) (got want : α) : Except String Unit :=
  if got == want then pure () else .error s!"{what}: model {repr got}, prototype {repr want}"

def checkCounters (om : OM) (j : Json) : Except String Unit := do
  let want : List Int := [← getInt j 0, ← getInt j 1, ← getInt j 2]
  let got : List Int := [om.cur.fallbacks,
    match om.nxt with | some n => (n.fallbacks : Int) | none => -1, om.rebuilds]
  expect "counters [cur fallbacks, nxt fallbacks, rebuilds]" got want

def checkDigests (om : OM) (j : Json) : Except String Unit := do
  if j.isNull then return
  let (d1, d2) ← digests om
  expect "digest of cur" d1 (← getNat j 0)
  expect "digest of nxt" d2 (← getInt j 1)

def step (mk : Nat → Params) (om : OM) (r : Json) : Except String OM := do
  let tag ← (← r.getArrVal? 0).getStr?
  match tag with
  | "i" =>
    let x ← getInt r 1
    let (h, om) ← liftW (om.insert mk (if x < 0 then none else some x.toNat))
    expect "handle" h (← getNat r 2)
    let k ← r.getArrVal? 3
    let ((a, b, c), _) ← liftW (runCore om.cur (key (om.curIdx.getX h)))
    expect "key of the new element" [a, b, c] [← getNat k 0, ← getNat k 1, ← getNat k 2]
    checkCounters om (← r.getArrVal? 4)
    checkDigests om (← r.getArrVal? 5)
    return om
  | "d" =>
    let om ← liftW (om.delete mk (← getNat r 1))
    checkCounters om (← r.getArrVal? 2)
    checkDigests om (← r.getArrVal? 3)
    return om
  | "o" =>
    let ans ← liftW (om.order (← getNat r 1) (← getNat r 2))
    expect "order answer" ans (← (← r.getArrVal? 3).getBool?)
    return om
  | "f" =>
    checkDigests om (← r.getArrVal? 1)
    return om
  | t => .error s!"unknown record {t}"

/-- Replay one trace; returns the number of records, or the first mismatch. -/
def replay (path : System.FilePath) : IO (Except String Nat) := do
  let lines := (← IO.FS.lines path).filter (· ≠ "")
  let some hdrLine := lines[0]? | return .error "empty trace"
  let run : Except String Nat := do
    let hdr ← Json.parse hdrLine
    let ps ← (← hdr.getObjValAs? (Array Json) "params").mapM parseParams
    let KB ← hdr.getObjValAs? Nat "K_B"
    let mk (N : Nat) : Params := (ps.find? (·.N == N)).getD default
    let mut om ← liftW (OM.init mk KB)
    let mut i := 0
    for line in lines.drop 1 do
      i := i + 1
      let r ← Json.parse line
      match step mk om r with
      | .ok om' => om := om'
      | .error e => throw s!"record {i} {line.take 120}: {e}"
    return i
  return run

def main (args : List String) : IO UInt32 := do
  let mut failed := 0
  for a in args do
    let t0 ← IO.monoMsNow
    match ← replay a with
    | .ok n => IO.println s!"OK   {a}: {n} records ({(← IO.monoMsNow) - t0} ms)"
    | .error e =>
      IO.println s!"FAIL {a}: {e}"
      failed := failed + 1
  IO.println s!"{args.length - failed}/{args.length} traces replayed exactly"
  return if failed == 0 then 0 else 1

end OM.Test

def main (args : List String) : IO UInt32 := OM.Test.main args
