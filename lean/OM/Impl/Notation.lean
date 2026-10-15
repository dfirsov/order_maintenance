import OM.Impl.Sim

/-!
# M6: notation for the core language, and procedures
-/

namespace OM.Impl

open OM.Model
open OM.Machine (Reg BinOp UnOp)

instance {n : Nat} : OfNat Exp n := ⟨.lit n⟩
instance : Coe Reg Exp := ⟨.var⟩
instance : Add Exp := ⟨.bin .add⟩
instance : Sub Exp := ⟨.bin .sub⟩
instance : Mul Exp := ⟨.bin .mul⟩
instance : Div Exp := ⟨.bin .div⟩
instance : Mod Exp := ⟨.bin .mod⟩

@[simp] theorem Exp.ofNat_def (n : Nat) : (OfNat.ofNat n : Exp) = .lit n := rfl
@[simp] theorem Exp.add_def (a b : Exp) : a + b = .bin .add a b := rfl
@[simp] theorem Exp.sub_def (a b : Exp) : a - b = .bin .sub a b := rfl
@[simp] theorem Exp.mul_def (a b : Exp) : a * b = .bin .mul a b := rfl
@[simp] theorem Exp.div_def (a b : Exp) : a / b = .bin .div a b := rfl
@[simp] theorem Exp.mod_def (a b : Exp) : a % b = .bin .mod a b := rfl

infix:50 " <ₑ " => Exp.bin BinOp.lt
infix:50 " ≤ₑ " => Exp.bin BinOp.le
infix:50 " =ₑ " => Exp.bin BinOp.eq
infixr:35 " &&ₑ " => Exp.bin BinOp.and
infixr:30 " ||ₑ " => Exp.bin BinOp.or
prefix:max "!ₑ" => Exp.un UnOp.not

infixr:20 " ;; " => Stm.seq
infix:40 " ::= " => Stm.assign

/-- `max a b`, without branches. -/
def Exp.max (a b : Exp) : Exp := (a <ₑ b) * b + (1 - (a <ₑ b)) * a
/-- Truncated subtraction (Level F's `-` on `Nat`). -/
def Exp.monus (a b : Exp) : Exp := Exp.max a b - b
/-- `if c then a else 0`, for a condition `c` worth 0 or 1. -/
def Exp.ifz (c a : Exp) : Exp := c * a

/-- Scalar `k` of the core. -/
def Exp.sc (k : SF) : Exp := .rd (.s k) 0
def Stm.wsc (k : SF) (e : Exp) : Stm := .wr (.s k) 0 e
def Exp.ar (k : AF) (i : Exp) : Exp := .rd (.a k) i
def Stm.war (k : AF) (i e : Exp) : Stm := .wr (.a k) i e

theorem Exp.ev_max (κ : Caps) (s : Core) (L : Loc) {a b : Exp} {x y : Nat} (ha : a.ev κ s L = some x)
    (hb : b.ev κ s L = some y) : (Exp.max a b).ev κ s L = some (Nat.max x y) := by
  simp only [Exp.max, Exp.ev, ha, hb, Option.bind_some, OM.Machine.BinOp.eval, Exp.add_def,
    Exp.mul_def, Exp.sub_def, Exp.ofNat_def]
  by_cases h : x < y
  · simp [h]; omega
  · simp [h]; omega

theorem Exp.ev_monus (κ : Caps) (s : Core) (L : Loc) {a b : Exp} {x y : Nat} (ha : a.ev κ s L = some x)
    (hb : b.ev κ s L = some y) : (Exp.monus a b).ev κ s L = some (x - y) := by
  simp only [Exp.monus, Exp.sub_def, Exp.ev, Exp.ev_max κ s L ha hb, hb, Option.bind_some,
    OM.Machine.BinOp.eval]
  have h1 : y ≤ Nat.max x y := Nat.le_max_right x y
  have h2 : Nat.max x y = if x ≤ y then y else x := rfl
  rw [if_pos h1]; congr 1; split at h2 <;> omega

@[simp] theorem Exp.cost_monus (a b : Exp) : (Exp.monus a b).cost = 8 + 3 * a.cost + 4 * b.cost := by
  simp [Exp.monus, Exp.max, Exp.cost]; omega

/-- A procedure of the core language. -/
structure Proc where
  name : String
  params : List Reg
  rets : List Reg
  body : Stm

def Proc.call (q : Proc) (args : List Exp) (dsts : List Reg) : Stm :=
  .call q.name q.params q.body q.rets args dsts

end OM.Impl

namespace OM.Impl

open OM.Model

/-! ### Stepping through `evalF` -/

theorem evalF_seq_ok {κ : Caps} {A B : Stm} {s s1 : Core} {L L1 : Loc} {c1 : Nat}
    (h : evalF κ A s L = .ok s1 L1 c1) : evalF κ (A ;; B) s L = (evalF κ B s1 L1).addCost c1 := by
  simp [evalF, h, Res.bind]

theorem evalF_call_ok {κ : Caps} {q : Proc} {args : List Exp} {ds : List OM.Machine.Reg} {s s' : Core}
    {L L' : Loc} {vs : List Nat} {c : Nat} (ha : evList κ s L args = some vs)
    (hb : evalF κ q.body s (OM.Machine.State.setLocs (fun _ => 0) q.params vs) = .ok s' L' c) :
    evalF κ (q.call args ds) s L =
      .ok s' (OM.Machine.State.setLocs L ds (q.rets.map L')) (1 + costList args + ds.length + c) := by
  simp [Proc.call, evalF, ha, hb]

theorem Res.addCost_ok {s : Core} {L : Loc} {c c' : Nat} : (Res.ok s L c').addCost c = .ok s L (c + c') :=
  rfl

/-- A Level F `bind` that succeeded: both parts succeeded. -/
theorem run_bind_ok {α β : Type} {m : CM α} {f : α → CM β} {s s' : Core} {b : β}
    (h : (m >>= f).run s = .ok b s') : ∃ a s1, m.run s = .ok a s1 ∧ (f a).run s1 = .ok b s' := by
  rw [OM.Proof.run_bind] at h
  revert h
  cases m.run s with
  | ok a s1 => intro h; exact ⟨a, s1, rfl, h⟩
  | error e s1 => intro h; simp at h

end OM.Impl
