import OM.Impl.Lang

/-!
# M6: compiling the core language to the machine

**Layout.** The core in slot `p` (0 or 1) owns the machine arrays `1000·p + code`:
* one array per record field (codes 10–99), indexed by record, of capacity `κ.tbl`;
* one array per plain number array (`AF`), of capacity `κ.arr`;
* one single-cell array per scalar, and per table size (codes 100–103);
* the parameters, one cell each (code 110).

`Enc p κ s m` says that machine state `m` holds core `s` in slot `p`.
-/

namespace OM.Impl

open OM.Model
open OM.Machine (Reg Arr BinOp UnOp)

/-! ### Codes -/

def EF.idx : EF → Nat
  | .next => 0 | .prev => 1 | .grp => 2 | .lab => 3 | .dead => 4 | .h => 5
def GF.idx : GF → Nat
  | .next => 0 | .prev => 1 | .first => 2 | .last => 3 | .chk => 4 | .lab => 5 | .size => 6
  | .st => 7 | .src => 8 | .l => 9 | .r => 10 | .dead => 11
def CF.idx : CF → Nat
  | .next => 0 | .prev => 1 | .first => 2 | .last => 3 | .size => 4 | .st => 5 | .src => 6
  | .l => 7 | .r => 8 | .tag => 9 | .dead => 10
def NF.idx : NF → Nat
  | .height => 0 | .livePar => 1 | .weight => 2 | .first => 3 | .last => 4 | .draining => 5
  | .t1 => 6 | .t2 => 7 | .overflow => 8 | .dead => 9
def AF.idx : AF → Nat
  | .pqHead => 0 | .pqNext => 1 | .pqPrev => 2 | .pqWhere => 3 | .nbNext => 4 | .nbPrev => 5
  | .lpar => 6
def SF.idx : SF → Nat
  | .count => 0 | .head => 1 | .tail => 2 | .firstGroup => 3 | .firstChunk => 4 | .notReady => 5
  | .fallbacks => 6 | .pqHi => 7 | .pqLo => 8 | .pqScan => 9
def Tbl.idx : Tbl → Nat
  | .E => 0 | .G => 1 | .C => 2 | .N => 3
def PF.idx : PF → Nat
  | .N => 0 | .L => 1 | .G => 2 | .T => 3 | .theta => 4 | .Be => 5 | .Bg => 6 | .De => 7
  | .Dg => 8 | .KG => 9 | .KC => 10 | .KR => 11 | .a => 12 | .s => 13 | .beta => 14 | .H => 15

theorem EF.idx_inj {k k' : EF} (h : k.idx = k'.idx) : k = k' := by
  cases k <;> cases k' <;> first | rfl | (simp [EF.idx] at h)
theorem GF.idx_inj {k k' : GF} (h : k.idx = k'.idx) : k = k' := by
  cases k <;> cases k' <;> first | rfl | (simp [GF.idx] at h)
theorem CF.idx_inj {k k' : CF} (h : k.idx = k'.idx) : k = k' := by
  cases k <;> cases k' <;> first | rfl | (simp [CF.idx] at h)
theorem NF.idx_inj {k k' : NF} (h : k.idx = k'.idx) : k = k' := by
  cases k <;> cases k' <;> first | rfl | (simp [NF.idx] at h)
theorem AF.idx_inj {k k' : AF} (h : k.idx = k'.idx) : k = k' := by
  cases k <;> cases k' <;> first | rfl | (simp [AF.idx] at h)
theorem SF.idx_inj {k k' : SF} (h : k.idx = k'.idx) : k = k' := by
  cases k <;> cases k' <;> first | rfl | (simp [SF.idx] at h)
theorem Tbl.idx_inj {k k' : Tbl} (h : k.idx = k'.idx) : k = k' := by
  cases k <;> cases k' <;> first | rfl | (simp [Tbl.idx] at h)

theorem EF.idx_lt (k : EF) : k.idx < 6 := by cases k <;> decide
theorem GF.idx_lt (k : GF) : k.idx < 12 := by cases k <;> decide
theorem CF.idx_lt (k : CF) : k.idx < 11 := by cases k <;> decide
theorem NF.idx_lt (k : NF) : k.idx < 10 := by cases k <;> decide
theorem AF.idx_lt (k : AF) : k.idx < 7 := by cases k <;> decide
theorem SF.idx_lt (k : SF) : k.idx < 10 := by cases k <;> decide
theorem Tbl.idx_lt (k : Tbl) : k.idx < 4 := by cases k <;> decide
theorem PF.idx_lt (k : PF) : k.idx < 16 := by cases k <;> decide

def Fld.code : Fld → Nat
  | .e k => 10 + k.idx | .g k => 20 + k.idx | .c k => 40 + k.idx | .n k => 60 + k.idx
  | .a k => 80 + k.idx | .s k => 90 + k.idx

theorem Fld.code_lt (f : Fld) : 10 ≤ f.code ∧ f.code < 100 := by
  cases f with
  | e k => have := k.idx_lt; simp [Fld.code]; omega
  | g k => have := k.idx_lt; simp [Fld.code]; omega
  | c k => have := k.idx_lt; simp [Fld.code]; omega
  | n k => have := k.idx_lt; simp [Fld.code]; omega
  | a k => have := k.idx_lt; simp [Fld.code]; omega
  | s k => have := k.idx_lt; simp [Fld.code]; omega

theorem Fld.code_inj {f g : Fld} (h : f.code = g.code) : f = g := by
  cases f with
  | e k => cases g with
    | e k' => simp [Fld.code] at h; rw [EF.idx_inj h]
    | _ k' => have := k.idx_lt; have := k'.idx_lt; simp [Fld.code] at h; omega
  | g k => cases g with
    | g k' => simp [Fld.code] at h; rw [GF.idx_inj h]
    | _ k' => have := k.idx_lt; have := k'.idx_lt; simp [Fld.code] at h; omega
  | c k => cases g with
    | c k' => simp [Fld.code] at h; rw [CF.idx_inj h]
    | _ k' => have := k.idx_lt; have := k'.idx_lt; simp [Fld.code] at h; omega
  | n k => cases g with
    | n k' => simp [Fld.code] at h; rw [NF.idx_inj h]
    | _ k' => have := k.idx_lt; have := k'.idx_lt; simp [Fld.code] at h; omega
  | a k => cases g with
    | a k' => simp [Fld.code] at h; rw [AF.idx_inj h]
    | _ k' => have := k.idx_lt; have := k'.idx_lt; simp [Fld.code] at h; omega
  | s k => cases g with
    | s k' => simp [Fld.code] at h; rw [SF.idx_inj h]
    | _ k' => have := k.idx_lt; have := k'.idx_lt; simp [Fld.code] at h; omega

/-- The machine array of field `f` in slot `p`. -/
def arrF (p : Nat) (f : Fld) : Arr := 1000 * p + f.code
/-- The machine cell holding the size of table `t`. -/
def arrS (p : Nat) (t : Tbl) : Arr := 1000 * p + 100 + t.idx
/-- The machine array of the parameters. -/
def arrP (p : Nat) : Arr := 1000 * p + 110

theorem arrF_inj {p : Nat} {f g : Fld} (h : arrF p f = arrF p g) : f = g := by
  have h' : (1000 * p + f.code : Nat) = 1000 * p + g.code := h
  exact Fld.code_inj (by omega)
theorem arrF_ne_arrS (p : Nat) (f : Fld) (t : Tbl) : arrF p f ≠ arrS p t := by
  have := f.code_lt
  change (1000 * p + f.code : Nat) ≠ 1000 * p + 100 + t.idx; omega
theorem arrF_ne_arrP (p : Nat) (f : Fld) : arrF p f ≠ arrP p := by
  have := f.code_lt
  change (1000 * p + f.code : Nat) ≠ 1000 * p + 110; omega
theorem arrS_inj {p : Nat} {t t' : Tbl} (h : arrS p t = arrS p t') : t = t' := by
  have h' : (1000 * p + 100 + t.idx : Nat) = 1000 * p + 100 + t'.idx := h
  exact Tbl.idx_inj (by omega)
theorem arrS_ne_arrP (p : Nat) (t : Tbl) : arrS p t ≠ arrP p := by
  have := t.idx_lt
  change (1000 * p + 100 + t.idx : Nat) ≠ 1000 * p + 110; omega

/-! ### Compilation -/

def Exp.compile (p : Nat) : Exp → OM.Machine.Expr
  | .lit n => .lit n
  | .var x => .var x
  | .rd f i => .load (arrF p f) (i.compile p)
  | .size t => .load (arrS p t) (.lit 0)
  | .prm k => .load (arrP p) (.lit k.idx)
  | .bin op a b => .bin op (a.compile p) (b.compile p)
  | .un op a => .un op (a.compile p)

def Stm.compile (p : Nat) : Stm → OM.Machine.Stmt
  | .skip => .skip
  | .assign x e => .assign x (e.compile p)
  | .wr f i e => .store (arrF p f) (i.compile p) (e.compile p)
  | .push t x =>
    .seq (.assign x (.load (arrS p t) (.lit 0)))
      (.store (arrS p t) (.lit 0) (.bin .add (.var x) (.lit 1)))
  | .seq c d => .seq (c.compile p) (d.compile p)
  | .ite c t f => .ite (c.compile p) (t.compile p) (f.compile p)
  | .loop x n b => .loop x (n.compile p) (b.compile p)
  | .call nm ps b rs args ds => .call nm ps (b.compile p) rs (args.map (Exp.compile p)) ds
  | .fail => .fail
  | .bug => .assign "bug" (.bin .sub (.lit 0) (.lit 1))
  | .catch c h => .catch (c.compile p) (h.compile p)

theorem Exp.cost_compile (p : Nat) (e : Exp) : (e.compile p).cost = e.cost := by
  induction e with
  | lit | var | size | prm => rfl
  | rd f i ih => simp [Exp.compile, OM.Machine.Expr.cost, Exp.cost, ih]
  | bin op a b iha ihb => simp [Exp.compile, OM.Machine.Expr.cost, Exp.cost, iha, ihb]
  | un op a ih => simp [Exp.compile, OM.Machine.Expr.cost, Exp.cost, ih]

/-! ### The encoding -/

/-- Machine state `m` holds core `s` in slot `p`, with capacities `κ`. -/
structure Enc (p : Nat) (κ : Caps) (s : Core) (m : OM.Machine.State) : Prop where
  cap : ∀ f : Fld, m.cap (arrF p f) = f.cap κ
  mem : ∀ f : Fld, ∀ i < f.cap κ, m.mem (arrF p f) i = f.get s i
  scap : ∀ t, m.cap (arrS p t) = 1
  smem : ∀ t, m.mem (arrS p t) 0 = t.size s
  sle : ∀ t, t.size s ≤ κ.tbl t
  pcap : m.cap (arrP p) = 16
  pmem : ∀ k : PF, m.mem (arrP p) k.idx = k.get s.P

end OM.Impl
