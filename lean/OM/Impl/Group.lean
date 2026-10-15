import OM.Impl.Elem
import OM.Impl.StartDrain

/-!
# M6: groups (`Model/Core.lean`: group splits)

Each procedure is a sequence of field writes. A write is a `modify` of one record
(`evalF_wrG_ok` …), consecutive writes to one record merge (`Array.modify_modify_same`), and the
blocks follow Level F's `let`s, so a conditional write needs a two-way split only.
-/

namespace OM.Impl

open OM.Model
open OM.Machine (Reg BinOp UnOp)
open OM.Proof.Top (getX_modify')

local notation "upd" => OM.Machine.State.upd

/-! ### Writes -/

theorem evalF_wrG_ok {κ : Caps} {s : Core} {L : Loc} {k : GF} {i e : Exp} {j w : Nat} (hi : i.ev κ s L = some j)
    (he : e.ev κ s L = some w) (hj : j < s.Gs.size) (hc : j < κ.tbl .G) (hk : k.ok w = true) :
    evalF κ (.wr (.g k) i e) s L = .ok { s with Gs := s.Gs.modify j (GF.set · w k) } L (1 + i.cost + e.cost) := by
  simp [evalF, hi, he, Fld.set, hj, hk]

theorem evalF_wrC_ok {κ : Caps} {s : Core} {L : Loc} {k : CF} {i e : Exp} {j w : Nat} (hi : i.ev κ s L = some j)
    (he : e.ev κ s L = some w) (hj : j < s.C.size) (hc : j < κ.tbl .C) (hk : k.ok w = true) :
    evalF κ (.wr (.c k) i e) s L = .ok { s with C := s.C.modify j (CF.set · w k) } L (1 + i.cost + e.cost) := by
  simp [evalF, hi, he, Fld.set, hj, hk]

theorem evalF_wrS_ok {κ : Caps} {s : Core} {L : Loc} {k : SF} {e : Exp} {w : Nat}
    (he : e.ev κ s L = some w) (hk : k.ok w = true) :
    evalF κ (.wr (.s k) 0 e) s L = .ok (k.set s w) L (1 + 1 + e.cost) := by
  simp [evalF, he, Fld.set, hk, Exp.ev, Exp.cost]

/-! ### `linkGroupPair` -/

def lgpA0 : Stm :=
  .wgF .lab "gl" "labL" ;; .wgF .st "gl" 1 ;; .wgF .src "gl" "g" ;; .wgF .prev "gl" "gp" ;; .wgF .next "gl" "g"
def lgpA2 : Stm :=
  .wgF .lab "gr" "labR" ;; .wgF .st "gr" 1 ;; .wgF .src "gr" "g" ;; .wgF .prev "gr" "g" ;; .wgF .next "gr" "gn"
def lgpG : Stm :=
  .wgF .prev "g" "gl" ;; .wgF .next "g" "gr" ;; .wgF .st "g" 2 ;; .wgF .l "g" "gl" ;; .wgF .r "g" "gr"

/-- `linkGroupPair`: link `gl`, `gr` around `g` (locals `g gl gr labL labR`). -/
def linkGroupPairS : Stm :=
  "gp" ::= .gF .prev "g" ;; "gn" ::= .gF .next "g" ;; "c" ::= .gF .chk "g" ;;
  lgpA0 ;;
  .ite (!ₑ ("gp" =ₑ 0)) (.wgF .next "gp" "gl") .skip ;;
  lgpA2 ;;
  .ite (!ₑ ("gn" =ₑ 0)) (.wgF .prev "gn" "gr") .skip ;;
  .ite (.cF .first "c" =ₑ "g") (.wcF .first "c" "gl") .skip ;;
  lgpG ;;
  .ite (.cF .last "c" =ₑ "g") (.wcF .last "c" "gr") .skip ;;
  .ite ("gp" =ₑ 0) (.wsc .firstGroup "gl") .skip

/-- Five writes to one group. -/
theorem five_wrG {κ : Caps} {s : Core} {L : Loc} {x : Reg} {j : Nat} {k1 k2 k3 k4 k5 : GF} {e1 e2 e3 e4 e5 : Exp}
    {w1 w2 w3 w4 w5 : Nat} (hx : L x = j) (hj : j < s.Gs.size) (hc : j < κ.tbl .G)
    (h1 : ∀ s', e1.ev κ s' L = some w1) (h2 : ∀ s', e2.ev κ s' L = some w2) (h3 : ∀ s', e3.ev κ s' L = some w3)
    (h4 : ∀ s', e4.ev κ s' L = some w4) (h5 : ∀ s', e5.ev κ s' L = some w5)
    (o1 : k1.ok w1 = true) (o2 : k2.ok w2 = true) (o3 : k3.ok w3 = true) (o4 : k4.ok w4 = true) (o5 : k5.ok w5 = true) :
    evalF κ (.wr (.g k1) (.var x) e1 ;; .wr (.g k2) (.var x) e2 ;; .wr (.g k3) (.var x) e3 ;;
      .wr (.g k4) (.var x) e4 ;; .wr (.g k5) (.var x) e5) s L =
      .ok { s with Gs := s.Gs.modify j (fun X =>
          GF.set (GF.set (GF.set (GF.set (GF.set X w1 k1) w2 k2) w3 k3) w4 k4) w5 k5) } L
        (5 + 5 + e1.cost + e2.cost + e3.cost + e4.cost + e5.cost) := by
  have hv : ∀ s' : Core, (Exp.var x).ev κ s' L = some j := fun _ => by simp [Exp.ev, hx]
  rw [evalF_seq_ok2 (evalF_wrG_ok (hv _) (h1 _) hj hc o1) (evalF_seq_ok2 (evalF_wrG_ok (hv _) (h2 _) (by simpa using hj) hc o2)
    (evalF_seq_ok2 (evalF_wrG_ok (hv _) (h3 _) (by simpa using hj) hc o3)
      (evalF_seq_ok2 (evalF_wrG_ok (hv _) (h4 _) (by simpa using hj) hc o4)
        (evalF_wrG_ok (hv _) (h5 _) (by simpa using hj) hc o5))))]
  simp only [Array.modify_modify_same, Function.comp_def, Exp.cost]
  congr 1; omega

theorem ite_skip_ok {κ : Caps} {c : Exp} {t : Stm} {s s' : Core} {L : Loc} {ct : Nat} (b : Bool)
    (hc : c.ev κ s L = some (if b then 1 else 0)) (ht : b = true → evalF κ t s L = .ok s' L ct) (hs : b = false → s' = s) :
    ∃ n, evalF κ (.ite c t .skip) s L = .ok s' L n ∧ n ≤ 1 + c.cost + max ct 1 := by
  cases b
  · obtain rfl := hs rfl; exact ⟨_, evalF_ite_f (by simpa using hc) evalF_skip, by omega⟩
  · exact ⟨_, evalF_ite_t (v := 1) (by simpa using hc) one_ne_zero (ht rfl), by omega⟩

/-- **`linkGroupPairS` computes `linkGroupPair`.** -/
theorem linkGroupPairS_agree (κ : Caps) (σ : Core) (L : Loc) {g gl gr labL labR : Nat} (hg : L "g" = g)
    (hgl : L "gl" = gl) (hgr : L "gr" = gr) (hlL : L "labL" = labL) (hlR : L "labR" = labR)
    (hgG : g < σ.Gs.size) (hglG : gl < σ.Gs.size) (hgrG : gr < σ.Gs.size)
    (hpG : (σ.Gs.getX g).prev < σ.Gs.size) (hnG : (σ.Gs.getX g).next < σ.Gs.size)
    (hcC : (σ.Gs.getX g).chk < σ.C.size) (hG : σ.Gs.size ≤ κ.tbl .G) (hC : σ.C.size ≤ κ.tbl .C) :
    ∃ L' n, evalF κ linkGroupPairS σ L = .ok (linkGroupPair σ g gl gr labL labR) L' n ∧ n ≤ 150 := by
  set G := σ.Gs.getX g
  set c := G.chk
  set C := σ.C.getX c
  have hgT : g < κ.tbl .G := by omega
  have e1 := evalF_assign_ok (κ := κ) (s := σ) (L := L) (x := "gp") (e := .gF .prev "g") (v := G.prev)
    (by simp [Exp.gF, Exp.ev, hg, Fld.cap, Fld.get, GF.get, G, hgT])
  have e2 := evalF_assign_ok (κ := κ) (s := σ) (L := upd L "gp" G.prev) (x := "gn") (e := .gF .next "g") (v := G.next)
    (by simp [Exp.gF, Exp.ev, OM.Machine.State.upd, hg, Fld.cap, Fld.get, GF.get, G, hgT])
  have e3 := evalF_assign_ok (κ := κ) (s := σ) (L := upd (upd L "gp" G.prev) "gn" G.next) (x := "c")
    (e := .gF .chk "g") (v := c) (by simp [Exp.gF, Exp.ev, OM.Machine.State.upd, hg, Fld.cap, Fld.get, GF.get, c, G, hgT])
  set L3 := upd (upd (upd L "gp" G.prev) "gn" G.next) "c" c
  have r : ∀ x, x ≠ "gp" → x ≠ "gn" → x ≠ "c" → L3 x = L x := fun x h1 h2 h3 => by
    simp [L3, OM.Machine.State.upd, h1, h2, h3]
  have rg := r "g" (by decide) (by decide) (by decide)
  have rgl := r "gl" (by decide) (by decide) (by decide)
  have rgr := r "gr" (by decide) (by decide) (by decide)
  have rlL := r "labL" (by decide) (by decide) (by decide)
  have rlR := r "labR" (by decide) (by decide) (by decide)
  have rgp : L3 "gp" = G.prev := by simp [L3, OM.Machine.State.upd]
  have rgn : L3 "gn" = G.next := by simp [L3, OM.Machine.State.upd]
  have rc : L3 "c" = c := by simp [L3, OM.Machine.State.upd]
  -- the left sibling
  set A0 := σ.Gs.modify gl fun X => { X with lab := labL, st := .overflow, src := g, prev := G.prev, next := g }
  have b1 : evalF κ lgpA0 σ L3 = .ok { σ with Gs := A0 } L3 15 := by
    simp only [lgpA0, Stm.wgF]
    rw [five_wrG (x := "gl") (j := gl) (w1 := labL) (w2 := 1) (w3 := g) (w4 := G.prev) (w5 := g) (by rw [rgl, hgl]) hglG (by omega) (fun _ => by simp [Exp.ev, rlL, hlL])
      (fun _ => rfl) (fun _ => by simp [Exp.ev, rg, hg]) (fun _ => by simp [Exp.ev, rgp])
      (fun _ => by simp [Exp.ev, rg, hg]) rfl rfl rfl rfl rfl]
    rfl
  -- the left neighbour
  set A1 := if G.prev != NIL then A0.modify G.prev (fun X => { X with next := gl }) else A0
  obtain ⟨n2, b2, hn2⟩ := ite_skip_ok (κ := κ) (c := !ₑ ("gp" =ₑ 0)) (t := .wgF .next "gp" "gl")
    (s := { σ with Gs := A0 }) (s' := { σ with Gs := A1 }) (L := L3) (ct := 3) (G.prev != NIL)
    (by by_cases h : G.prev = 0 <;> simp [Exp.ev, OM.Machine.BinOp.eval, OM.Machine.UnOp.eval, rgp, h, NIL])
    (fun hb => by
      have hb' : G.prev ≠ 0 := by simpa [NIL] using hb
      simp only [A1, hb, if_true, Stm.wgF]
      exact evalF_wrG_ok (by simp [Exp.ev, rgp]) (by simp [Exp.ev, rgl, hgl]) (by simp [A0]; exact hpG) (by omega) rfl)
    (fun hb => by simp [A1, hb])
  -- the right sibling
  set A2 := A1.modify gr fun X => { X with lab := labR, st := .overflow, src := g, prev := g, next := G.next }
  have hA1 : A1.size = σ.Gs.size := by simp only [A1, A0]; split <;> simp
  have b3 : evalF κ lgpA2 { σ with Gs := A1 } L3 = .ok { σ with Gs := A2 } L3 15 := by
    simp only [lgpA2, Stm.wgF]
    rw [five_wrG (x := "gr") (j := gr) (w1 := labR) (w2 := 1) (w3 := g) (w4 := g) (w5 := G.next)
      (by rw [rgr, hgr]) (by simp [hA1, hgrG]) (by omega) (fun _ => by simp [Exp.ev, rlR, hlR])
      (fun _ => rfl) (fun _ => by simp [Exp.ev, rg, hg]) (fun _ => by simp [Exp.ev, rg, hg])
      (fun _ => by simp [Exp.ev, rgn]) rfl rfl rfl rfl rfl]
    rfl
  have hA2 : A2.size = σ.Gs.size := by simp [A2, hA1]
  -- the right neighbour
  set A3 := if G.next != NIL then A2.modify G.next (fun X => { X with prev := gr }) else A2
  obtain ⟨n4, b4, hn4⟩ := ite_skip_ok (κ := κ) (c := !ₑ ("gn" =ₑ 0)) (t := .wgF .prev "gn" "gr")
    (s := { σ with Gs := A2 }) (s' := { σ with Gs := A3 }) (L := L3) (ct := 3) (G.next != NIL)
    (by by_cases h : G.next = 0 <;> simp [Exp.ev, OM.Machine.BinOp.eval, OM.Machine.UnOp.eval, rgn, h, NIL])
    (fun hb => by
      simp only [A3, hb, if_true, Stm.wgF]
      exact evalF_wrG_ok (by simp [Exp.ev, rgn]) (by simp [Exp.ev, rgr, hgr]) (by simp [hA2]; exact hnG) (by omega) rfl)
    (fun hb => by simp [A3, hb])
  have hA3 : A3.size = σ.Gs.size := by simp only [A3]; split <;> simp [hA2]
  -- the chunk's first group
  have hcT : c < κ.tbl .C := by omega
  set C1 := if C.first == g then σ.C.modify c (fun X => { X with first := gl }) else σ.C
  obtain ⟨n5, b5, hn5⟩ := ite_skip_ok (κ := κ) (c := .cF .first "c" =ₑ "g") (t := .wcF .first "c" "gl")
    (s := { σ with Gs := A3 }) (s' := { σ with Gs := A3, C := C1 }) (L := L3) (ct := 3) (C.first == g)
    (by simp [Exp.cF, Exp.ev, OM.Machine.BinOp.eval, rc, rg, hg, hcT, Fld.cap, Fld.get, CF.get, C])
    (fun hb => by
      simp only [C1, hb, if_true, Stm.wcF]
      exact evalF_wrC_ok (by simp [Exp.ev, rc]) (by simp [Exp.ev, rgl, hgl]) hcC hcT rfl)
    (fun hb => by simp [C1, hb])
  -- `g` itself
  set A4 := A3.modify g fun X => { X with prev := gl, next := gr, st := .splitting, l := gl, r := gr }
  have b6 : evalF κ lgpG { σ with Gs := A3, C := C1 } L3 = .ok { σ with Gs := A4, C := C1 } L3 15 := by
    simp only [lgpG, Stm.wgF]
    rw [five_wrG (x := "g") (j := g) (w1 := gl) (w2 := gr) (w3 := 2) (w4 := gl) (w5 := gr)
      (by rw [rg, hg]) (by simp [hA3, hgG]) (by omega) (fun _ => by simp [Exp.ev, rgl, hgl])
      (fun _ => by simp [Exp.ev, rgr, hgr]) (fun _ => rfl) (fun _ => by simp [Exp.ev, rgl, hgl])
      (fun _ => by simp [Exp.ev, rgr, hgr]) rfl rfl rfl rfl rfl]
    rfl
  -- the chunk's last group
  have hC1 : (C1.getX c).last = C.last := by simp only [C1]; split <;> simp [getX_modify', C]; split <;> rfl
  have hC1s : C1.size = σ.C.size := by simp only [C1]; split <;> simp
  set C2 := if C.last == g then C1.modify c (fun X => { X with last := gr }) else C1
  obtain ⟨n7, b7, hn7⟩ := ite_skip_ok (κ := κ) (c := .cF .last "c" =ₑ "g") (t := .wcF .last "c" "gr")
    (s := { σ with Gs := A4, C := C1 }) (s' := { σ with Gs := A4, C := C2 }) (L := L3) (ct := 3) (C.last == g)
    (by simp [Exp.cF, Exp.ev, OM.Machine.BinOp.eval, rc, rg, hg, hcT, Fld.cap, Fld.get, CF.get, hC1])
    (fun hb => by
      simp only [C2, hb, if_true, Stm.wcF]
      exact evalF_wrC_ok (by simp [Exp.ev, rc]) (by simp [Exp.ev, rgr, hgr]) (by rw [hC1s]; exact hcC) hcT rfl)
    (fun hb => by simp [C2, hb])
  -- the first group of the structure
  obtain ⟨n8, b8, hn8⟩ := ite_skip_ok (κ := κ) (c := "gp" =ₑ 0) (t := .wsc .firstGroup "gl")
    (s := { σ with Gs := A4, C := C2 })
    (s' := { σ with Gs := A4, C := C2, firstGroup := if G.prev != NIL then σ.firstGroup else gl }) (L := L3) (ct := 3)
    (G.prev == NIL)
    (by simp [Exp.ev, OM.Machine.BinOp.eval, rgp, NIL])
    (fun hb => by
      have hb' : G.prev = 0 := by simpa [NIL] using hb
      simp only [hb', NIL, bne_self_eq_false, Bool.false_eq_true, if_false, Stm.wsc]
      exact evalF_wrS_ok (κ := κ) (L := L3) (k := .firstGroup) (e := .var "gl") (w := gl)
        (by simp [Exp.ev, rgl, hgl]) rfl)
    (fun hb => by
      have hb' : (G.prev != NIL) = true := by simpa [NIL] using hb
      rw [if_pos hb'])
  refine ⟨L3, _, evalF_seq_ok2 e1 (evalF_seq_ok2 e2 (evalF_seq_ok2 e3 (evalF_seq_ok2 b1 (evalF_seq_ok2 b2
    (evalF_seq_ok2 b3 (evalF_seq_ok2 b4 (evalF_seq_ok2 b5 (evalF_seq_ok2 b6 (evalF_seq_ok2 b7 b8))))))))), ?_⟩
  simp only [Exp.cost, Exp.gF, Exp.cF] at hn2 hn4 hn5 hn7 hn8 ⊢
  omega

/-! ### `unlinkGroup` -/

def ulCE : Exp := ("cf" =ₑ "g") &&ₑ ("cl" =ₑ "g")
def ulG : Stm := .wgF .dead "g" 1 ;; .wgF .next "g" 0 ;; .wgF .prev "g" 0
/-- `unlinkGroup`: unlink `g` from the group list and its chunk, and free it (local `g`). -/
def unlinkGroupS : Stm :=
  "gp" ::= .gF .prev "g" ;; "gn" ::= .gF .next "g" ;; "c" ::= .gF .chk "g" ;;
  .ite (!ₑ ("gp" =ₑ 0)) (.wgF .next "gp" "gn") .skip ;;
  .ite (!ₑ ("gn" =ₑ 0)) (.wgF .prev "gn" "gp") .skip ;;
  ulG ;;
  "cf" ::= .cF .first "c" ;; "cl" ::= .cF .last "c" ;;
  .ite ulCE (.wcF .first "c" 0 ;; .wcF .last "c" 0)
    (.ite ("cf" =ₑ "g") (.wcF .first "c" "gn") (.ite ("cl" =ₑ "g") (.wcF .last "c" "gp") .skip)) ;;
  .ite ("gp" =ₑ 0) (.wsc .firstGroup "gn") .skip ;;
  .lgrow .freeG 0 "g" 0

theorem unlinkGroupS_agree (κ : Caps) (σ : Core) (L : Loc) {g : Nat} (hg : L "g" = g)
    (hgG : g < σ.Gs.size) (hpG : (σ.Gs.getX g).prev < σ.Gs.size) (hnG : (σ.Gs.getX g).next < σ.Gs.size)
    (hcC : (σ.Gs.getX g).chk < σ.C.size) (hG : σ.Gs.size ≤ κ.tbl .G) (hC : σ.C.size ≤ κ.tbl .C)
    (hF : σ.freeG.length + 1 ≤ κ.lcap .freeG) (hF0 : 0 < κ.lrec .freeG) :
    ∃ L' n, evalF κ unlinkGroupS σ L = .ok (unlinkGroup σ g) L' n ∧ n ≤ 150 := by
  set G := σ.Gs.getX g
  set c := G.chk
  set C := σ.C.getX c
  have hgT : g < κ.tbl .G := by omega
  have hcT : c < κ.tbl .C := by omega
  have e1 := evalF_assign_ok (κ := κ) (s := σ) (L := L) (x := "gp") (e := .gF .prev "g") (v := G.prev)
    (by simp [Exp.gF, Exp.ev, hg, Fld.cap, Fld.get, GF.get, G, hgT])
  have e2 := evalF_assign_ok (κ := κ) (s := σ) (L := upd L "gp" G.prev) (x := "gn") (e := .gF .next "g") (v := G.next)
    (by simp [Exp.gF, Exp.ev, OM.Machine.State.upd, hg, Fld.cap, Fld.get, GF.get, G, hgT])
  have e3 := evalF_assign_ok (κ := κ) (s := σ) (L := upd (upd L "gp" G.prev) "gn" G.next) (x := "c")
    (e := .gF .chk "g") (v := c) (by simp [Exp.gF, Exp.ev, OM.Machine.State.upd, hg, Fld.cap, Fld.get, GF.get, c, G, hgT])
  set L3 := upd (upd (upd L "gp" G.prev) "gn" G.next) "c" c
  have rg : L3 "g" = g := by simp [L3, OM.Machine.State.upd, hg]
  have rgp : L3 "gp" = G.prev := by simp [L3, OM.Machine.State.upd]
  have rgn : L3 "gn" = G.next := by simp [L3, OM.Machine.State.upd]
  have rc : L3 "c" = c := by simp [L3, OM.Machine.State.upd]
  -- the neighbours
  set A1 := if G.prev != NIL then σ.Gs.modify G.prev (fun X => { X with next := G.next }) else σ.Gs
  obtain ⟨n4, b4, hn4⟩ := ite_skip_ok (κ := κ) (c := !ₑ ("gp" =ₑ 0)) (t := .wgF .next "gp" "gn")
    (s := σ) (s' := { σ with Gs := A1 }) (L := L3) (ct := 3) (G.prev != NIL)
    (by by_cases h : G.prev = 0 <;> simp [Exp.ev, OM.Machine.BinOp.eval, OM.Machine.UnOp.eval, rgp, h, NIL])
    (fun hb => by
      simp only [A1, hb, if_true, Stm.wgF]
      exact evalF_wrG_ok (by simp [Exp.ev, rgp]) (by simp [Exp.ev, rgn]) hpG (by omega) rfl)
    (fun hb => by simp [A1, hb])
  have hA1 : A1.size = σ.Gs.size := by simp only [A1]; split <;> simp
  set A2 := if G.next != NIL then A1.modify G.next (fun X => { X with prev := G.prev }) else A1
  obtain ⟨n5, b5, hn5⟩ := ite_skip_ok (κ := κ) (c := !ₑ ("gn" =ₑ 0)) (t := .wgF .prev "gn" "gp")
    (s := { σ with Gs := A1 }) (s' := { σ with Gs := A2 }) (L := L3) (ct := 3) (G.next != NIL)
    (by by_cases h : G.next = 0 <;> simp [Exp.ev, OM.Machine.BinOp.eval, OM.Machine.UnOp.eval, rgn, h, NIL])
    (fun hb => by
      simp only [A2, hb, if_true, Stm.wgF]
      exact evalF_wrG_ok (by simp [Exp.ev, rgn]) (by simp [Exp.ev, rgp]) (by simp [hA1]; exact hnG) (by omega) rfl)
    (fun hb => by simp [A2, hb])
  have hA2 : A2.size = σ.Gs.size := by simp only [A2]; split <;> simp [hA1]
  -- `g` itself
  set A3 := A2.modify g fun X => { X with alive := false, next := NIL, prev := NIL }
  have b6 : evalF κ ulG { σ with Gs := A2 } L3 = .ok { σ with Gs := A3 } L3 9 := by
    simp only [ulG, Stm.wgF]
    have hv : ∀ s' : Core, (Exp.var "g").ev κ s' L3 = some g := fun _ => by simp [Exp.ev, rg]
    rw [evalF_seq_ok2 (evalF_wrG_ok (hv _) rfl (by simp [hA2, hgG]) hgT rfl)
      (evalF_seq_ok2 (evalF_wrG_ok (hv _) rfl (by simp [hA2, hgG]) hgT rfl)
        (evalF_wrG_ok (hv _) rfl (by simp [hA2, hgG]) hgT rfl))]
    simp only [Array.modify_modify_same, Function.comp_def, Exp.cost]
    rfl
  -- the chunk
  have ecf := evalF_assign_ok (κ := κ) (s := { σ with Gs := A3 }) (L := L3) (x := "cf") (e := .cF .first "c")
    (v := C.first) (by simp [Exp.cF, Exp.ev, rc, hcT, Fld.cap, Fld.get, CF.get, C])
  have ecl := evalF_assign_ok (κ := κ) (s := { σ with Gs := A3 }) (L := upd L3 "cf" C.first) (x := "cl")
    (e := .cF .last "c") (v := C.last) (by simp [Exp.cF, Exp.ev, OM.Machine.State.upd, rc, hcT, Fld.cap, Fld.get, CF.get, C])
  set L5 := upd (upd L3 "cf" C.first) "cl" C.last
  have r5 : ∀ x, x ≠ "cf" → x ≠ "cl" → L5 x = L3 x := fun x h1 h2 => by simp [L5, OM.Machine.State.upd, h1, h2]
  set C' := if C.first == g && C.last == g then σ.C.modify c (fun X => { X with first := NIL, last := NIL })
      else if C.first == g then σ.C.modify c (fun X => { X with first := G.next })
      else if C.last == g then σ.C.modify c (fun X => { X with last := G.prev })
      else σ.C
  have hcv : ∀ s' : Core, (Exp.var "c").ev κ s' L5 = some c := fun _ => by
    simp [Exp.ev, r5 "c" (by decide) (by decide), rc]
  have b7 : ∃ n7, evalF κ (.ite ulCE (.wcF .first "c" 0 ;; .wcF .last "c" 0)
      (.ite ("cf" =ₑ "g") (.wcF .first "c" "gn") (.ite ("cl" =ₑ "g") (.wcF .last "c" "gp") .skip)))
      { σ with Gs := A3 } L5 = .ok { σ with Gs := A3, C := C' } L5 n7 ∧ n7 ≤ 30 := by
    have h5f : L5 "cf" = C.first := by simp [L5, OM.Machine.State.upd]
    have h5l : L5 "cl" = C.last := by simp [L5, OM.Machine.State.upd]
    have h5g : L5 "g" = g := by rw [r5 "g" (by decide) (by decide), rg]
    have h5p : L5 "gp" = G.prev := by rw [r5 "gp" (by decide) (by decide), rgp]
    have h5n : L5 "gn" = G.next := by rw [r5 "gn" (by decide) (by decide), rgn]
    simp only [Stm.wcF]
    have hcs : (({ σ with Gs := A3 } : Core)).C.size = σ.C.size := rfl
    by_cases hf : C.first = g <;> by_cases hl : C.last = g
    · have hC' : C' = (σ.C.modify c (CF.set · 0 .first)).modify c (CF.set · 0 .last) := by
        rw [Array.modify_modify_same]; simp [C', hf, hl]; rfl
      have w1 := evalF_wrC_ok (κ := κ) (s := { σ with Gs := A3 }) (L := L5) (k := .first) (e := (0 : Exp)) (w := 0)
        (hcv _) rfl hcC hcT rfl
      have w2 := evalF_wrC_ok (κ := κ) (s := { σ with Gs := A3, C := σ.C.modify c (CF.set · 0 .first) }) (L := L5)
        (k := .last) (e := (0 : Exp)) (w := 0) (hcv _) rfl (by simp [hcC]) hcT rfl
      rw [hC']
      exact ⟨_, evalF_ite_t (v := 1) (by simp [ulCE, Exp.ev, OM.Machine.BinOp.eval, h5f, h5l, h5g, hf, hl])
        one_ne_zero (evalF_seq_ok2 w1 w2), by simp [Exp.cost, ulCE]⟩
    · have hC' : C' = σ.C.modify c (CF.set · G.next .first) := by simp [C', hf, hl]; rfl
      have w1 := evalF_wrC_ok (κ := κ) (s := { σ with Gs := A3 }) (L := L5) (k := .first) (e := .var "gn")
        (w := G.next) (hcv _) (by simp [Exp.ev, h5n]) hcC hcT rfl
      rw [hC']
      exact ⟨_, evalF_ite_f (by simp [ulCE, Exp.ev, OM.Machine.BinOp.eval, h5f, h5l, h5g, hf, hl])
        (evalF_ite_t (v := 1) (by simp [Exp.ev, OM.Machine.BinOp.eval, h5f, h5g, hf]) one_ne_zero w1),
        by simp [Exp.cost, ulCE]⟩
    · have hC' : C' = σ.C.modify c (CF.set · G.prev .last) := by simp [C', hf, hl]; rfl
      have w1 := evalF_wrC_ok (κ := κ) (s := { σ with Gs := A3 }) (L := L5) (k := .last) (e := .var "gp")
        (w := G.prev) (hcv _) (by simp [Exp.ev, h5p]) hcC hcT rfl
      rw [hC']
      exact ⟨_, evalF_ite_f (by simp [ulCE, Exp.ev, OM.Machine.BinOp.eval, h5f, h5l, h5g, hf, hl])
        (evalF_ite_f (by simp [Exp.ev, OM.Machine.BinOp.eval, h5f, h5g, hf])
          (evalF_ite_t (v := 1) (by simp [Exp.ev, OM.Machine.BinOp.eval, h5l, h5g, hl]) one_ne_zero w1)),
        by simp [Exp.cost, ulCE]⟩
    · have hC' : C' = σ.C := by simp [C', hf, hl]
      rw [hC']
      exact ⟨_, evalF_ite_f (by simp [ulCE, Exp.ev, OM.Machine.BinOp.eval, h5f, h5l, h5g, hf, hl])
        (evalF_ite_f (by simp [Exp.ev, OM.Machine.BinOp.eval, h5f, h5g, hf])
          (evalF_ite_f (by simp [Exp.ev, OM.Machine.BinOp.eval, h5l, h5g, hl]) evalF_skip)),
        by simp [Exp.cost, ulCE]⟩
  obtain ⟨n7, b7, hn7⟩ := b7
  set fg := if G.prev != NIL then σ.firstGroup else G.next
  obtain ⟨n8, b8, hn8⟩ := ite_skip_ok (κ := κ) (c := "gp" =ₑ 0) (t := .wsc .firstGroup "gn")
    (s := { σ with Gs := A3, C := C' }) (s' := { σ with Gs := A3, C := C', firstGroup := fg }) (L := L5) (ct := 3)
    (G.prev == NIL)
    (by simp [Exp.ev, OM.Machine.BinOp.eval, r5 "gp" (by decide) (by decide), rgp, NIL])
    (fun hb => by
      have hb' : G.prev = 0 := by simpa [NIL] using hb
      simp only [fg, hb', NIL, bne_self_eq_false, Bool.false_eq_true, if_false, Stm.wsc]
      exact evalF_wrS_ok (κ := κ) (L := L5) (k := .firstGroup) (e := .var "gn") (w := G.next)
        (by simp [Exp.ev, r5 "gn" (by decide) (by decide), rgn]) rfl)
    (fun hb => by
      have hb' : (G.prev != NIL) = true := by simpa [NIL] using hb
      simp only [fg]; rw [if_pos hb'])
  set S8 : Core := { σ with Gs := A3, C := C', firstGroup := fg }
  have hso : LK.set κ S8 0 (LK.view S8 0 .freeG ++ [(g, 0)]) .freeG =
      some { S8 with freeG := g :: σ.freeG } := by
    rw [LK.set_ok (by simp [LK.recOk]) (by simp [LK.valid, LK.view]) (by simp [LK.view, S8]; omega) hF0]
    simp [LK.put, LK.view, S8, Function.comp_def]
  have b9 : evalF κ (.lgrow .freeG 0 "g" 0) S8 L5 = .ok { S8 with freeG := g :: σ.freeG } L5 22 := by
    simp only [evalF, Exp.ev, Exp.ofNat_def, r5 "g" (by decide) (by decide), rg, hso, Exp.cost]
  refine ⟨L5, _, evalF_seq_ok2 e1 (evalF_seq_ok2 e2 (evalF_seq_ok2 e3 (evalF_seq_ok2 b4 (evalF_seq_ok2 b5
    (evalF_seq_ok2 b6 (evalF_seq_ok2 ecf (evalF_seq_ok2 ecl (evalF_seq_ok2 b7 (evalF_seq_ok2 b8 b9))))))))), ?_⟩
  simp only [Exp.cost, Exp.gF, Exp.cF] at hn4 hn5 hn8 ⊢
  omega

end OM.Impl
