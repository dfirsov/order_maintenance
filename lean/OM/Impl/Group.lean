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

/-! ### Moving one element -/

theorem evalF_wrE_ok {κ : Caps} {s : Core} {L : Loc} {k : EF} {i e : Exp} {j w : Nat} (hi : i.ev κ s L = some j)
    (he : e.ev κ s L = some w) (hj : j < s.E.size) (hc : j < κ.tbl .E) (hk : k.ok w = true) :
    evalF κ (.wr (.e k) i e) s L = .ok { s with E := s.E.modify j (EF.set · w k) } L (1 + i.cost + e.cost) := by
  simp [evalF, hi, he, Fld.set, hj, hk]

def mvGS (first : Bool) : Stm :=
  if first then .ite ("f" =ₑ "l") (.wgF .first "g" 0 ;; .wgF .last "g" 0) (.wgF .first "g" "en")
  else .ite ("f" =ₑ "l") (.wgF .first "g" 0 ;; .wgF .last "g" 0) (.wgF .last "g" "en")
def mvDS (first : Bool) : Stm :=
  if first then .ite (.gF .first "d" =ₑ 0) (.wgF .first "d" "e") .skip ;; .wgF .last "d" "e"
  else .ite (.gF .first "d" =ₑ 0) (.wgF .last "d" "e") .skip ;; .wgF .first "d" "e"
def mvES : Stm := .weF .grp "e" "d" ;; .weF .lab "e" "lab"

/-- Move element `e` from group `g` to group `d` with label `lab`: the first of `g` to the end of `d`
(`first`), or the last of `g` to the front of `d` (locals `g d e lab`). -/
def moveS (first : Bool) : Stm :=
  "f" ::= .gF .first "g" ;; "l" ::= .gF .last "g" ;; "en" ::= .eF (if first then .next else .prev) "e" ;;
  mvGS first ;; mvDS first ;; mvES

theorem moveS_agree (κ : Caps) (σ : Core) (L : Loc) (first : Bool) {g d e lab : Nat} (hg : L "g" = g)
    (hd : L "d" = d) (he : L "e" = e) (hl : L "lab" = lab) (hgG : g < σ.Gs.size) (hdG : d < σ.Gs.size)
    (heE : e < σ.E.size) (hG : σ.Gs.size ≤ κ.tbl .G) (hE : σ.E.size ≤ κ.tbl .E) :
    ∃ L' n, evalF κ (moveS first) σ L =
      .ok (if first then moveFirstLeft σ g d e lab else moveLastRight σ g d e lab) L' n ∧ n ≤ 80 := by
  set G := σ.Gs.getX g
  set en := if first then (σ.E.getX e).next else (σ.E.getX e).prev
  have hgT : g < κ.tbl .G := by omega
  have hdT : d < κ.tbl .G := by omega
  have heT : e < κ.tbl .E := by omega
  have e1 := evalF_assign_ok (κ := κ) (s := σ) (L := L) (x := "f") (e := .gF .first "g") (v := G.first)
    (by simp [Exp.gF, Exp.ev, hg, Fld.cap, Fld.get, GF.get, G, hgT])
  have e2 := evalF_assign_ok (κ := κ) (s := σ) (L := upd L "f" G.first) (x := "l") (e := .gF .last "g") (v := G.last)
    (by simp [Exp.gF, Exp.ev, OM.Machine.State.upd, hg, Fld.cap, Fld.get, GF.get, G, hgT])
  have e3 := evalF_assign_ok (κ := κ) (s := σ) (L := upd (upd L "f" G.first) "l" G.last) (x := "en")
    (e := .eF (if first then .next else .prev) "e") (v := en)
    (by cases first <;> simp [Exp.eF, Exp.ev, OM.Machine.State.upd, he, Fld.cap, Fld.get, EF.get, en, heT])
  set L3 := upd (upd (upd L "f" G.first) "l" G.last) "en" en
  have r : ∀ x, x ≠ "f" → x ≠ "l" → x ≠ "en" → L3 x = L x := fun x h1 h2 h3 => by
    simp [L3, OM.Machine.State.upd, h1, h2, h3]
  have rg : L3 "g" = g := by rw [r "g" (by decide) (by decide) (by decide), hg]
  have rd : L3 "d" = d := by rw [r "d" (by decide) (by decide) (by decide), hd]
  have re : L3 "e" = e := by rw [r "e" (by decide) (by decide) (by decide), he]
  have rl : L3 "lab" = lab := by rw [r "lab" (by decide) (by decide) (by decide), hl]
  have rf : L3 "f" = G.first := by simp [L3, OM.Machine.State.upd]
  have rll : L3 "l" = G.last := by simp [L3, OM.Machine.State.upd]
  have ren : L3 "en" = en := by simp [L3, OM.Machine.State.upd]
  have hvg : ∀ s' : Core, (Exp.var "g").ev κ s' L3 = some g := fun _ => by simp [Exp.ev, rg]
  have hvd : ∀ s' : Core, (Exp.var "d").ev κ s' L3 = some d := fun _ => by simp [Exp.ev, rd]
  have hve : ∀ s' : Core, (Exp.var "e").ev κ s' L3 = some e := fun _ => by simp [Exp.ev, re]
  -- the source group
  set A1 := σ.Gs.modify g fun X => if G.first == G.last then { X with first := NIL, last := NIL }
    else if first then { X with first := en } else { X with last := en }
  have b4 : ∃ n4, evalF κ (mvGS first) σ L3 = .ok { σ with Gs := A1 } L3 n4 ∧ n4 ≤ 15 := by
    by_cases hfl : G.first = G.last
    · have w1 := evalF_wrG_ok (κ := κ) (s := σ) (L := L3) (k := .first) (e := (0 : Exp)) (w := 0) (hvg _) rfl hgG hgT rfl
      have w2 := evalF_wrG_ok (κ := κ) (s := { σ with Gs := σ.Gs.modify g (GF.set · 0 .first) }) (L := L3)
        (k := .last) (e := (0 : Exp)) (w := 0) (hvg _) rfl (by simp [hgG]) hgT rfl
      have hA : A1 = (σ.Gs.modify g (GF.set · 0 .first)).modify g (GF.set · 0 .last) := by
        rw [Array.modify_modify_same]; simp only [A1, hfl, beq_self_eq_true, if_true]; rfl
      rw [hA]
      have ec : ("f" =ₑ "l" : Exp).ev κ σ L3 = some 1 := by simp [Exp.ev, OM.Machine.BinOp.eval, rf, rll, hfl]
      cases first <;> exact ⟨_, evalF_ite_t ec one_ne_zero (evalF_seq_ok2 w1 w2), by simp [Exp.cost]⟩
    · have ec : ("f" =ₑ "l" : Exp).ev κ σ L3 = some 0 := by simp [Exp.ev, OM.Machine.BinOp.eval, rf, rll, hfl]
      cases first
      · have w1 := evalF_wrG_ok (κ := κ) (s := σ) (L := L3) (k := .last) (e := .var "en") (w := en) (hvg _)
          (by simp [Exp.ev, ren]) hgG hgT rfl
        have hA : A1 = σ.Gs.modify g (GF.set · en .last) := by
          simp only [A1, show (G.first == G.last) = false by simpa using hfl]; rfl
        rw [hA]; exact ⟨_, evalF_ite_f ec w1, by simp [Exp.cost]⟩
      · have w1 := evalF_wrG_ok (κ := κ) (s := σ) (L := L3) (k := .first) (e := .var "en") (w := en) (hvg _)
          (by simp [Exp.ev, ren]) hgG hgT rfl
        have hA : A1 = σ.Gs.modify g (GF.set · en .first) := by
          simp only [A1, show (G.first == G.last) = false by simpa using hfl]; rfl
        rw [hA]; exact ⟨_, evalF_ite_f ec w1, by simp [Exp.cost]⟩
  obtain ⟨n4, b4, hn4⟩ := b4
  -- the destination group
  have hA1s : A1.size = σ.Gs.size := by simp [A1]
  set D1 := A1.getX d
  set A2 := A1.modify d fun X => if first then { X with first := if X.first == NIL then e else X.first, last := e }
    else { X with last := if X.first == NIL then e else X.last, first := e }
  have b5 : ∃ n5, evalF κ (mvDS first) { σ with Gs := A1 } L3 = .ok { σ with Gs := A2 } L3 n5 ∧ n5 ≤ 15 := by
    have ec : (.gF .first "d" =ₑ 0 : Exp).ev κ { σ with Gs := A1 } L3 = some (if D1.first = 0 then 1 else 0) := by
      simp [Exp.gF, Exp.ev, OM.Machine.BinOp.eval, rd, hdT, Fld.cap, Fld.get, GF.get, D1]
    by_cases h0 : D1.first = 0
    · have h0' : (A1.getX d).first = 0 := h0
      rw [if_pos h0] at ec
      cases first
      · have w1 := evalF_wrG_ok (κ := κ) (s := { σ with Gs := A1 }) (L := L3) (k := .last) (e := .var "e") (w := e)
          (hvd _) (hve _) (by simp [hA1s, hdG]) hdT rfl
        have w2 := evalF_wrG_ok (κ := κ) (s := { σ with Gs := A1.modify d (GF.set · e .last) }) (L := L3) (k := .first)
          (e := .var "e") (w := e) (hvd _) (hve _) (by simp [hA1s, hdG]) hdT rfl
        have hA : A2 = (A1.modify d (GF.set · e .last)).modify d (GF.set · e .first) := by
          rw [Array.modify_modify_same]; apply Array.modify_congr_getX
          simp [GF.set, h0', NIL]
        rw [hA]
        exact ⟨_, evalF_seq_ok2 (evalF_ite_t ec one_ne_zero w1) w2, by simp [Exp.cost, Exp.gF]⟩
      · have w1 := evalF_wrG_ok (κ := κ) (s := { σ with Gs := A1 }) (L := L3) (k := .first) (e := .var "e") (w := e)
          (hvd _) (hve _) (by simp [hA1s, hdG]) hdT rfl
        have w2 := evalF_wrG_ok (κ := κ) (s := { σ with Gs := A1.modify d (GF.set · e .first) }) (L := L3) (k := .last)
          (e := .var "e") (w := e) (hvd _) (hve _) (by simp [hA1s, hdG]) hdT rfl
        have hA : A2 = (A1.modify d (GF.set · e .first)).modify d (GF.set · e .last) := by
          rw [Array.modify_modify_same]; apply Array.modify_congr_getX
          simp [GF.set, h0', NIL]
        rw [hA]
        exact ⟨_, evalF_seq_ok2 (evalF_ite_t ec one_ne_zero w1) w2, by simp [Exp.cost, Exp.gF]⟩
    · have h0' : ¬(A1.getX d).first = 0 := h0
      rw [if_neg h0] at ec
      cases first
      · have w2 := evalF_wrG_ok (κ := κ) (s := { σ with Gs := A1 }) (L := L3) (k := .first)
          (e := .var "e") (w := e) (hvd _) (hve _) (by simp [hA1s, hdG]) hdT rfl
        have hA : A2 = A1.modify d (GF.set · e .first) := by
          apply Array.modify_congr_getX
          simp [GF.set, h0', NIL]
        rw [hA]
        exact ⟨_, evalF_seq_ok2 (evalF_ite_f ec evalF_skip) w2, by simp [Exp.cost, Exp.gF]⟩
      · have w2 := evalF_wrG_ok (κ := κ) (s := { σ with Gs := A1 }) (L := L3) (k := .last)
          (e := .var "e") (w := e) (hvd _) (hve _) (by simp [hA1s, hdG]) hdT rfl
        have hA : A2 = A1.modify d (GF.set · e .last) := by
          apply Array.modify_congr_getX
          simp [GF.set, h0', NIL]
        rw [hA]
        exact ⟨_, evalF_seq_ok2 (evalF_ite_f ec evalF_skip) w2, by simp [Exp.cost, Exp.gF]⟩
  obtain ⟨n5, b5, hn5⟩ := b5
  -- the element
  have w6 := evalF_wrE_ok (κ := κ) (s := { σ with Gs := A2 }) (L := L3) (k := .grp) (e := .var "d") (w := d)
    (hve _) (hvd _) heE heT rfl
  have w7 := evalF_wrE_ok (κ := κ) (s := { σ with Gs := A2, E := σ.E.modify e (EF.set · d .grp) }) (L := L3)
    (k := .lab) (e := .var "lab") (w := lab) (hve _) (by simp [Exp.ev, rl]) (by simp [heE]) heT rfl
  have hfin : { σ with Gs := A2, E := (σ.E.modify e (EF.set · d .grp)).modify e (EF.set · lab .lab) } =
      (if first then moveFirstLeft σ g d e lab else moveLastRight σ g d e lab) := by
    rw [Array.modify_modify_same]
    cases first <;> rfl
  refine ⟨L3, _, evalF_seq_ok2 e1 (evalF_seq_ok2 e2 (evalF_seq_ok2 e3 (evalF_seq_ok2 b4 (evalF_seq_ok2 b5
    (by simp only [mvES, Stm.weF]; rw [← hfin]; exact evalF_seq_ok2 w6 w7))))), ?_⟩
  simp only [Exp.cost, Exp.gF, Exp.eF] at hn4 hn5 ⊢
  omega

/-! ### Label primitives -/

theorem guard_run_ne {α : Type} {msg : String} {s s' : Core} {v : α} : (OM.Model.guard msg : CM α).run s ≠ .ok v s' := by
  simp [OM.Model.guard]

/-- `lab := between a b` (locals `a b`). -/
def betweenS : Stm := .ite ("b" ≤ₑ "a" + 1) .fail ("lab" ::= ("a" + "b") / 2)
/-- `lab := after a D B` (locals `a D B`). -/
def afterS : Stm :=
  "v" ::= "a" + "D" ;; .ite ((.bin .shl 1 "B" ≤ₑ "v") ||ₑ ("v" ≤ₑ "a")) .fail ("lab" ::= "v")
/-- `lab := before b D` (locals `b D`). -/
def beforeS : Stm := .ite (("b" <ₑ "D") ||ₑ ("D" =ₑ 0)) .fail ("lab" ::= "b" - "D")

theorem between_inv {a b : Nat} {why : String} {s s' : Core} {v : Nat} (h : (between a b why).run s = .ok v s') :
    s' = s ∧ a + 1 < b ∧ v = (a + b) / 2 := by
  unfold between at h
  by_cases hc : a + 1 ≥ b
  · simp [hc, OM.Model.guard] at h
  · simp [hc] at h; exact ⟨h.2.symm, by omega, h.1.symm⟩

theorem after_inv {a D B : Nat} {why : String} {s s' : Core} {v : Nat} (h : (after a D B why).run s = .ok v s') :
    s' = s ∧ a + D < 1 <<< B ∧ a < a + D ∧ v = a + D := by
  unfold after at h
  by_cases hc : 1 <<< B ≤ a + D ∨ D = 0
  · simp [hc, OM.Model.guard] at h
  · simp [hc] at h; exact ⟨h.2.symm, by omega, by omega, h.1.symm⟩

theorem before_inv {b D : Nat} {why : String} {s s' : Core} {v : Nat} (h : (before b D why).run s = .ok v s') :
    s' = s ∧ D ≤ b ∧ D ≠ 0 ∧ v = b - D := by
  unfold before at h
  by_cases hc : b < D ∨ D = 0
  · simp [hc, OM.Model.guard] at h
  · simp [hc] at h; exact ⟨h.2.symm, by omega, by omega, h.1.symm⟩

theorem betweenS_ok {κ : Caps} {s : Core} {L : Loc} {a b : Nat} (ha : L "a" = a) (hb : L "b" = b) (h : a + 1 < b) :
    ∃ c, evalF κ betweenS s L = .ok s (upd L "lab" ((a + b) / 2)) c ∧ c ≤ 15 := by
  have : ¬ b ≤ a + 1 := by omega
  refine ⟨12, ?_, by omega⟩
  simp [betweenS, evalF, Exp.ev, OM.Machine.BinOp.eval, ha, hb, this, Exp.cost, Res.addCost]

theorem afterS_ok {κ : Caps} {s : Core} {L : Loc} {a D B : Nat} (ha : L "a" = a) (hD : L "D" = D) (hB : L "B" = B)
    (h1 : a + D < 1 <<< B) (h2 : a < a + D) :
    ∃ c, evalF κ afterS s L = .ok s (upd (upd L "v" (a + D)) "lab" (a + D)) c ∧ c ≤ 20 := by
  have h1' : ¬ 1 * 2 ^ B ≤ a + D := by rw [Nat.shiftLeft_eq] at h1; omega
  have h2' : D ≠ 0 := by omega
  have h3 : a + D < 2 ^ B := by omega
  refine ⟨16, ?_, by omega⟩
  simp [afterS, evalF, Exp.ev, OM.Machine.BinOp.eval, ha, hD, hB, h1', h2', Exp.cost, Res.addCost, Res.bind]
  rw [if_pos h3]; simp [OM.Machine.State.upd]

theorem beforeS_ok {κ : Caps} {s : Core} {L : Loc} {b D : Nat} (hb : L "b" = b) (hD : L "D" = D)
    (h1 : D ≤ b) (h2 : D ≠ 0) : evalF κ beforeS s L = .ok s (upd L "lab" (b - D)) 12 := by
  have : ¬ b < D := by omega
  simp [beforeS, evalF, Exp.ev, OM.Machine.BinOp.eval, hb, hD, this, h1, h2, Exp.cost, Res.addCost]

end OM.Impl
