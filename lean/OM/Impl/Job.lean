import OM.Impl.Reserve
import OM.Impl.Finish
import OM.Proof.Top.Step

/-!
# M6: the top structure's job at Level M (`jobStep`)

The running job lives in the optional record `resJob`; the program reads its fields into locals
(`jx jy jz` and the program counter `jt ja jb jc jd`, `pcEnc`) and writes the new counter with
`pcSet` (or clears the job). Each case is matched against the Level F run lemma the cost proof
uses.
-/

namespace OM.Impl

open OM.Model
open OM.Proof.Top
open OM.Machine (Reg BinOp UnOp)

local notation "upd" => OM.Machine.State.upd

/-! ### A copy step -/

def jcopyS : Stm :=
  "v" ::= .prd "jx" "ja" ;;
  .pwr "jy" "ja" "v" ;; .pwr "jz" "ja" "v" ;;
  .ite (.rd (.n .first) "v" =ₑ "jx") (.wr (.n .first) "v" "jy") .skip ;;
  .ite (.rd (.n .last) "v" =ₑ "jx") (.wr (.n .last) "v" "jz") .skip ;;
  .ite ("ja" <ₑ .prm .H) (.pcSet 0 ("ja" + 1) 0 0 0) (.pcSet 1 0 0 0 0)

theorem getX_default_of_le {α : Type} [Inhabited α] {a : Array α} {i : Nat} (h : a.size ≤ i) : a.getX i = default := by
  simp [Array.getX, Array.getD, show ¬i < a.size by omega]

theorem jcopyS_ok {κ : Caps} {s : Core} {L : Loc} {j : Job} {l : Nat} (hjob : s.resJob = some j)
    (hx : L "jx" = j.x) (hy : L "jy" = j.y) (hz : L "jz" = j.z) (hl : L "ja" = l)
    (hx0 : j.x ≠ NIL) (hyz : j.y ≠ j.z)
    (hnx : notPrep s j.x) (hny : notPrep s j.y) (hnz : notPrep s j.z)
    (hxC : j.x < κ.tbl .C) (hyC : j.y < κ.tbl .C) (hzC : j.z < κ.tbl .C) (hlw : l < κ.pw)
    (hvN : (s.path.getX j.x).getX l < κ.tbl .N) :
    ∃ L' c, evalF κ jcopyS s L = .ok { copyC s j l with resJob := some (copyNext s.P j l) } L' c ∧ c ≤ 100 ∧
      ∀ r, r ≠ "v" → L' r = L r := by
  set v := (s.path.getX j.x).getX l
  have a1 := evalF_assign_ok (κ := κ) (s := s) (L := L) (x := "v") (e := .prd "jx" "ja") (v := v)
    (by simp [Exp.ev, hx, hl, hxC, hlw, rowOf_notPrep hnx, v])
  set L1 := upd L "v" v
  have h1 : ∀ r, r ≠ "v" → L1 r = L r := fun r h => by simp [L1, OM.Machine.State.upd, h]
  have h1x : L1 "jx" = j.x := by rw [h1 _ (by decide), hx]
  have h1y : L1 "jy" = j.y := by rw [h1 _ (by decide), hy]
  have h1z : L1 "jz" = j.z := by rw [h1 _ (by decide), hz]
  have h1l : L1 "ja" = l := by rw [h1 _ (by decide), hl]
  have h1v : L1 "v" = v := by simp [L1, OM.Machine.State.upd]
  set s1 : Core := { s with path := s.path.setX j.y ((s.path.getX j.y).setX l v) }
  have e2 : evalF κ (.pwr "jy" "ja" "v") s L1 = .ok s1 L1 7 := by
    simp [evalF, Exp.ev, h1y, h1l, h1v, hyC, hlw, hny, Exp.cost, s1]
  set s2 : Core := { s1 with path := s1.path.setX j.z ((s1.path.getX j.z).setX l v) }
  have e3 : evalF κ (.pwr "jz" "ja" "v") s1 L1 = .ok s2 L1 7 := by
    have : notPrep s1 j.z := hnz
    simp [evalF, Exp.ev, h1z, h1l, h1v, hzC, hlw, this, Exp.cost, s2]
  set V := s.nodes.getX v
  have hs2v : s2.nodes.getX v = V := rfl
  -- `first`
  set s3 : Core := if V.first == j.x then { s2 with nodes := s2.nodes.modify v fun n => { n with first := j.y } } else s2
  have e4 : ∃ c4, evalF κ (.ite (.rd (.n .first) "v" =ₑ "jx") (.wr (.n .first) "v" "jy") .skip) s2 L1 =
      .ok s3 L1 c4 ∧ c4 ≤ 12 := by
    by_cases hf : V.first = j.x
    · have hvs : v < s.nodes.size := by
        by_contra hc
        have : V = default := getX_default_of_le (by omega)
        rw [this] at hf; exact hx0 (by rw [← hf]; rfl)
      have w := evalF_wrN_ok (κ := κ) (s := s2) (L := L1) (k := .first) (i := .var "v") (e := .var "jy") (j := v)
        (w := j.y) (by simp [Exp.ev, h1v]) (by simp [Exp.ev, h1y]) hvs hvN rfl
      have hs3 : s3 = { s2 with nodes := s2.nodes.modify v (NF.set · j.y .first) } := by
        simp only [s3, hf, beq_self_eq_true, if_true]; rfl
      rw [← hs3] at w
      exact ⟨_, evalF_ite_t (v := 1) (by simp [Exp.ev, OM.Machine.BinOp.eval, h1v, h1x, hvN, Fld.cap, Fld.get,
        NF.get, hs2v, hf]) one_ne_zero w, by simp [Exp.cost]⟩
    · have hs3 : s3 = s2 := by simp only [s3]; rw [if_neg (by simpa using hf)]
      rw [hs3]
      exact ⟨_, evalF_ite_f (by simp [Exp.ev, OM.Machine.BinOp.eval, h1v, h1x, hvN, Fld.cap, Fld.get,
        NF.get, hs2v, hf]) evalF_skip, by simp [Exp.cost]⟩
  obtain ⟨c4, e4, hc4⟩ := e4
  have hs3v : (s3.nodes.getX v).last = V.last := by
    simp only [s3]; split
    · simp only [getX_modify']; split <;> rfl
    · rfl
  have hs3n : s3.nodes.size = s.nodes.size := by simp only [s3]; split <;> simp [s2, s1]
  -- `last`
  set s4 : Core := if V.last == j.x then { s3 with nodes := s3.nodes.modify v fun n => { n with last := j.z } } else s3
  have e5 : ∃ c5, evalF κ (.ite (.rd (.n .last) "v" =ₑ "jx") (.wr (.n .last) "v" "jz") .skip) s3 L1 =
      .ok s4 L1 c5 ∧ c5 ≤ 12 := by
    by_cases hf : V.last = j.x
    · have hvs : v < s.nodes.size := by
        by_contra hc
        have : V = default := getX_default_of_le (by omega)
        rw [this] at hf; exact hx0 (by rw [← hf]; rfl)
      have w := evalF_wrN_ok (κ := κ) (s := s3) (L := L1) (k := .last) (i := .var "v") (e := .var "jz") (j := v)
        (w := j.z) (by simp [Exp.ev, h1v]) (by simp [Exp.ev, h1z]) (by rw [hs3n]; exact hvs) hvN rfl
      have hs4 : s4 = { s3 with nodes := s3.nodes.modify v (NF.set · j.z .last) } := by
        simp only [s4, hf, beq_self_eq_true, if_true]; rfl
      rw [← hs4] at w
      exact ⟨_, evalF_ite_t (v := 1) (by simp [Exp.ev, OM.Machine.BinOp.eval, h1v, h1x, hvN, Fld.cap, Fld.get,
        NF.get, hs3v, hf]) one_ne_zero w, by simp [Exp.cost]⟩
    · have hs4 : s4 = s3 := by simp only [s4]; rw [if_neg (by simpa using hf)]
      rw [hs4]
      exact ⟨_, evalF_ite_f (by simp [Exp.ev, OM.Machine.BinOp.eval, h1v, h1x, hvN, Fld.cap, Fld.get,
        NF.get, hs3v, hf]) evalF_skip, by simp [Exp.cost]⟩
  obtain ⟨c5, e5, hc5⟩ := e5
  have hs4c : s4 = copyC s j l := rfl
  have hj4 : (copyC s j l).resJob = some j := by
    rw [← hs4c]; simp only [s4, s3]; split <;> split <;> exact hjob
  have hP : (copyC s j l).P = s.P := by rw [← hs4c]; simp only [s4, s3]; split <;> split <;> rfl
  rw [hs4c] at e5
  -- the program counter
  have e6 : ∃ c6, evalF κ (.ite ("ja" <ₑ .prm .H) (.pcSet 0 ("ja" + 1) 0 0 0) (.pcSet 1 0 0 0 0)) (copyC s j l) L1 =
      .ok { copyC s j l with resJob := some (copyNext s.P j l) } L1 c6 ∧ c6 ≤ 40 := by
    by_cases hH : l < s.P.H
    · have hn : copyNext s.P j l = { j with pc := .copy (l + 1) } := by simp [copyNext, hH]
      rw [hn]
      refine ⟨_, evalF_ite_t (v := 1) (by simp [Exp.ev, OM.Machine.BinOp.eval, h1l, PF.get, hP, hH]) one_ne_zero
        (by simp [evalF, evList, Exp.ev, hj4, h1l, OM.Machine.BinOp.eval, pcDec]; rfl), ?_⟩
      simp [costList, Exp.cost]
    · have hn : copyNext s.P j l = { j with pc := .walk none } := by simp [copyNext, hH]
      rw [hn]
      refine ⟨_, evalF_ite_f (by simp [Exp.ev, OM.Machine.BinOp.eval, h1l, PF.get, hP, hH])
        (by simp [evalF, evList, Exp.ev, hj4, pcDec]; rfl), ?_⟩
      simp [costList, Exp.cost]
  obtain ⟨c6, e6, hc6⟩ := e6
  refine ⟨L1, _, evalF_seq_ok2 a1 (evalF_seq_ok2 e2 (evalF_seq_ok2 e3 (evalF_seq_ok2 e4 (evalF_seq_ok2 e5 e6)))),
    ?_, h1⟩
  simp only [Exp.cost] at hc4 hc5 ⊢; omega

/-! ### A sweep step that moves a chunk (`drainStep`, `drainStep_move`) -/

theorem lor_shift (a c b h : Nat) (hc : c < 2 ^ b) (hh : 1 ≤ h) :
    (a <<< (h * b)) ||| (c <<< ((h - 1) * b)) = a * 2 ^ (h * b) + c * 2 ^ ((h - 1) * b) := by
  have e : h * b = b + (h - 1) * b := by
    obtain ⟨k, rfl⟩ : ∃ k, h = k + 1 := ⟨h - 1, by omega⟩
    simp; ring
  rw [e, Nat.shiftLeft_add, ← Nat.shiftLeft_or_distrib, ← Nat.shiftLeft_add_eq_or_of_lt hc]
  simp only [Nat.shiftLeft_eq, pow_add]; ring

/-- `r := belowOf h c` (local `h`). -/
def belowS (c r : Reg) : Stm := .ite ("h" =ₑ 1) (r ::= .var c) (r ::= .prd c ("h" - 1))

theorem belowS_ok {κ : Caps} {s : Core} {L : Loc} {c r : Reg} {h y : Nat} (hh : L "h" = h) (hc : L c = y)
    (h1 : 1 ≤ h) (hnp : notPrep s y) (hyC : y < κ.tbl .C) (hw : h - 1 < κ.pw) :
    evalF κ (belowS c r) s L = .ok s (upd L r (if h == 1 then y else (s.path.getX y).getX (h - 1)))
      (if h = 1 then 6 else 13) := by
  by_cases e : h = 1
  · simp [belowS, evalF, Exp.ev, hh, hc, OM.Machine.BinOp.eval, e, Exp.cost, Res.addCost]
  · simp [belowS, evalF, Exp.ev, hh, hc, OM.Machine.BinOp.eval, e, Exp.cost, Res.addCost, hyC, hw,
      rowOf_notPrep hnp, h1]

def dsLeftS : Stm := "t" ::= .rd (.n .t1) "v" ;; "lf" ::= 1 ;; "y" ::= .var "y0" ;; "bl" ::= .var "b0"
def dsRightS : Stm :=
  "y" ::= .rd (.n .last) "v" ;; belowS "y" "bl" ;;
  (lookupP .side).call [.var "v", .var "bl"] ["f", "sd"] ;; .ite "f" .skip .fail ;;
  .ite ("sd" =ₑ 1) .skip .fail ;; "t" ::= .rd (.n .t2) "v" ;; "lf" ::= 0
/-- The chunk moved (`y`), its target (`t`), the direction (`lf`) and the entry below (`bl`). -/
def dsPickS : Stm :=
  "y0" ::= .rd (.n .first) "v" ;; belowS "y0" "b0" ;;
  (lookupP .side).call [.var "v", .var "b0"] ["f", "sd"] ;; .ite "f" .skip .fail ;;
  .ite ("sd" =ₑ 0) dsLeftS dsRightS

theorem dsPickS_ok {κ : Caps} {s : Core} {L : Loc} {v : Nat} (hv : L "v" = v) (hh : L "h" = (s.nodes.getX v).height)
    (h1 : 1 ≤ (s.nodes.getX v).height)
    (hside : goesLeft s v ∨
      lookup (s.nodes.getX v).side (belowY s v (s.nodes.getX v).first) = some .right ∧
      lookup (s.nodes.getX v).side (belowY s v (s.nodes.getX v).last) = some .right)
    (hvN : v < κ.tbl .N) (hvs : v < κ.lrec .side)
    (hnf : notPrep s (s.nodes.getX v).first) (hnl : notPrep s (s.nodes.getX v).last)
    (hfC : (s.nodes.getX v).first < κ.tbl .C) (hlC : (s.nodes.getX v).last < κ.tbl .C)
    (hw : (s.nodes.getX v).height - 1 < κ.pw) :
    ∃ L' c, evalF κ dsPickS s L = .ok s L' c ∧ L' "y" = dsY s v ∧ L' "t" = dsT s v ∧
      L' "lf" = b2n (decide (goesLeft s v)) ∧ L' "bl" = belowY s v (dsY s v) ∧
      c ≤ 300 + 80 * (s.nodes.getX v).side.length ∧
      ∀ r, r ≠ "y0" → r ≠ "b0" → r ≠ "f" → r ≠ "sd" → r ≠ "t" → r ≠ "lf" → r ≠ "y" → r ≠ "bl" → L' r = L r := by
  set V := s.nodes.getX v
  set h := V.height
  have hvs' : LK.view s v .side = encS V.side := rfl
  have a1 := evalF_assign_ok (κ := κ) (s := s) (L := L) (x := "y0") (e := .rd (.n .first) "v") (v := V.first)
    (by simp [Exp.ev, hv, hvN, Fld.cap, Fld.get, NF.get, V])
  set L1 := upd L "y0" V.first
  have e2 := belowS_ok (κ := κ) (s := s) (L := L1) (c := "y0") (r := "b0") (h := h)
    (by simp [L1, OM.Machine.State.upd, hh]) (by simp [L1, OM.Machine.State.upd]) h1 hnf hfC hw
  set b0 := if h == 1 then V.first else (s.path.getX V.first).getX (h - 1)
  have hb0 : b0 = belowY s v V.first := rfl
  set L2 := upd L1 "b0" b0
  obtain ⟨Lf, cf, ef, hf, hsd, -, -, hcf⟩ := lookupP_agree κ .side s
    (OM.Machine.State.setLocs (fun _ => 0) ["i", "x"] [v, b0]) (i := v) (x := b0)
    (by simp [OM.Machine.State.setLocs, OM.Machine.State.upd])
    (by simp [OM.Machine.State.setLocs, OM.Machine.State.upd]) hvs
  rw [hvs', lookup_encS, hb0] at hf hsd
  rw [hvs'] at hcf
  have e3 := evalF_call_ok (q := lookupP .side) (args := [.var "v", .var "b0"]) (ds := ["f", "sd"]) (L := L2)
    (by simp [evList, Exp.ev, L2, L1, OM.Machine.State.upd, hv]) ef
  set L3 := OM.Machine.State.setLocs L2 ["f", "sd"] ((lookupP .side).rets.map Lf)
  have hL3 : ∀ r, r ≠ "f" → r ≠ "sd" → L3 r = L2 r := fun r h1 h2 => by
    simp [L3, lookupP, OM.Machine.State.setLocs, OM.Machine.State.upd, h1, h2]
  have h3f : L3 "f" = Lf "f" := by simp [L3, lookupP, OM.Machine.State.setLocs, OM.Machine.State.upd]
  have h3sd : L3 "sd" = Lf "v" := by simp [L3, lookupP, OM.Machine.State.setLocs, OM.Machine.State.upd]
  have h3v : L3 "v" = v := by rw [hL3 _ (by decide) (by decide)]; simp [L2, L1, OM.Machine.State.upd, hv]
  have h3h : L3 "h" = h := by rw [hL3 _ (by decide) (by decide)]; simp [L2, L1, OM.Machine.State.upd, hh]
  have hlen : (encS V.side).length = V.side.length := by simp [encS]
  rw [hlen] at hcf
  by_cases hl : goesLeft s v
  · have hl' : lookup V.side (belowY s v V.first) = some .left := hl
    rw [hl'] at hf hsd
    simp only [Option.map_some, Option.isSome_some, if_true, Option.getD_some, sideN] at hf hsd
    have e4 : evalF κ (.ite "f" .skip .fail) s L3 = .ok s L3 3 := by
      simp [evalF, Exp.ev, h3f, hf, Exp.cost, Res.addCost]
    have hy : dsY s v = V.first := by simp [dsY, hl, V]
    have ht : dsT s v = V.t1 := by simp [dsT, hl, V]
    have a5 := evalF_assign_ok (κ := κ) (s := s) (L := L3) (x := "t") (e := .rd (.n .t1) "v") (v := V.t1)
      (by simp [Exp.ev, h3v, hvN, Fld.cap, Fld.get, NF.get, V])
    set L5 := upd (upd (upd (upd L3 "t" V.t1) "lf" 1) "y" V.first) "bl" b0
    have e5 : evalF κ dsLeftS s L3 = .ok s L5 9 := by
      have a6 := evalF_assign_ok (κ := κ) (s := s) (L := upd L3 "t" V.t1) (x := "lf") (e := (1 : Exp)) (v := 1) rfl
      have a7 := evalF_assign_ok (κ := κ) (s := s) (L := upd (upd L3 "t" V.t1) "lf" 1) (x := "y") (e := .var "y0")
        (v := V.first) (by simp [Exp.ev, OM.Machine.State.upd, hL3, L2, L1])
      have a8 := evalF_assign_ok (κ := κ) (s := s) (L := upd (upd (upd L3 "t" V.t1) "lf" 1) "y" V.first) (x := "bl")
        (e := .var "b0") (v := b0) (by simp [Exp.ev, OM.Machine.State.upd, hL3, L2])
      exact evalF_seq_ok2 a5 (evalF_seq_ok2 a6 (evalF_seq_ok2 a7 a8))
    have hc6 : ("sd" =ₑ 0 : Exp).ev κ s L3 = some 1 := by simp [Exp.ev, OM.Machine.BinOp.eval, h3sd, hsd]
    refine ⟨L5, _, evalF_seq_ok2 a1 (evalF_seq_ok2 e2 (evalF_seq_ok2 e3 (evalF_seq_ok2 e4
      (evalF_ite_t hc6 one_ne_zero e5)))), by simp [L5, OM.Machine.State.upd, hy],
      by simp [L5, OM.Machine.State.upd, ht], by simp [L5, OM.Machine.State.upd, hl, b2n],
      by simp [L5, OM.Machine.State.upd, hy, hb0], ?_, ?_⟩
    · simp only [Exp.cost, costList, List.map, List.sum_cons, List.sum_nil, List.length_cons, List.length_nil] at hcf ⊢
      split <;> omega
    · intro r h1 h2 h3 h4 h5 h6 h7 h8
      simp only [L5, OM.Machine.State.upd, if_neg h5, if_neg h6, if_neg h7, if_neg h8]
      rw [hL3 r h3 h4]; simp [L2, L1, OM.Machine.State.upd, h1, h2]
  · obtain ⟨hr1, hr2⟩ : lookup V.side (belowY s v V.first) = some .right ∧
        lookup V.side (belowY s v V.last) = some .right := hside.resolve_left hl
    rw [hr1] at hf hsd
    simp only [Option.map_some, Option.isSome_some, if_true, Option.getD_some, sideN] at hf hsd
    have e4 : evalF κ (.ite "f" .skip .fail) s L3 = .ok s L3 3 := by
      simp [evalF, Exp.ev, h3f, hf, Exp.cost, Res.addCost]
    have hy : dsY s v = V.last := by simp [dsY, hl, V]
    have ht : dsT s v = V.t2 := by simp [dsT, hl, V]
    have hc6 : ("sd" =ₑ 0 : Exp).ev κ s L3 = some 0 := by simp [Exp.ev, OM.Machine.BinOp.eval, h3sd, hsd]
    -- the right branch
    have a5 := evalF_assign_ok (κ := κ) (s := s) (L := L3) (x := "y") (e := .rd (.n .last) "v") (v := V.last)
      (by simp [Exp.ev, h3v, hvN, Fld.cap, Fld.get, NF.get, V])
    set L5 := upd L3 "y" V.last
    have e6 := belowS_ok (κ := κ) (s := s) (L := L5) (c := "y") (r := "bl") (h := h)
      (by simp [L5, OM.Machine.State.upd, h3h]) (by simp [L5, OM.Machine.State.upd]) h1 hnl hlC hw
    set b1 := if h == 1 then V.last else (s.path.getX V.last).getX (h - 1)
    have hb1 : b1 = belowY s v V.last := rfl
    set L6 := upd L5 "bl" b1
    obtain ⟨Lg, cg, eg, hg, hgd, -, -, hcg⟩ := lookupP_agree κ .side s
      (OM.Machine.State.setLocs (fun _ => 0) ["i", "x"] [v, b1]) (i := v) (x := b1)
      (by simp [OM.Machine.State.setLocs, OM.Machine.State.upd])
      (by simp [OM.Machine.State.setLocs, OM.Machine.State.upd]) hvs
    rw [hvs', lookup_encS, hb1, hr2] at hg hgd
    rw [hvs', hlen] at hcg
    simp only [Option.map_some, Option.isSome_some, if_true, Option.getD_some, sideN] at hg hgd
    have e7 := evalF_call_ok (q := lookupP .side) (args := [.var "v", .var "bl"]) (ds := ["f", "sd"]) (L := L6)
      (by simp [evList, Exp.ev, L6, L5, OM.Machine.State.upd, h3v]) eg
    set L7 := OM.Machine.State.setLocs L6 ["f", "sd"] ((lookupP .side).rets.map Lg)
    have hL7 : ∀ r, r ≠ "f" → r ≠ "sd" → L7 r = L6 r := fun r h1 h2 => by
      simp [L7, lookupP, OM.Machine.State.setLocs, OM.Machine.State.upd, h1, h2]
    have h7f : L7 "f" = 1 := by simp [L7, lookupP, OM.Machine.State.setLocs, OM.Machine.State.upd, hg]
    have h7sd : L7 "sd" = 1 := by simp [L7, lookupP, OM.Machine.State.setLocs, OM.Machine.State.upd, hgd]
    have h7v : L7 "v" = v := by rw [hL7 _ (by decide) (by decide)]; simp [L6, L5, OM.Machine.State.upd, h3v]
    have e8 : evalF κ (.ite "f" .skip .fail) s L7 = .ok s L7 3 := by
      simp [evalF, Exp.ev, h7f, Exp.cost, Res.addCost]
    have e9 : evalF κ (.ite ("sd" =ₑ 1) .skip .fail) s L7 = .ok s L7 5 := by
      simp [evalF, Exp.ev, h7sd, OM.Machine.BinOp.eval, Exp.cost, Res.addCost]
    have a10 := evalF_assign_ok (κ := κ) (s := s) (L := L7) (x := "t") (e := .rd (.n .t2) "v") (v := V.t2)
      (by simp [Exp.ev, h7v, hvN, Fld.cap, Fld.get, NF.get, V])
    have a11 := evalF_assign_ok (κ := κ) (s := s) (L := upd L7 "t" V.t2) (x := "lf") (e := (0 : Exp)) (v := 0) rfl
    set L8 := upd (upd L7 "t" V.t2) "lf" 0
    have eR : ∃ cR, evalF κ dsRightS s L3 = .ok s L8 cR ∧ cR ≤ 120 + 40 * V.side.length := by
      refine ⟨_, evalF_seq_ok2 a5 (evalF_seq_ok2 e6 (evalF_seq_ok2 e7 (evalF_seq_ok2 e8 (evalF_seq_ok2 e9
        (evalF_seq_ok2 a10 a11))))), ?_⟩
      simp only [Exp.cost, costList, List.map, List.sum_cons, List.sum_nil, List.length_cons, List.length_nil] at hcg ⊢
      split <;> omega
    obtain ⟨cR, eR, hcR⟩ := eR
    refine ⟨L8, _, evalF_seq_ok2 a1 (evalF_seq_ok2 e2 (evalF_seq_ok2 e3 (evalF_seq_ok2 e4
      (evalF_ite_f hc6 eR)))), ?_, ?_, ?_, ?_, ?_, ?_⟩
    · simp [L8, OM.Machine.State.upd, hL7, L6, L5, hy]
    · simp [L8, OM.Machine.State.upd, ht]
    · simp [L8, OM.Machine.State.upd, hl, b2n]
    · simp [L8, OM.Machine.State.upd, hL7, L6, hy, hb1]
    · simp only [Exp.cost, costList, List.map, List.sum_cons, List.sum_nil, List.length_cons, List.length_nil] at hcf ⊢
      split <;> omega
    · intro r h1 h2 h3 h4 h5 h6 h7 h8
      simp only [L8, OM.Machine.State.upd, if_neg h5, if_neg h6]
      rw [hL7 r h3 h4]; simp only [L6, L5, OM.Machine.State.upd, if_neg h7, if_neg h8]
      rw [hL3 r h3 h4]; simp [L2, L1, OM.Machine.State.upd, h1, h2]

/-- A table lookup that must succeed: `r := lab? of entry e in table t`. -/
def labS (t e r : Reg) : Stm := (lookupP .table).call [.var t, .var e] ["f", r] ;; .ite "f" .skip .fail

theorem labS_ok {κ : Caps} {s : Core} {L : Loc} {t e r : Reg} {tv ev l : Nat} (hr : r ≠ "f") (ht : L t = tv)
    (he : L e = ev) (htr : tv < κ.lrec .table) (hl : (s.nodes.getX tv).lab? ev = some l) :
    ∃ c, evalF κ (labS t e r) s L =
      .ok s (OM.Machine.State.setLocs L ["f", r] [1, l]) c ∧ c ≤ 70 + 20 * (s.nodes.getX tv).table.length := by
  obtain ⟨Lf, cf, ef, hf, hv, -, -, hcf⟩ := lookupP_agree κ .table s
    (OM.Machine.State.setLocs (fun _ => 0) ["i", "x"] [tv, ev]) (i := tv) (x := ev)
    (by simp [OM.Machine.State.setLocs, OM.Machine.State.upd])
    (by simp [OM.Machine.State.setLocs, OM.Machine.State.upd]) htr
  have hlk : lookup (LK.view s tv .table) ev = some l := hl
  rw [hlk] at hf hv
  simp only [Option.isSome_some, if_true, Option.getD_some] at hf hv
  have e1 := evalF_call_ok (q := lookupP .table) (args := [.var t, .var e]) (ds := ["f", r]) (L := L)
    (by simp [evList, Exp.ev, ht, he]) ef
  have hL : OM.Machine.State.setLocs L ["f", r] ((lookupP .table).rets.map Lf) =
      OM.Machine.State.setLocs L ["f", r] [1, l] := by simp [lookupP, hf, hv]
  rw [hL] at e1
  have hf1 : OM.Machine.State.setLocs L ["f", r] [1, l] "f" = 1 := by
    simp [OM.Machine.State.setLocs, OM.Machine.State.upd, Ne.symm hr]
  have e2 : evalF κ (.ite "f" .skip .fail) s (OM.Machine.State.setLocs L ["f", r] [1, l]) =
      .ok s (OM.Machine.State.setLocs L ["f", r] [1, l]) 3 := by
    simp only [evalF, Exp.ev, hf1]; simp [Exp.cost, Res.addCost]
  refine ⟨_, evalF_seq_ok2 e1 e2, ?_⟩
  simp only [LK.view, costList, List.map, List.sum_cons, List.sum_nil, Exp.cost, List.length_cons,
    List.length_nil] at hcf ⊢
  omega

/-- The labels around the move and the tag fields they make (locals `v h y t bl`). -/
def dsLabS : Stm :=
  .ite ("h" <ₑ .prm .H) .skip .fail ;;
  "pr" ::= .prd "y" ("h" + 1) ;;
  labS "pr" "t" "pt" ;; labS "t" "bl" "tb" ;; labS "pr" "v" "pv" ;; labS "v" "bl" "vb" ;;
  "e1" ::= .bin .shl 1 ("h" * .prm .beta) ;; "e0" ::= .bin .shl 1 (("h" - 1) * .prm .beta) ;;
  "old" ::= "pv" * "e1" + "vb" * "e0" ;; "new" ::= "pt" * "e1" + "tb" * "e0"

theorem dsLabS_ok {κ : Caps} {s : Core} {L : Loc} {v h y t bl pt tb pv vb : Nat}
    (hv : L "v" = v) (hh : L "h" = h) (hy : L "y" = y) (ht : L "t" = t) (hbl : L "bl" = bl)
    (hhH : h < s.P.H) (h1 : 1 ≤ h) (hnp : notPrep s y) (hyC : y < κ.tbl .C) (hw : h + 1 < κ.pw)
    (hpt : (s.nodes.getX ((s.path.getX y).getX (h + 1))).lab? t = some pt)
    (htb : (s.nodes.getX t).lab? bl = some tb)
    (hpv : (s.nodes.getX ((s.path.getX y).getX (h + 1))).lab? v = some pv)
    (hvb : (s.nodes.getX v).lab? bl = some vb)
    (htbB : tb < 2 ^ s.P.beta) (hvbB : vb < 2 ^ s.P.beta)
    (hprr : (s.path.getX y).getX (h + 1) < κ.lrec .table) (htr : t < κ.lrec .table) (hvr : v < κ.lrec .table) :
    ∃ L' c, evalF κ dsLabS s L = .ok s L' c ∧
      L' "old" = (pv <<< (h * s.P.beta)) ||| (vb <<< ((h - 1) * s.P.beta)) ∧
      L' "new" = (pt <<< (h * s.P.beta)) ||| (tb <<< ((h - 1) * s.P.beta)) ∧
      c ≤ 400 + 40 * (s.nodes.getX ((s.path.getX y).getX (h + 1))).table.length +
        20 * (s.nodes.getX t).table.length + 20 * (s.nodes.getX v).table.length ∧
      ∀ r, r = "v" ∨ r = "y" ∨ r = "t" ∨ r = "lf" ∨ r = "h" → L' r = L r := by
  set pr := (s.path.getX y).getX (h + 1)
  set β := s.P.beta
  have e1 : evalF κ (.ite ("h" <ₑ .prm .H) .skip .fail) s L = .ok s L 6 := by
    simp [evalF, Exp.ev, hh, OM.Machine.BinOp.eval, PF.get, hhH, Exp.cost, Res.addCost]
  have a2 := evalF_assign_ok (κ := κ) (s := s) (L := L) (x := "pr") (e := .prd "y" ("h" + 1)) (v := pr)
    (by simp [Exp.ev, hy, hh, OM.Machine.BinOp.eval, hyC, hw, rowOf_notPrep hnp, pr])
  set L2 := upd L "pr" pr
  obtain ⟨c3, e3, hc3⟩ := labS_ok (κ := κ) (s := s) (L := L2) (t := "pr") (e := "t") (r := "pt") (by decide)
    (by simp [L2, OM.Machine.State.upd]) (by simp [L2, OM.Machine.State.upd, ht]) hprr hpt
  set L3 := OM.Machine.State.setLocs L2 ["f", "pt"] [1, pt]
  obtain ⟨c4, e4, hc4⟩ := labS_ok (κ := κ) (s := s) (L := L3) (t := "t") (e := "bl") (r := "tb") (by decide)
    (by simp [L3, L2, OM.Machine.State.setLocs, OM.Machine.State.upd, ht])
    (by simp [L3, L2, OM.Machine.State.setLocs, OM.Machine.State.upd, hbl]) htr htb
  set L4 := OM.Machine.State.setLocs L3 ["f", "tb"] [1, tb]
  obtain ⟨c5, e5, hc5⟩ := labS_ok (κ := κ) (s := s) (L := L4) (t := "pr") (e := "v") (r := "pv") (by decide)
    (by simp [L4, L3, L2, OM.Machine.State.setLocs, OM.Machine.State.upd])
    (by simp [L4, L3, L2, OM.Machine.State.setLocs, OM.Machine.State.upd, hv]) hprr hpv
  set L5 := OM.Machine.State.setLocs L4 ["f", "pv"] [1, pv]
  obtain ⟨c6, e6, hc6⟩ := labS_ok (κ := κ) (s := s) (L := L5) (t := "v") (e := "bl") (r := "vb") (by decide)
    (by simp [L5, L4, L3, L2, OM.Machine.State.setLocs, OM.Machine.State.upd, hv])
    (by simp [L5, L4, L3, L2, OM.Machine.State.setLocs, OM.Machine.State.upd, hbl]) hvr hvb
  set L6 := OM.Machine.State.setLocs L5 ["f", "vb"] [1, vb]
  have hL6 : ∀ r, r ≠ "pr" → r ≠ "f" → r ≠ "pt" → r ≠ "tb" → r ≠ "pv" → r ≠ "vb" → L6 r = L r := by
    intro r h1 h2 h3 h4 h5 h6
    simp [L6, L5, L4, L3, L2, OM.Machine.State.setLocs, OM.Machine.State.upd, h1, h2, h3, h4, h5, h6]
  have h6 : L6 "pt" = pt ∧ L6 "tb" = tb ∧ L6 "pv" = pv ∧ L6 "vb" = vb ∧ L6 "h" = h := by
    simp [L6, L5, L4, L3, L2, OM.Machine.State.setLocs, OM.Machine.State.upd, hh]
  obtain ⟨h6pt, h6tb, h6pv, h6vb, h6h⟩ := h6
  have a7 := evalF_assign_ok (κ := κ) (s := s) (L := L6) (x := "e1") (e := .bin .shl 1 ("h" * .prm .beta))
    (v := 2 ^ (h * β)) (by simp [Exp.ev, h6h, OM.Machine.BinOp.eval, PF.get, β])
  set L7 := upd L6 "e1" (2 ^ (h * β))
  have a8 := evalF_assign_ok (κ := κ) (s := s) (L := L7) (x := "e0") (e := .bin .shl 1 (("h" - 1) * .prm .beta))
    (v := 2 ^ ((h - 1) * β)) (by simp [Exp.ev, L7, OM.Machine.State.upd, h6h, OM.Machine.BinOp.eval, PF.get, β, h1])
  set L8 := upd L7 "e0" (2 ^ ((h - 1) * β))
  have a9 := evalF_assign_ok (κ := κ) (s := s) (L := L8) (x := "old") (e := "pv" * "e1" + "vb" * "e0")
    (v := pv * 2 ^ (h * β) + vb * 2 ^ ((h - 1) * β))
    (by simp [Exp.ev, L8, L7, OM.Machine.State.upd, h6pv, h6vb, OM.Machine.BinOp.eval])
  set L9 := upd L8 "old" (pv * 2 ^ (h * β) + vb * 2 ^ ((h - 1) * β))
  have a10 := evalF_assign_ok (κ := κ) (s := s) (L := L9) (x := "new") (e := "pt" * "e1" + "tb" * "e0")
    (v := pt * 2 ^ (h * β) + tb * 2 ^ ((h - 1) * β))
    (by simp [Exp.ev, L9, L8, L7, OM.Machine.State.upd, h6pt, h6tb, OM.Machine.BinOp.eval])
  refine ⟨_, _, evalF_seq_ok2 e1 (evalF_seq_ok2 a2 (evalF_seq_ok2 e3 (evalF_seq_ok2 e4 (evalF_seq_ok2 e5
    (evalF_seq_ok2 e6 (evalF_seq_ok2 a7 (evalF_seq_ok2 a8 (evalF_seq_ok2 a9 a10)))))))), ?_, ?_, ?_, ?_⟩
  · simp [L9, OM.Machine.State.upd, lor_shift pv vb β h hvbB h1]
  · simp [OM.Machine.State.upd, lor_shift pt tb β h htbB h1]
  · simp only [Exp.cost, Exp.ofNat_def, Exp.mul_def, Exp.add_def, Exp.sub_def] at hc3 hc4 hc5 hc6 ⊢; omega
  · intro r hr
    have : r ≠ "pr" ∧ r ≠ "f" ∧ r ≠ "pt" ∧ r ≠ "tb" ∧ r ≠ "pv" ∧ r ≠ "vb" ∧ r ≠ "e1" ∧ r ≠ "e0" ∧ r ≠ "old" ∧
        r ≠ "new" := by rcases hr with rfl | rfl | rfl | rfl | rfl <;> decide
    obtain ⟨a, b, c, d, e, f, g, i, k, m⟩ := this
    simp only [L9, L8, L7, OM.Machine.State.upd, if_neg g, if_neg i, if_neg k, if_neg m]
    exact hL6 r a b c d e f

/-- Two writes to the same node. -/
theorem evalF_wrN2 {κ : Caps} {s : Core} {L : Loc} {k1 k2 : NF} {i e1 e2 : Exp} {j w1 w2 : Nat}
    (hi : ∀ S : Core, i.ev κ S L = some j) (he1 : ∀ S : Core, e1.ev κ S L = some w1)
    (he2 : ∀ S : Core, e2.ev κ S L = some w2) (hj : j < s.nodes.size) (hc : j < κ.tbl .N)
    (hk1 : k1.ok w1 = true) (hk2 : k2.ok w2 = true) :
    evalF κ (.wr (.n k1) i e1 ;; .wr (.n k2) i e2) s L =
      .ok { s with nodes := s.nodes.modify j fun n => NF.set (NF.set n w1 k1) w2 k2 } L
        (1 + i.cost + e1.cost + (1 + i.cost + e2.cost)) := by
  have w1' := evalF_wrN_ok (κ := κ) (s := s) (L := L) (k := k1) (i := i) (e := e1) (j := j) (w := w1) (hi _) (he1 _)
    hj hc hk1
  have w2' := evalF_wrN_ok (κ := κ) (s := { s with nodes := s.nodes.modify j (NF.set · w1 k1) }) (L := L) (k := k2)
    (i := i) (e := e2) (j := j) (w := w2) (hi _) (he2 _) (by simp [hj]) hc hk2
  rw [Array.modify_modify_same] at w2'
  exact evalF_seq_ok2 w1' w2'

def dsTagS : Stm :=
  "ty" ::= .rd (.c .tag) "y" ;; .ite ("ty" <ₑ "old") .fail .skip ;;
  "tg" ::= "ty" - "old" + "new" ;; gstP.call [.var "y", .var "tg"] []
def dsRangeS : Stm :=
  .ite (.rd (.n .first) "v" =ₑ .rd (.n .last) "v") (.wr (.n .first) "v" 0 ;; .wr (.n .last) "v" 0)
    (.ite "lf" (.wr (.n .first) "v" (.rd (.c .next) "y")) (.wr (.n .last) "v" (.rd (.c .prev) "y")))
def dsTgtS : Stm :=
  .ite "lf" (.ite (.rd (.n .first) "t" =ₑ 0) (.wr (.n .first) "t" "y") .skip ;; .wr (.n .last) "t" "y")
            (.ite (.rd (.n .last) "t" =ₑ 0) (.wr (.n .last) "t" "y") .skip ;; .wr (.n .first) "t" "y")
/-- The writes of a sweep step that moves chunk `y` to target `t` (locals `v h y t lf old new`). -/
def dsMutS : Stm := dsTagS ;; .pwr "y" "h" "t" ;; dsRangeS ;; dsTgtS

theorem dsMutS_ok {κ : Caps} {s : Core} {L : Loc} {v old new : Nat}
    (hv : L "v" = v) (hh : L "h" = (s.nodes.getX v).height) (hy : L "y" = dsY s v) (ht : L "t" = dsT s v)
    (hlf : L "lf" = b2n (decide (goesLeft s v))) (hold : L "old" = old) (hnew : L "new" = new)
    (hle : old ≤ (s.C.getX (dsY s v)).tag) (hok : OM.Proof.TagOK s (dsY s v) ((s.C.getX (dsY s v)).tag - old + new))
    (hys : dsY s v < s.C.size) (hyC : dsY s v < κ.tbl .C)
    (hyP : (s.C.getX (dsY s v)).prev < κ.tbl .C) (hyN : (s.C.getX (dsY s v)).next < κ.tbl .C)
    (hnp : notPrep s (dsY s v)) (hw : (s.nodes.getX v).height < κ.pw)
    (hvs : v < s.nodes.size) (hts : dsT s v < s.nodes.size) (hvN : v < κ.tbl .N) (htN : dsT s v < κ.tbl .N)
    (htv : dsT s v ≠ v) :
    ∃ L' c, evalF κ dsMutS s L = .ok (dsS s v ((s.C.getX (dsY s v)).tag - old + new)) L' c ∧ c ≤ 150 ∧
      ∀ r, r ≠ "ty" → r ≠ "tg" → L' r = L r := by
  set y := dsY s v
  set t := dsT s v
  set V := s.nodes.getX v
  set cy := s.C.getX y
  set tag := cy.tag - old + new
  -- the tag
  have a1 := evalF_assign_ok (κ := κ) (s := s) (L := L) (x := "ty") (e := .rd (.c .tag) "y") (v := cy.tag)
    (by simp [Exp.ev, hy, hyC, Fld.cap, Fld.get, CF.get, cy, y])
  set L1 := upd L "ty" cy.tag
  have e2 : evalF κ (.ite ("ty" <ₑ "old") .fail .skip) s L1 = .ok s L1 5 := by
    have : ¬ cy.tag < old := by omega
    simp [evalF, Exp.ev, L1, OM.Machine.State.upd, hold, OM.Machine.BinOp.eval, this, Exp.cost, Res.addCost]
  have a3 := evalF_assign_ok (κ := κ) (s := s) (L := L1) (x := "tg") (e := "ty" - "old" + "new") (v := tag)
    (by simp [Exp.ev, L1, OM.Machine.State.upd, hold, hnew, OM.Machine.BinOp.eval, hle, tag])
  set L3 := upd L1 "tg" tag
  have h3 : ∀ r, r ≠ "ty" → r ≠ "tg" → L3 r = L r := fun r h1 h2 => by simp [L3, L1, OM.Machine.State.upd, h1, h2]
  obtain ⟨Lg, cg, eg, hcg⟩ := gstP_agree (κ := κ) (s := s)
    (L := OM.Machine.State.setLocs (fun _ => 0) ["c", "t"] [y, tag]) (c := y) (t := tag)
    (by simp [OM.Machine.State.setLocs, OM.Machine.State.upd]) (by simp [OM.Machine.State.setLocs, OM.Machine.State.upd])
    hys hyC hyP hyN hok
  have e4 := evalF_call_ok (q := gstP) (args := [.var "y", .var "tg"]) (ds := []) (L := L3)
    (by simp [evList, Exp.ev, L3, L1, OM.Machine.State.upd, hy]) eg
  set s1 : Core := { s with C := s.C.modify y fun C => { C with tag := tag } }
  have e14 : ∃ c, evalF κ dsTagS s L = .ok s1 L3 c ∧ c ≤ 60 := by
    refine ⟨_, evalF_seq_ok2 a1 (evalF_seq_ok2 e2 (evalF_seq_ok2 a3 e4)), ?_⟩
    simp [Exp.cost, costList]; omega
  obtain ⟨c14, e14, hc14⟩ := e14
  have h3v : L3 "v" = v := by rw [h3 _ (by decide) (by decide), hv]
  have h3h : L3 "h" = V.height := by rw [h3 _ (by decide) (by decide), hh]
  have h3y : L3 "y" = y := by rw [h3 _ (by decide) (by decide), hy]
  have h3t : L3 "t" = t := by rw [h3 _ (by decide) (by decide), ht]
  have h3lf : L3 "lf" = b2n (decide (goesLeft s v)) := by rw [h3 _ (by decide) (by decide), hlf]
  -- the path
  set s2 : Core := { s1 with path := s1.path.setX y ((s1.path.getX y).setX V.height t) }
  have e5 : evalF κ (.pwr "y" "h" "t") s1 L3 = .ok s2 L3 7 := by
    have : notPrep s1 y := hnp
    simp [evalF, Exp.ev, h3y, h3h, h3t, hyC, hw, this, Exp.cost, s2]
  have hs2v : s2.nodes = s.nodes := rfl
  have hs2y : s2.C.getX y = { cy with tag := tag } := by
    simp only [s2, s1, getX_modify', hys, and_self, if_true]; rfl
  -- the range of `v`
  set s3 : Core := if V.first == V.last then
      { s2 with nodes := s2.nodes.modify v fun n => { n with first := NIL, last := NIL } }
    else if goesLeft s v then { s2 with nodes := s2.nodes.modify v fun n => { n with first := cy.next } }
    else { s2 with nodes := s2.nodes.modify v fun n => { n with last := cy.prev } }
  have e6 : ∃ c6, evalF κ dsRangeS s2 L3 = .ok s3 L3 c6 ∧ c6 ≤ 20 := by
    by_cases hfl : V.first = V.last
    · have hfl' : (s.nodes.getX v).first = (s.nodes.getX v).last := hfl
      have w := evalF_wrN2 (κ := κ) (s := s2) (L := L3) (k1 := .first) (k2 := .last) (i := .var "v") (e1 := (0 : Exp))
        (e2 := (0 : Exp)) (ev_var_const h3v) (ev_lit_const 0) (ev_lit_const 0) (by rw [hs2v]; exact hvs) hvN rfl rfl
      have hs3 : s3 = { s2 with nodes := s2.nodes.modify v fun n => NF.set (NF.set n 0 .first) 0 .last } := by
        simp only [s3, hfl, beq_self_eq_true, if_true]; rfl
      rw [← hs3] at w
      exact ⟨_, evalF_ite_t (v := 1) (by simp [Exp.ev, OM.Machine.BinOp.eval, h3v, hvN, Fld.cap, Fld.get, NF.get,
        hs2v, hfl']) one_ne_zero w, by simp [Exp.cost]⟩
    · have hfl' : ¬ (s.nodes.getX v).first = (s.nodes.getX v).last := hfl
      have hc : (.rd (.n .first) "v" =ₑ .rd (.n .last) "v" : Exp).ev κ s2 L3 = some 0 := by
        simp [Exp.ev, OM.Machine.BinOp.eval, h3v, hvN, Fld.cap, Fld.get, NF.get, hs2v, hfl']
      by_cases hl : goesLeft s v
      · have w := evalF_wrN_ok (κ := κ) (s := s2) (L := L3) (k := .first) (i := .var "v") (e := .rd (.c .next) "y")
          (j := v) (w := cy.next) (by simp [Exp.ev, h3v]) (by simp [Exp.ev, h3y, hyC, Fld.cap, Fld.get, CF.get, hs2y])
          (by rw [hs2v]; exact hvs) hvN rfl
        have hs3 : s3 = { s2 with nodes := s2.nodes.modify v (NF.set · cy.next .first) } := by
          simp only [s3, if_neg (show ¬ (V.first == V.last) = true by simpa using hfl), if_pos hl]; rfl
        rw [← hs3] at w
        exact ⟨_, evalF_ite_f hc (evalF_ite_t (v := 1) (by simp [Exp.ev, h3lf, hl, b2n]) one_ne_zero w),
          by simp [Exp.cost]⟩
      · have w := evalF_wrN_ok (κ := κ) (s := s2) (L := L3) (k := .last) (i := .var "v") (e := .rd (.c .prev) "y")
          (j := v) (w := cy.prev) (by simp [Exp.ev, h3v]) (by simp [Exp.ev, h3y, hyC, Fld.cap, Fld.get, CF.get, hs2y])
          (by rw [hs2v]; exact hvs) hvN rfl
        have hs3 : s3 = { s2 with nodes := s2.nodes.modify v (NF.set · cy.prev .last) } := by
          simp only [s3, if_neg (show ¬ (V.first == V.last) = true by simpa using hfl), if_neg hl]; rfl
        rw [← hs3] at w
        exact ⟨_, evalF_ite_f hc (evalF_ite_f (by simp [Exp.ev, h3lf, hl, b2n]) w), by simp [Exp.cost]⟩
  obtain ⟨c6, e6, hc6⟩ := e6
  have hs3t : s3.nodes.getX t = s.nodes.getX t := by
    simp only [s3]; split
    · simp only [getX_modify']; rw [if_neg (fun h => htv h.1)]
    · split <;> simp only [getX_modify'] <;> rw [if_neg (fun h => htv h.1)]
  have hs3n : s3.nodes.size = s.nodes.size := by simp only [s3]; split; simp [s2, s1]; split <;> simp [s2, s1]
  -- the target
  set T := s.nodes.getX t
  have e7 : ∃ c7, evalF κ dsTgtS s3 L3 = .ok (dsS s v tag) L3 c7 ∧ c7 ≤ 30 := by
    by_cases hl : goesLeft s v
    · set s4 : Core := if T.first == NIL then { s3 with nodes := s3.nodes.modify t fun n => { n with first := y } } else s3
      have hfin : dsS s v tag = { s4 with nodes := s4.nodes.modify t fun n => { n with last := y } } := by
        simp only [dsS, s4, s3, if_pos hl]; rfl
      have e8 : ∃ c8, evalF κ (.ite (.rd (.n .first) "t" =ₑ 0) (.wr (.n .first) "t" "y") .skip) s3 L3 = .ok s4 L3 c8 ∧
          c8 ≤ 12 := by
        by_cases hT : T.first = 0
        · have hT' : (s.nodes.getX t).first = 0 := hT
          have w := evalF_wrN_ok (κ := κ) (s := s3) (L := L3) (k := .first) (i := .var "t") (e := .var "y")
            (j := t) (w := y) (by simp [Exp.ev, h3t]) (by simp [Exp.ev, h3y]) (by rw [hs3n]; exact hts) htN rfl
          have hs4 : s4 = { s3 with nodes := s3.nodes.modify t (NF.set · y .first) } := by
            simp only [s4, show (T.first == NIL) = true from beq_iff_eq.mpr hT, if_true]; rfl
          rw [← hs4] at w
          exact ⟨_, evalF_ite_t (v := 1) (by simp [Exp.ev, OM.Machine.BinOp.eval, h3t, htN, Fld.cap, Fld.get, NF.get,
            hs3t, hT]) one_ne_zero w, by simp [Exp.cost]⟩
        · have hT' : ¬ (s.nodes.getX t).first = 0 := hT
          have hs4 : s4 = s3 := by
            simp only [s4, show (T.first == NIL) = false from beq_eq_false_iff_ne.mpr hT, Bool.false_eq_true, if_false]
          rw [hs4]
          exact ⟨_, evalF_ite_f (by simp [Exp.ev, OM.Machine.BinOp.eval, h3t, htN, Fld.cap, Fld.get, NF.get,
            hs3t, hT]) evalF_skip, by simp [Exp.cost]⟩
      obtain ⟨c8, e8, hc8⟩ := e8
      have hs4n : s4.nodes.size = s.nodes.size := by simp only [s4]; split <;> simp [hs3n]
      have w := evalF_wrN_ok (κ := κ) (s := s4) (L := L3) (k := .last) (i := .var "t") (e := .var "y")
        (j := t) (w := y) (by simp [Exp.ev, h3t]) (by simp [Exp.ev, h3y]) (by rw [hs4n]; exact hts) htN rfl
      rw [hfin]
      exact ⟨_, evalF_ite_t (v := 1) (by simp [Exp.ev, h3lf, hl, b2n]) one_ne_zero (evalF_seq_ok2 e8 w),
        by simp [Exp.cost]; omega⟩
    · set s4 : Core := if T.last == NIL then { s3 with nodes := s3.nodes.modify t fun n => { n with last := y } } else s3
      have hfin : dsS s v tag = { s4 with nodes := s4.nodes.modify t fun n => { n with first := y } } := by
        simp only [dsS, s4, s3, if_neg hl]; rfl
      have e8 : ∃ c8, evalF κ (.ite (.rd (.n .last) "t" =ₑ 0) (.wr (.n .last) "t" "y") .skip) s3 L3 = .ok s4 L3 c8 ∧
          c8 ≤ 12 := by
        by_cases hT : T.last = 0
        · have hT' : (s.nodes.getX t).last = 0 := hT
          have w := evalF_wrN_ok (κ := κ) (s := s3) (L := L3) (k := .last) (i := .var "t") (e := .var "y")
            (j := t) (w := y) (by simp [Exp.ev, h3t]) (by simp [Exp.ev, h3y]) (by rw [hs3n]; exact hts) htN rfl
          have hs4 : s4 = { s3 with nodes := s3.nodes.modify t (NF.set · y .last) } := by
            simp only [s4, show (T.last == NIL) = true from beq_iff_eq.mpr hT, if_true]; rfl
          rw [← hs4] at w
          exact ⟨_, evalF_ite_t (v := 1) (by simp [Exp.ev, OM.Machine.BinOp.eval, h3t, htN, Fld.cap, Fld.get, NF.get,
            hs3t, hT]) one_ne_zero w, by simp [Exp.cost]⟩
        · have hT' : ¬ (s.nodes.getX t).last = 0 := hT
          have hs4 : s4 = s3 := by
            simp only [s4, show (T.last == NIL) = false from beq_eq_false_iff_ne.mpr hT, Bool.false_eq_true, if_false]
          rw [hs4]
          exact ⟨_, evalF_ite_f (by simp [Exp.ev, OM.Machine.BinOp.eval, h3t, htN, Fld.cap, Fld.get, NF.get,
            hs3t, hT]) evalF_skip, by simp [Exp.cost]⟩
      obtain ⟨c8, e8, hc8⟩ := e8
      have hs4n : s4.nodes.size = s.nodes.size := by simp only [s4]; split <;> simp [hs3n]
      have w := evalF_wrN_ok (κ := κ) (s := s4) (L := L3) (k := .first) (i := .var "t") (e := .var "y")
        (j := t) (w := y) (by simp [Exp.ev, h3t]) (by simp [Exp.ev, h3y]) (by rw [hs4n]; exact hts) htN rfl
      rw [hfin]
      exact ⟨_, evalF_ite_f (by simp [Exp.ev, h3lf, hl, b2n]) (evalF_seq_ok2 e8 w), by simp [Exp.cost]; omega⟩
  obtain ⟨c7, e7, hc7⟩ := e7
  exact ⟨L3, _, evalF_seq_ok2 e14 (evalF_seq_ok2 e5 (evalF_seq_ok2 e6 e7)), by omega, h3⟩

/-- A sweep step that moves a chunk (locals `v h`). -/
def dsMoveS : Stm := dsPickS ;; dsLabS ;; dsMutS

theorem dsMoveS_ok {κ : Caps} {s : Core} {L : Loc} {v pt tb pv vb : Nat}
    (hv : L "v" = v) (hh : L "h" = (s.nodes.getX v).height)
    -- Level F (as in `drainStep_move`)
    (hside : goesLeft s v ∨
      lookup (s.nodes.getX v).side (belowY s v (s.nodes.getX v).first) = some .right ∧
      lookup (s.nodes.getX v).side (belowY s v (s.nodes.getX v).last) = some .right)
    (hsz : (s.nodes.getX v).height + 1 < (s.path.getX (dsY s v)).size)
    (hpt : (s.nodes.getX ((s.path.getX (dsY s v)).getX ((s.nodes.getX v).height + 1))).lab? (dsT s v) = some pt)
    (htb : (s.nodes.getX (dsT s v)).lab? (belowY s v (dsY s v)) = some tb)
    (hpv : (s.nodes.getX ((s.path.getX (dsY s v)).getX ((s.nodes.getX v).height + 1))).lab? v = some pv)
    (hvb : (s.nodes.getX v).lab? (belowY s v (dsY s v)) = some vb)
    (hold : (pv <<< ((s.nodes.getX v).height * s.P.beta)) |||
        (vb <<< (((s.nodes.getX v).height - 1) * s.P.beta)) ≤ (s.C.getX (dsY s v)).tag)
    (hok : OM.Proof.TagOK s (dsY s v) (dsTag s v pt tb pv vb))
    -- the shape
    (h1 : 1 ≤ (s.nodes.getX v).height) (hpsz : (s.path.getX (dsY s v)).size = s.P.H + 1)
    (htbB : tb < 2 ^ s.P.beta) (hvbB : vb < 2 ^ s.P.beta) (htv : dsT s v ≠ v)
    (hvs : v < s.nodes.size) (hts : dsT s v < s.nodes.size) (hys : dsY s v < s.C.size)
    (hnf : notPrep s (s.nodes.getX v).first) (hnl : notPrep s (s.nodes.getX v).last)
    -- capacities
    (hvN : v < κ.tbl .N) (htN : dsT s v < κ.tbl .N) (hvsd : v < κ.lrec .side) (hvr : v < κ.lrec .table)
    (htr : dsT s v < κ.lrec .table)
    (hprr : (s.path.getX (dsY s v)).getX ((s.nodes.getX v).height + 1) < κ.lrec .table)
    (hfC : (s.nodes.getX v).first < κ.tbl .C) (hlC : (s.nodes.getX v).last < κ.tbl .C)
    (hyP : (s.C.getX (dsY s v)).prev < κ.tbl .C) (hyN : (s.C.getX (dsY s v)).next < κ.tbl .C)
    (hw : (s.nodes.getX v).height + 1 < κ.pw) :
    ∃ L' c, evalF κ dsMoveS s L = .ok (dsS s v (dsTag s v pt tb pv vb)) L' c ∧
      c ≤ 1000 + 80 * (s.nodes.getX v).side.length +
        40 * (s.nodes.getX ((s.path.getX (dsY s v)).getX ((s.nodes.getX v).height + 1))).table.length +
        20 * (s.nodes.getX (dsT s v)).table.length + 20 * (s.nodes.getX v).table.length ∧
      L' "v" = v ∧ L' "h" = (s.nodes.getX v).height := by
  set h := (s.nodes.getX v).height
  have hyE : dsY s v = (s.nodes.getX v).first ∨ dsY s v = (s.nodes.getX v).last := by
    unfold dsY; split <;> simp
  have hnp : notPrep s (dsY s v) := by rcases hyE with e | e <;> rw [e] <;> assumption
  have hyC : dsY s v < κ.tbl .C := by rcases hyE with e | e <;> rw [e] <;> assumption
  obtain ⟨L1, c1, e1, h1y, h1t, h1lf, h1bl, hc1, hF1⟩ := dsPickS_ok (κ := κ) (s := s) (L := L) hv hh h1 hside hvN hvsd
    hnf hnl hfC hlC (by omega)
  have hF1' : ∀ r, r = "v" ∨ r = "h" → L1 r = L r := by
    intro r hr; apply hF1 <;> rcases hr with rfl | rfl <;> decide
  obtain ⟨L2, c2, e2, h2o, h2n, hc2, hF2⟩ := dsLabS_ok (κ := κ) (s := s) (L := L1) (v := v) (h := h)
    (y := dsY s v) (t := dsT s v) (bl := belowY s v (dsY s v)) (pt := pt) (tb := tb) (pv := pv) (vb := vb)
    (by rw [hF1' "v" (by simp), hv]) (by rw [hF1' "h" (by simp), hh]) h1y h1t h1bl (by omega) h1 hnp hyC hw
    hpt htb hpv hvb htbB hvbB hprr htr hvr
  obtain ⟨L3, c3, e3, hc3, hF3⟩ := dsMutS_ok (κ := κ) (s := s) (L := L2) (v := v)
    (old := (pv <<< (h * s.P.beta)) ||| (vb <<< ((h - 1) * s.P.beta)))
    (new := (pt <<< (h * s.P.beta)) ||| (tb <<< ((h - 1) * s.P.beta)))
    (by rw [hF2 "v" (by simp), hF1' "v" (by simp), hv]) (by rw [hF2 "h" (by simp), hF1' "h" (by simp), hh])
    (by rw [hF2 "y" (by simp), h1y]) (by rw [hF2 "t" (by simp), h1t]) (by rw [hF2 "lf" (by simp), h1lf]) h2o h2n
    hold hok hys hyC hyP hyN hnp (by omega) hvs hts hvN htN htv
  refine ⟨L3, _, evalF_seq_ok2 e1 (evalF_seq_ok2 e2 e3), by omega, ?_, ?_⟩
  · rw [hF3 "v" (by decide) (by decide), hF2 "v" (by simp), hF1' "v" (by simp), hv]
  · rw [hF3 "h" (by decide) (by decide), hF2 "h" (by simp), hF1' "h" (by simp), hh]

/-! ### `drainStep` -/

/-- `ok := drainStep v`. -/
def dsP : Proc where
  name := "drainStep"
  params := ["v"]
  rets := ["ok"]
  body :=
    .ite (.rd (.n .dead) "v") ("ok" ::= 0)
      ("h" ::= .rd (.n .height) "v" ;;
       .ite (.rd (.n .first) "v" =ₑ 0) (finishDrainS ;; "ok" ::= 0) (dsMoveS ;; "ok" ::= 1))

theorem dsP_dead {κ : Caps} {s : Core} {L : Loc} {v : Nat} (hv : L "v" = v) (hvN : v < κ.tbl .N)
    (hal : (s.nodes.getX v).alive = false) :
    ∃ L' c, evalF κ dsP.body s L = .ok s L' c ∧ L' "ok" = 0 ∧ c ≤ 10 := by
  refine ⟨_, _, evalF_ite_t (v := 1) (by simp [Exp.ev, hv, hvN, Fld.cap, Fld.get, NF.get, hal, b2n]) one_ne_zero
    (evalF_assign_ok (v := 0) rfl), by simp [OM.Machine.State.upd], by simp [Exp.cost]⟩

theorem dsP_pre {κ : Caps} {s : Core} {L : Loc} {v : Nat} (hv : L "v" = v) (hvN : v < κ.tbl .N)
    (hal : (s.nodes.getX v).alive = true) {s' : Core} {L' : Loc} {c : Nat}
    (h : evalF κ (.ite (.rd (.n .first) "v" =ₑ 0) (finishDrainS ;; "ok" ::= 0) (dsMoveS ;; "ok" ::= 1)) s
      (upd L "h" (s.nodes.getX v).height) = .ok s' L' c) :
    evalF κ dsP.body s L = .ok s' L' (c + 6) := by
  have a1 := evalF_assign_ok (κ := κ) (s := s) (L := L) (x := "h") (e := .rd (.n .height) "v")
    (v := (s.nodes.getX v).height) (by simp [Exp.ev, hv, hvN, Fld.cap, Fld.get, NF.get])
  have := evalF_ite_f (t := ("ok" ::= 0)) (by simp [Exp.ev, hv, hvN, Fld.cap, Fld.get, NF.get, hal, b2n] :
    (Exp.rd (.n .dead) "v").ev κ s L = some 0) (evalF_seq_ok2 a1 h)
  convert this using 2
  · rfl
  · simp only [Exp.cost]; omega

theorem dsP_move {κ : Caps} {s : Core} {L : Loc} {v pt tb pv vb : Nat} (hv : L "v" = v)
    (hal : (s.nodes.getX v).alive = true) (hf : (s.nodes.getX v).first ≠ NIL)
    (hside : goesLeft s v ∨
      lookup (s.nodes.getX v).side (belowY s v (s.nodes.getX v).first) = some .right ∧
      lookup (s.nodes.getX v).side (belowY s v (s.nodes.getX v).last) = some .right)
    (hsz : (s.nodes.getX v).height + 1 < (s.path.getX (dsY s v)).size)
    (hpt : (s.nodes.getX ((s.path.getX (dsY s v)).getX ((s.nodes.getX v).height + 1))).lab? (dsT s v) = some pt)
    (htb : (s.nodes.getX (dsT s v)).lab? (belowY s v (dsY s v)) = some tb)
    (hpv : (s.nodes.getX ((s.path.getX (dsY s v)).getX ((s.nodes.getX v).height + 1))).lab? v = some pv)
    (hvb : (s.nodes.getX v).lab? (belowY s v (dsY s v)) = some vb)
    (hold : (pv <<< ((s.nodes.getX v).height * s.P.beta)) |||
        (vb <<< (((s.nodes.getX v).height - 1) * s.P.beta)) ≤ (s.C.getX (dsY s v)).tag)
    (hok : OM.Proof.TagOK s (dsY s v) (dsTag s v pt tb pv vb))
    (h1 : 1 ≤ (s.nodes.getX v).height) (hpsz : (s.path.getX (dsY s v)).size = s.P.H + 1)
    (htbB : tb < 2 ^ s.P.beta) (hvbB : vb < 2 ^ s.P.beta) (htv : dsT s v ≠ v)
    (hvs : v < s.nodes.size) (hts : dsT s v < s.nodes.size) (hys : dsY s v < s.C.size)
    (hnf : notPrep s (s.nodes.getX v).first) (hnl : notPrep s (s.nodes.getX v).last)
    (hvN : v < κ.tbl .N) (htN : dsT s v < κ.tbl .N) (hvsd : v < κ.lrec .side) (hvr : v < κ.lrec .table)
    (htr : dsT s v < κ.lrec .table)
    (hprr : (s.path.getX (dsY s v)).getX ((s.nodes.getX v).height + 1) < κ.lrec .table)
    (hfC : (s.nodes.getX v).first < κ.tbl .C) (hlC : (s.nodes.getX v).last < κ.tbl .C)
    (hyP : (s.C.getX (dsY s v)).prev < κ.tbl .C) (hyN : (s.C.getX (dsY s v)).next < κ.tbl .C)
    (hw : (s.nodes.getX v).height + 1 < κ.pw) :
    ∃ L' c, evalF κ dsP.body s L = .ok (dsS s v (dsTag s v pt tb pv vb)) L' c ∧ L' "ok" = 1 ∧
      c ≤ 1100 + 80 * (s.nodes.getX v).side.length +
        40 * (s.nodes.getX ((s.path.getX (dsY s v)).getX ((s.nodes.getX v).height + 1))).table.length +
        20 * (s.nodes.getX (dsT s v)).table.length + 20 * (s.nodes.getX v).table.length := by
  obtain ⟨L1, c1, e1, hc1, -, -⟩ := dsMoveS_ok (κ := κ) (s := s) (L := upd L "h" (s.nodes.getX v).height)
    (v := v) (by simp [OM.Machine.State.upd, hv]) (by simp [OM.Machine.State.upd]) hside hsz hpt htb hpv hvb hold hok
    h1 hpsz htbB hvbB htv hvs hts hys hnf hnl hvN htN hvsd hvr htr hprr hfC hlC hyP hyN hw
  have e2 := evalF_seq_ok2 e1 (evalF_assign_ok (κ := κ) (s := dsS s v (dsTag s v pt tb pv vb)) (L := L1) (x := "ok")
    (e := (1 : Exp)) (v := 1) rfl)
  have hc : (Exp.rd (.n .first) "v" =ₑ 0 : Exp).ev κ s (upd L "h" (s.nodes.getX v).height) = some 0 := by
    have : ¬ (s.nodes.getX v).first = 0 := hf
    simp [Exp.ev, OM.Machine.State.upd, hv, hvN, Fld.cap, Fld.get, NF.get, OM.Machine.BinOp.eval, this]
  have e3 := evalF_ite_f (t := finishDrainS ;; "ok" ::= 0) hc e2
  exact ⟨_, _, dsP_pre hv hvN hal e3, by simp [OM.Machine.State.upd], by simp [Exp.cost] at hc1 ⊢; omega⟩

theorem dsP_finish {κ : Caps} {s : Core} {L : Loc} {v B : Nat} (hv : L "v" = v)
    (hal : (s.nodes.getX v).alive = true) (hf : (s.nodes.getX v).first = NIL)
    (hnd : (s.nodes.getX v).inTables.Nodup) (hT : ∀ T ∈ (s.nodes.getX v).inTables, v ∈ (s.nodes.getX T).order)
    (hv0 : v ≠ 0) (hvs : v < s.nodes.size) (hvo : v ∉ (s.nodes.getX v).order)
    (hvN : v < κ.tbl .N) (hvr : v < κ.lrec .table) (hvi : v < κ.lrec .inTab)
    (ht1 : (s.nodes.getX v).t1 < κ.tbl .N) (ht2 : (s.nodes.getX v).t2 < κ.tbl .N)
    (hcE : ∀ e ∈ (s.nodes.getX v).order, e < κ.lrec .cin ∧ e < κ.lrec .inTab ∧
      (s.cin.getX e).length ≤ κ.lcap .cin ∧ (s.nodes.getX e).inTables.length ≤ κ.lcap .inTab ∧
      (s.cin.getX e).length ≤ B ∧ (s.nodes.getX e).inTables.length ≤ B)
    (hcT : ∀ T ∈ (s.nodes.getX v).inTables, T < κ.lrec .table ∧ T < κ.lrec .side ∧
      (s.nodes.getX T).table.length ≤ κ.lcap .table ∧ (s.nodes.getX T).side.length ≤ κ.lcap .side ∧
      (s.nodes.getX T).table.length ≤ B ∧ (s.nodes.getX T).side.length ≤ B) :
    ∃ L' c, evalF κ dsP.body s L = .ok (fdS v s) L' c ∧ L' "ok" = 0 ∧
      c ≤ 300 + (s.nodes.getX v).table.length * (171 + 100 * B) +
        (s.nodes.getX v).inTables.length * (301 + 200 * B) := by
  obtain ⟨L1, c1, e1, hc1, -⟩ := finishDrainS_ok (κ := κ) (s := s) (L := upd L "h" (s.nodes.getX v).height)
    (v := v) (B := B) (by simp [OM.Machine.State.upd, hv]) (by simp [OM.Machine.State.upd]) hnd hT hv0 hvs hvo hvN hvr
    hvi ht1 ht2 hcE hcT
  have e2 := evalF_seq_ok2 e1 (evalF_assign_ok (κ := κ) (s := fdS v s) (L := L1) (x := "ok") (e := (0 : Exp)) (v := 0) rfl)
  have hc : (Exp.rd (.n .first) "v" =ₑ 0 : Exp).ev κ s (upd L "h" (s.nodes.getX v).height) = some 1 := by
    have : (s.nodes.getX v).first = 0 := hf
    simp [Exp.ev, OM.Machine.State.upd, hv, hvN, Fld.cap, Fld.get, NF.get, OM.Machine.BinOp.eval, this]
  have e3 := evalF_ite_t (f := dsMoveS ;; "ok" ::= 1) hc one_ne_zero e2
  exact ⟨_, _, dsP_pre hv hvN hal e3, by simp [OM.Machine.State.upd], by simp [Exp.cost] at hc1 ⊢; omega⟩

/-! ### The funding loop, the step after a drain start, the walk -/

/-- The program agrees with Level F's `drainStep src` from `S` (within `D` steps). -/
def DSAgree (κ : Caps) (S : Core) (src D : Nat) : Prop :=
  ∀ b S', (drainStep src).run S = .ok b S' →
    ∃ L' c, evalF κ dsP.body S (OM.Machine.State.setLocs (fun _ => 0) ["v"] [src]) = .ok S' L' c ∧
      L' "ok" = b2n b ∧ c ≤ D ∧ S'.resJob = S.resJob

/-- `fundLoop` (locals `ja jb jc jd` = `v up src k`); the job's counter is updated. -/
def fundS : Stm :=
  .ite ("jd" <ₑ .prm .s)
    (dsP.call [.var "jc"] ["dk"] ;; .ite "dk" (.pcSet 4 "ja" "jb" "jc" ("jd" + 1)) (.pcSet 2 "jb" 0 0 0))
    (.pcSet 2 "jb" 0 0 0)

theorem fundS_agree {κ : Caps} {S : Core} {L : Loc} {j : Job} {v up src k D : Nat} (hjob : S.resJob = some j)
    (ha : L "ja" = v) (hb : L "jb" = up) (hc : L "jc" = src) (hd : L "jd" = k) (hds : DSAgree κ S src D)
    {r : Option Job} {S' : Core} (h : (fundLoop j v up src k).run S = .ok r S') :
    ∃ L' c, evalF κ fundS S L = .ok { S' with resJob := r } L' c ∧ c ≤ D + 80 := by
  unfold fundLoop at h
  simp only [OM.Proof.run_getP_bind] at h
  by_cases hk : k < S.P.s
  · rw [if_pos hk] at h
    obtain ⟨b, S1, h1, h2⟩ := run_bind_ok h
    obtain ⟨Ld, cd, ed, hdk, hcd, hj1⟩ := hds b S1 h1
    have e1 := evalF_call_ok (q := dsP) (args := [.var "jc"]) (ds := ["dk"]) (L := L) (by simp [evList, Exp.ev, hc]) ed
    set L1 := OM.Machine.State.setLocs L ["dk"] (dsP.rets.map Ld)
    have hL1 : ∀ q, q ≠ "dk" → L1 q = L q := fun q hq => by
      simp [L1, dsP, OM.Machine.State.setLocs, OM.Machine.State.upd, hq]
    have h1dk : L1 "dk" = b2n b := by simp [L1, dsP, OM.Machine.State.setLocs, OM.Machine.State.upd, hdk]
    cases b
    · simp at h2
      obtain ⟨rfl, rfl⟩ := h2
      have e2' : evalF κ (.pcSet 2 "jb" 0 0 0) S1 L1 = .ok { S1 with resJob := some { j with pc := .walk (some up) } } L1 21 := by
        simp [evalF, evList, Exp.ev, hj1, hjob, hL1 "jb" (by decide), hb, pcDec, costList, Exp.cost]
      have e2 := evalF_ite_f (c := .var "dk") (t := .pcSet 4 "ja" "jb" "jc" ("jd" + 1)) (by simp [Exp.ev, h1dk, b2n]) e2'
      refine ⟨_, _, evalF_ite_t (v := 1) (by simp [Exp.ev, hd, OM.Machine.BinOp.eval, PF.get, hk]) one_ne_zero
        (evalF_seq_ok2 e1 e2), ?_⟩
      simp [Exp.cost, costList]; omega
    · simp at h2
      obtain ⟨rfl, rfl⟩ := h2
      have e2' : evalF κ (.pcSet 4 "ja" "jb" "jc" ("jd" + 1)) S1 L1 =
          .ok { S1 with resJob := some { j with pc := .fund v up src (k + 1) } } L1 23 := by
        simp [evalF, evList, Exp.ev, hj1, hjob, hL1 "ja" (by decide), hL1 "jb" (by decide), hL1 "jc" (by decide),
          hL1 "jd" (by decide), ha, hb, hc, hd, pcDec, OM.Machine.BinOp.eval, costList, Exp.cost]
      have e2 := evalF_ite_t (c := .var "dk") (f := .pcSet 2 "jb" 0 0 0) (v := 1) (by simp [Exp.ev, h1dk, b2n]) one_ne_zero e2'
      refine ⟨_, _, evalF_ite_t (v := 1) (by simp [Exp.ev, hd, OM.Machine.BinOp.eval, PF.get, hk]) one_ne_zero
        (evalF_seq_ok2 e1 e2), ?_⟩
      simp [Exp.cost, costList]; omega
  · rw [if_neg hk] at h
    simp at h
    obtain ⟨rfl, rfl⟩ := h
    have e' : evalF κ (.pcSet 2 "jb" 0 0 0) S L = .ok { S with resJob := some { j with pc := .walk (some up) } } L 21 := by
      simp [evalF, evList, Exp.ev, hjob, hb, pcDec, costList, Exp.cost]
    refine ⟨_, _, evalF_ite_f (by simp [Exp.ev, hd, OM.Machine.BinOp.eval, PF.get, hk]) e', ?_⟩
    simp [Exp.cost]

/-- `afterDrain` (locals `av au` = `v up`). -/
def afSetS : Stm := "ja" ::= .var "av" ;; "jb" ::= .var "au" ;; "jc" ::= .var "src" ;; "jd" ::= 0
def afterDS : Stm := "src" ::= .rd (.n .overflow) "av" ;; .ite ("src" =ₑ 0) (.pcSet 2 "au" 0 0 0) (afSetS ;; fundS)

theorem afterDS_agree {κ : Caps} {S : Core} {L : Loc} {j : Job} {v up D : Nat} (hjob : S.resJob = some j)
    (hv : L "av" = v) (hu : L "au" = up) (hvN : v < κ.tbl .N)
    (hds : DSAgree κ S (S.nodes.getX v).overflowOf D)
    {r : Option Job} {S' : Core} (h : (afterDrain j v up).run S = .ok r S') :
    ∃ L' c, evalF κ afterDS S L = .ok { S' with resJob := r } L' c ∧ c ≤ D + 120 := by
  unfold afterDrain at h
  simp only [run_getN_bind] at h
  set src := (S.nodes.getX v).overflowOf
  have a1 := evalF_assign_ok (κ := κ) (s := S) (L := L) (x := "src") (e := .rd (.n .overflow) "av") (v := src)
    (by simp [Exp.ev, hv, hvN, Fld.cap, Fld.get, NF.get, src])
  set L1 := upd L "src" src
  by_cases h0 : src = 0
  · rw [if_neg (by simp [h0, NIL])] at h
    simp at h
    obtain ⟨rfl, rfl⟩ := h
    have e' : evalF κ (.pcSet 2 "au" 0 0 0) S L1 = .ok { S with resJob := some { j with pc := .walk (some up) } } L1 21 := by
      simp [evalF, evList, Exp.ev, hjob, L1, OM.Machine.State.upd, hu, pcDec, costList, Exp.cost]
    refine ⟨_, _, evalF_seq_ok2 a1 (evalF_ite_t (v := 1) (by simp [Exp.ev, L1, OM.Machine.State.upd, h0,
      OM.Machine.BinOp.eval]) one_ne_zero e'), by simp [Exp.cost]⟩
  · rw [if_pos (by simpa [NIL] using h0)] at h
    set L2 := upd (upd (upd (upd L1 "ja" v) "jb" up) "jc" src) "jd" 0
    have e2 : evalF κ afSetS S L1 = .ok S L2 8 := by
      have b1 := evalF_assign_ok (κ := κ) (s := S) (L := L1) (x := "ja") (e := .var "av") (v := v)
        (by simp [Exp.ev, L1, OM.Machine.State.upd, hv])
      have b2 := evalF_assign_ok (κ := κ) (s := S) (L := upd L1 "ja" v) (x := "jb") (e := .var "au") (v := up)
        (by simp [Exp.ev, L1, OM.Machine.State.upd, hu])
      have b3 := evalF_assign_ok (κ := κ) (s := S) (L := upd (upd L1 "ja" v) "jb" up) (x := "jc") (e := .var "src")
        (v := src) (by simp [Exp.ev, L1, OM.Machine.State.upd])
      have b4 := evalF_assign_ok (κ := κ) (s := S) (L := upd (upd (upd L1 "ja" v) "jb" up) "jc" src) (x := "jd")
        (e := (0 : Exp)) (v := 0) rfl
      exact evalF_seq_ok2 b1 (evalF_seq_ok2 b2 (evalF_seq_ok2 b3 b4))
    obtain ⟨L3, c3, e3, hc3⟩ := fundS_agree (κ := κ) (S := S) (L := L2) (j := j) (v := v) (up := up) (src := src) (k := 0)
      (D := D) hjob (by simp [L2, OM.Machine.State.upd]) (by simp [L2, OM.Machine.State.upd])
      (by simp [L2, OM.Machine.State.upd]) (by simp [L2, OM.Machine.State.upd]) hds h
    have hc : ("src" =ₑ 0 : Exp).ev κ S L1 = some 0 := by
      simp [Exp.ev, L1, OM.Machine.State.upd, h0, OM.Machine.BinOp.eval]
    have e4 := evalF_ite_f (t := .pcSet 2 "au" 0 0 0) hc (evalF_seq_ok2 e2 e3)
    exact ⟨_, _, evalF_seq_ok2 a1 e4, by simp [Exp.cost]; omega⟩

/-- `startDrain v`. -/
def sdP : Proc where
  name := "startDrain"
  params := ["v"]
  rets := []
  body := startDrainS

/-- The program agrees with Level F's `startDrain v` from `S` (within `D` steps). -/
def SDAgree (κ : Caps) (S : Core) (v D : Nat) : Prop :=
  ∀ S', (startDrain v).run S = .ok () S' →
    ∃ L' c, evalF κ sdP.body S (OM.Machine.State.setLocs (fun _ => 0) ["v"] [v]) = .ok S' L' c ∧ c ≤ D ∧
      S'.resJob = S.resJob

/-- `pw := a ^ ht`. -/
def powS : Stm := "pw" ::= 1 ;; .loop "i" "ht" ("pw" ::= "pw" * .prm .a)

theorem foldl_mul_pow (a : Nat) : ∀ n, (List.range n).foldl (fun acc _ => acc * a) 1 = a ^ n
  | 0 => rfl
  | n + 1 => by rw [List.range_succ, List.foldl_append, foldl_mul_pow a n]; simp [pow_succ]

theorem powS_ok {κ : Caps} {S : Core} {L : Loc} {h : Nat} (hh : L "ht" = h) :
    ∃ L' c, evalF κ powS S L = .ok S L' c ∧ L' "pw" = S.P.a ^ h ∧ c ≤ 10 + 7 * h ∧
      ∀ r, r ≠ "pw" → r ≠ "i" → L' r = L r := by
  have a1 := evalF_assign_ok (κ := κ) (s := S) (L := L) (x := "pw") (e := (1 : Exp)) (v := 1) rfl
  obtain ⟨L', c, he, hc, hF, ha⟩ := evalF_loop_pure (κ := κ) (x := "i") (n := .var "ht") (b := "pw" ::= "pw" * .prm .a)
    (s := S) (L := upd L "pw" 1) (N := h) (by simp [Exp.ev, OM.Machine.State.upd, hh])
    (fun L' => ∀ r, r ≠ "pw" → r ≠ "i" → L' r = L r) (fun L' => L' "pw") (fun acc _ => acc * S.P.a) 6
    (fun r h1 _ => by simp [OM.Machine.State.upd, h1])
    (by
      intro k _ L1 hF1
      refine ⟨_, _, evalF_assign_ok (v := L1 "pw" * S.P.a) (by simp [Exp.ev, OM.Machine.State.upd,
        OM.Machine.BinOp.eval, PF.get]), by simp [Exp.cost], fun r h1 h2 => ?_, by simp [OM.Machine.State.upd]⟩
      simp [OM.Machine.State.upd, h1, h2]; exact hF1 r h1 h2)
  simp only [OM.Machine.State.upd, if_true] at ha
  rw [foldl_mul_pow] at ha
  refine ⟨L', _, evalF_seq_ok2 a1 he, ha, ?_, hF⟩
  simp [Exp.cost] at hc ⊢; omega

def walkC : Exp := (!ₑ ("up" =ₑ 0)) &&ₑ ((!ₑ "dr") &&ₑ (("ov" =ₑ 0) &&ₑ (2 * "pw" <ₑ "wt" + 2)))
def walkRd : Stm :=
  "up" ::= .rd (.n .livePar) "wv" ;; "wt" ::= .rd (.n .weight) "wv" ;; "ht" ::= .rd (.n .height) "wv" ;;
  "dr" ::= .rd (.n .draining) "wv" ;; "ov" ::= .rd (.n .overflow) "wv"
/-- `walkBody` at node `wv`. -/
def walkS : Stm :=
  .ite ("wv" =ₑ 0) .jobClear
    (walkRd ;; .wr (.n .weight) "wv" ("wt" + 2) ;; powS ;;
     .ite walkC (sdP.call [.var "wv"] [] ;; .pcSet 3 "wv" "up" 0 0) ("av" ::= .var "wv" ;; "au" ::= .var "up" ;; afterDS))

theorem walkS_agree {κ : Caps} {S : Core} {L : Loc} {j : Job} {v D1 D2 : Nat} (hjob : S.resJob = some j)
    (hv : L "wv" = v) (hvs : v ≠ 0 → v < S.nodes.size) (hvN : v ≠ 0 → v < κ.tbl .N)
    (hsd : SDAgree κ (wiC S v) v D1) (hds : DSAgree κ (wiC S v) (S.nodes.getX v).overflowOf D2)
    {r : Option Job} {S' : Core} (h : (walkBody j v).run S = .ok r S') :
    ∃ L' c, evalF κ walkS S L = .ok { S' with resJob := r } L' c ∧
      c ≤ D1 + D2 + 250 + 7 * (S.nodes.getX v).height := by
  unfold walkBody at h
  by_cases h0 : v = 0
  · rw [if_pos (by simp [h0, NIL])] at h
    simp at h
    obtain ⟨rfl, rfl⟩ := h
    exact ⟨_, _, evalF_ite_t (v := 1) (by simp [Exp.ev, hv, h0, OM.Machine.BinOp.eval]) one_ne_zero
      (show evalF κ .jobClear S L = .ok { S with resJob := none } L 27 from rfl), by simp [Exp.cost]; omega⟩
  · rw [if_neg (by simpa [NIL] using h0)] at h
    simp only [OM.Proof.run_getP_bind, run_getN_bind, run_modN_bind] at h
    have hvs' := hvs h0
    have hvN' := hvN h0
    set V := S.nodes.getX v
    -- the reads
    set L5 := upd (upd (upd (upd (upd L "up" V.livePar) "wt" V.weight) "ht" V.height) "dr" (b2n V.draining)) "ov"
      V.overflowOf
    have e1 : evalF κ walkRd S L = .ok S L5 15 := by
      have b1 := evalF_assign_ok (κ := κ) (s := S) (L := L) (x := "up") (e := .rd (.n .livePar) "wv") (v := V.livePar)
        (by simp [Exp.ev, hv, hvN', Fld.cap, Fld.get, NF.get, V])
      have b2 := evalF_assign_ok (κ := κ) (s := S) (L := upd L "up" V.livePar) (x := "wt") (e := .rd (.n .weight) "wv")
        (v := V.weight) (by simp [Exp.ev, OM.Machine.State.upd, hv, hvN', Fld.cap, Fld.get, NF.get, V])
      have b3 := evalF_assign_ok (κ := κ) (s := S) (L := upd (upd L "up" V.livePar) "wt" V.weight) (x := "ht")
        (e := .rd (.n .height) "wv") (v := V.height)
        (by simp [Exp.ev, OM.Machine.State.upd, hv, hvN', Fld.cap, Fld.get, NF.get, V])
      have b4 := evalF_assign_ok (κ := κ) (s := S) (L := upd (upd (upd L "up" V.livePar) "wt" V.weight) "ht" V.height)
        (x := "dr") (e := .rd (.n .draining) "wv") (v := b2n V.draining)
        (by simp [Exp.ev, OM.Machine.State.upd, hv, hvN', Fld.cap, Fld.get, NF.get, V])
      have b5 := evalF_assign_ok (κ := κ) (s := S)
        (L := upd (upd (upd (upd L "up" V.livePar) "wt" V.weight) "ht" V.height) "dr" (b2n V.draining))
        (x := "ov") (e := .rd (.n .overflow) "wv") (v := V.overflowOf)
        (by simp [Exp.ev, OM.Machine.State.upd, hv, hvN', Fld.cap, Fld.get, NF.get, V])
      exact evalF_seq_ok2 b1 (evalF_seq_ok2 b2 (evalF_seq_ok2 b3 (evalF_seq_ok2 b4 b5)))
    have h5 : ∀ r, r ≠ "up" → r ≠ "wt" → r ≠ "ht" → r ≠ "dr" → r ≠ "ov" → L5 r = L r := fun r a b c d e => by
      simp [L5, OM.Machine.State.upd, a, b, c, d, e]
    have h5v : L5 "wv" = v := by rw [h5 _ (by decide) (by decide) (by decide) (by decide) (by decide), hv]
    -- the weight
    have e2 := evalF_wrN_ok (κ := κ) (s := S) (L := L5) (k := .weight) (i := .var "wv") (e := "wt" + 2) (j := v)
      (w := V.weight + 2) (by simp [Exp.ev, h5v]) (by simp [Exp.ev, L5, OM.Machine.State.upd, OM.Machine.BinOp.eval])
      hvs' hvN' rfl
    have hW : ({ S with nodes := S.nodes.modify v (NF.set · (V.weight + 2) .weight) } : Core) = wiC S v := by
      simp only [wiC]; congr 1; apply Array.modify_congr_getX; rfl
    rw [hW] at e2
    obtain ⟨L6, c6, e6, h6pw, hc6, hF6⟩ := powS_ok (κ := κ) (S := wiC S v) (L := L5) (h := V.height)
      (by simp [L5, OM.Machine.State.upd])
    have h6 : ∀ r, r ≠ "pw" → r ≠ "i" → L6 r = L5 r := hF6
    have hjob' : (wiC S v).resJob = some j := hjob
    by_cases hc : V.livePar != NIL && !V.draining && V.overflowOf == NIL && decide (V.weight + 2 > 2 * S.P.a ^ V.height)
    · rw [if_pos hc] at h
      obtain ⟨u, S1, h1, h2⟩ := run_bind_ok h
      simp at h2
      obtain ⟨rfl, rfl⟩ := h2
      obtain ⟨Ls, cs, es, hcs, hjs⟩ := hsd S1 h1
      have e7 := evalF_call_ok (q := sdP) (args := [.var "wv"]) (ds := []) (L := L6)
        (by simp [evList, Exp.ev, h6 "wv" (by decide) (by decide), h5v]) es
      have e8 : evalF κ (.pcSet 3 "wv" "up" 0 0) S1 (OM.Machine.State.setLocs L6 [] (sdP.rets.map Ls)) =
          .ok { S1 with resJob := some { j with pc := .afterDrain v V.livePar } } L6 21 := by
        simp [evalF, evList, Exp.ev, hjs, hjob', OM.Machine.State.setLocs, h6 "wv" (by decide) (by decide), h5v,
          h6 "up" (by decide) (by decide), L5, OM.Machine.State.upd, pcDec, costList, Exp.cost]
      have hcv : walkC.ev κ (wiC S v) L6 = some 1 := by
        simp only [Bool.and_eq_true, bne_iff_ne, ne_eq, Bool.not_eq_eq_eq_not, Bool.not_true, beq_iff_eq,
          decide_eq_true_eq] at hc
        obtain ⟨⟨⟨hc1, hc2⟩, hc3⟩, hc4⟩ := hc
        simp [walkC, Exp.ev, OM.Machine.BinOp.eval, OM.Machine.UnOp.eval, h6pw, h6 "up" (by decide) (by decide),
          h6 "dr" (by decide) (by decide), h6 "ov" (by decide) (by decide), h6 "wt" (by decide) (by decide), L5,
          OM.Machine.State.upd, b2n, hc2, hc3, NIL] at hc1 ⊢
        exact ⟨hc1, hc4⟩
      refine ⟨_, _, evalF_ite_f (by simp [Exp.ev, hv, h0, OM.Machine.BinOp.eval]) (evalF_seq_ok2 e1 (evalF_seq_ok2 e2
        (evalF_seq_ok2 e6 (evalF_ite_t hcv one_ne_zero (evalF_seq_ok2 e7 e8))))), ?_⟩
      simp [Exp.cost, costList, walkC] at hc6 ⊢
      omega
    · rw [if_neg hc] at h
      have hcv : walkC.ev κ (wiC S v) L6 = some 0 := by
        simp only [Bool.and_eq_true, bne_iff_ne, ne_eq, Bool.not_eq_eq_eq_not, Bool.not_true, beq_iff_eq,
          decide_eq_true_eq, not_and] at hc
        simp [walkC, Exp.ev, OM.Machine.BinOp.eval, OM.Machine.UnOp.eval, h6pw, h6 "up" (by decide) (by decide),
          h6 "dr" (by decide) (by decide), h6 "ov" (by decide) (by decide), h6 "wt" (by decide) (by decide), L5,
          OM.Machine.State.upd, b2n, NIL]
        intro a b c
        have := hc ⟨⟨a, b⟩, c⟩
        show V.weight + 2 ≤ 2 * S.P.a ^ V.height
        omega
      have hov : ((wiC S v).nodes.getX v).overflowOf = V.overflowOf := by
        simp only [wiC, getX_modify', hvs', and_self, if_true]; rfl
      set L7 := upd (upd L6 "av" v) "au" V.livePar
      have b1 := evalF_assign_ok (κ := κ) (s := wiC S v) (L := L6) (x := "av") (e := .var "wv") (v := v)
        (by simp [Exp.ev, h6 "wv" (by decide) (by decide), h5v])
      have b2 := evalF_assign_ok (κ := κ) (s := wiC S v) (L := upd L6 "av" v) (x := "au") (e := .var "up")
        (v := V.livePar) (by simp [Exp.ev, OM.Machine.State.upd, h6 "up" (by decide) (by decide), L5])
      obtain ⟨L8, c8, e8, hc8⟩ := afterDS_agree (κ := κ) (S := wiC S v) (L := L7) (j := j) (v := v) (up := V.livePar)
        (D := D2) hjob' (by simp [L7, OM.Machine.State.upd]) (by simp [L7, OM.Machine.State.upd]) hvN'
        (by rw [hov]; exact hds) h
      exact ⟨_, _, evalF_ite_f (by simp [Exp.ev, hv, h0, OM.Machine.BinOp.eval]) (evalF_seq_ok2 e1 (evalF_seq_ok2 e2
        (evalF_seq_ok2 e6 (evalF_ite_f hcv (evalF_seq_ok2 b1 (evalF_seq_ok2 b2 e8)))))),
        by simp [Exp.cost, walkC] at hc6 ⊢; omega⟩

end OM.Impl
