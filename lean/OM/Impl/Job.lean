import OM.Impl.Reserve
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

end OM.Impl
