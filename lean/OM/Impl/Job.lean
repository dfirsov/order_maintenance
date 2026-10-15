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

end OM.Impl
