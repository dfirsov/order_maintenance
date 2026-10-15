import OM.Impl.Side

/-!
# M6: the tables of the top structure (`roomNextTo`, `tableInsert`)
-/

namespace OM.Impl

open OM.Model
open OM.Machine (Reg BinOp UnOp)

local notation "upd" => OM.Machine.State.upd

theorem findIdx?_some_iff' {l : List (Nat × Nat)} {x i : Nat} :
    l.findIdx? (·.1 == x) = some i ↔ l.findIdx (·.1 == x) = i ∧ i < l.length := by
  rw [List.findIdx?_eq_some_iff_findIdx_eq, and_comm]

theorem run_modN (t : Nat) (f : Node → Node) (σ : Core) :
    (modN t f).run σ = .ok () { σ with nodes := σ.nodes.modify t f } := rfl

theorem put_table_side (σ : Core) (t : Nat) (tbl : List (Nat × Nat)) (sd : List (Nat × Side)) :
    LK.put (LK.put σ t tbl .table) t (encS sd) .side =
      { σ with nodes := σ.nodes.modify t fun n => { n with table := tbl, side := sd } } := by
  simp [LK.put, Array.modify_modify_same, encS, List.map_map, Function.comp_def, sideOfN_sideN]

theorem put_table (σ : Core) (t : Nat) (tbl : List (Nat × Nat)) :
    LK.put σ t tbl .table =
      { σ with nodes := σ.nodes.modify t fun n => { n with table := tbl, side := (σ.nodes.getX t).side } } := by
  simp only [LK.put]
  congr 1
  apply Array.modify_congr_getX
  rfl

/-- `tableInsert t e w before lab` (`bf` = 1 for `before`). -/
def tableInsertP : Proc where
  name := "tableInsert"
  params := ["t", "e", "w", "bf", "lab"]
  rets := []
  body :=
    (findP .table).call [.var "t", .var "e"] ["r"] ;;
    "n" ::= .llen .table "t" ;;
    .ite ("r" <ₑ "n") .skip .fail ;;
    "p" ::= "r" + (1 - "bf") ;;
    (insertIdxP .table).call [.var "t", .var "p", .var "w", .var "lab"] [] ;;
    .ite (.rd (.n .draining) "t")
      ((lookupP .side).call [.var "t", .var "e"] ["f", "x"] ;;
       .ite "f" ((assocSetP .side).call [.var "t", .var "w", .var "x"] []) .fail)
      .skip

theorem getX_size_le {α : Type} [Inhabited α] {a : Array α} {i : Nat} (h : a.size ≤ i) : a.getX i = default := by
  simp [Array.getX, Array.getD, show ¬i < a.size by omega]

/-- **`tableInsertP` runs `tableInsert`.** -/
theorem tableInsertP_agree (κ : Caps) (σ : Core) (L : Loc) {t e w lab : Nat} {before : Bool} (ht : L "t" = t)
    (he : L "e" = e) (hw : L "w" = w) (hbf : L "bf" = b2n before) (hl : L "lab" = lab)
    (htr : t < κ.lrec .table) (hts : t < κ.lrec .side) (htN : t < κ.tbl .N)
    (hcapT : (σ.nodes.getX t).table.length + 1 ≤ κ.lcap .table)
    (hcapS : (σ.nodes.getX t).side.length + 1 ≤ κ.lcap .side) {σ' : Core}
    (h : (tableInsert t e w before lab).run σ = .ok () σ') :
    ∃ L' c, evalF κ tableInsertP.body σ L = .ok σ' L' c ∧
      c ≤ 250 + 120 * (σ.nodes.getX t).table.length + 50 * (σ.nodes.getX t).side.length := by
  unfold tableInsert at h
  simp [getN] at h
  set T := σ.nodes.getX t with hT
  have hsome : ∃ i, T.table.findIdx? (·.1 == e) = some i := by
    cases hfi : T.table.findIdx? (·.1 == e) with
    | none => simp [T, hfi, OM.Model.guard] at h
    | some i => exact ⟨i, rfl⟩
  obtain ⟨i, hfi⟩ := hsome
  simp only [hfi] at h
  obtain ⟨hfi1, hil⟩ := findIdx?_some_iff'.mp hfi
  have htsz : t < σ.nodes.size := by
    by_contra hc
    have hd : T = default := getX_size_le (by omega)
    rw [hd, show (default : Node).table = [] from rfl] at hil
    simp at hil
  set tbl' := T.table.insertIdx (if before = true then i else i + 1) (w, lab)
  -- the common prefix: find, guard, position, insertion
  obtain ⟨Lf, cf, ef, hrf, hcf⟩ := findP_agree κ .table σ
    (OM.Machine.State.setLocs (fun _ => 0) ["i", "x"] [t, e]) (i := t) (x := e)
    (by simp [OM.Machine.State.setLocs, OM.Machine.State.upd])
    (by simp [OM.Machine.State.setLocs, OM.Machine.State.upd]) htr
  have e1 := evalF_call_ok (q := findP .table) (args := [.var "t", .var "e"]) (ds := ["r"]) (L := L)
    (by simp [evList, Exp.ev, ht, he]) ef
  set L1 := OM.Machine.State.setLocs L ["r"] ((findP .table).rets.map Lf)
  have hL1 : ∀ r, r ≠ "r" → L1 r = L r := fun r h => by
    simp [L1, findP, OM.Machine.State.setLocs, OM.Machine.State.upd, h]
  have hr1 : L1 "r" = i := by
    simp [L1, findP, OM.Machine.State.setLocs, OM.Machine.State.upd, hrf, LK.view, T]; exact hfi1
  have e2 := evalF_assign_ok (κ := κ) (s := σ) (L := L1) (x := "n") (e := .llen .table "t") (v := T.table.length)
    (by simp [Exp.ev, hL1 "t" (by decide), ht, htr, LK.view, T])
  set L2 := upd L1 "n" T.table.length
  have e3 := evalF_ite_t (κ := κ) (s := σ) (L := L2) (c := "r" <ₑ "n") (t := .skip) (f := .fail) (v := 1)
    (by simp [Exp.ev, OM.Machine.BinOp.eval, L2, OM.Machine.State.upd, hr1, T, hil]) one_ne_zero evalF_skip
  set pos := if before = true then i else i + 1
  have hb1 : b2n before ≤ 1 := by cases before <;> simp [b2n]
  have e4 := evalF_assign_ok (κ := κ) (s := σ) (L := L2) (x := "p") (e := "r" + (1 - "bf")) (v := pos)
    (by
      have hbf2 : L2 "bf" = b2n before := by
        simp [L2, OM.Machine.State.upd]; rw [hL1 "bf" (by decide), hbf]
      simp only [Exp.ev, Exp.add_def, Exp.sub_def, Exp.ofNat_def, hbf2, OM.Machine.BinOp.eval,
        show L2 "r" = i by simp [L2, OM.Machine.State.upd, hr1], Option.bind_some, if_pos hb1]
      cases before <;> simp [pos, b2n])
  set L3 := upd L2 "p" pos
  have hL3 : ∀ r, r ≠ "r" → r ≠ "n" → r ≠ "p" → L3 r = L r := fun r h1 h2 h3 => by
    simp only [L3, L2, OM.Machine.State.upd, if_neg h2, if_neg h3]; exact hL1 r h1
  obtain ⟨Li, ci, ei, hci⟩ := insertIdxP_agree κ .table σ
    (OM.Machine.State.setLocs (fun _ => 0) ["i", "p", "a", "b"] [t, pos, w, lab]) (i := t) (p := pos) (a := w)
    (b := lab) (by simp [OM.Machine.State.setLocs, OM.Machine.State.upd])
    (by simp [OM.Machine.State.setLocs, OM.Machine.State.upd])
    (by simp [OM.Machine.State.setLocs, OM.Machine.State.upd])
    (by simp [OM.Machine.State.setLocs, OM.Machine.State.upd]) (by simp [LK.recOk, htsz]) htr
    (by simp [LK.valid]) (by show pos ≤ T.table.length; simp only [pos]; split <;> omega) (by simp [LK.view]; exact hcapT)
  have e5 := evalF_call_ok (q := insertIdxP .table) (args := [.var "t", .var "p", .var "w", .var "lab"]) (ds := [])
    (L := L3) (by
      have h1 : L3 "p" = pos := by simp [L3, OM.Machine.State.upd]
      simp [evList, Exp.ev, hL3 "t" (by decide) (by decide) (by decide), ht,
        hL3 "w" (by decide) (by decide) (by decide), hw, hL3 "lab" (by decide) (by decide) (by decide), hl, h1]) ei
  simp only [LK.view] at e5
  set S5 := LK.put σ t tbl' .table
  set L5 := OM.Machine.State.setLocs L3 [] ((insertIdxP .table).rets.map Li)
  have hL5 : ∀ r, r ≠ "r" → r ≠ "n" → r ≠ "p" → L5 r = L r := fun r h1 h2 h3 => hL3 r h1 h2 h3
  have hdr : (S5.nodes.getX t).draining = T.draining := by
    simp only [S5, LK.put, OM.Proof.Top.getX_modify', htsz, and_self, if_true, T]
  have hview : LK.view S5 t .side = encS T.side := by
    rw [LK.view_put (by simp [LK.recOk, htsz]) (by simp [LK.valid])]; simp [LK.view, T]
  by_cases hd : T.draining = true
  · simp only [hd, if_true] at h
    have hlk : ∃ sd, lookup T.side e = some sd := by
      cases hl : lookup T.side e with
      | none => simp [hl, OM.Model.guard] at h
      | some sd => exact ⟨sd, rfl⟩
    obtain ⟨sd, hlk⟩ := hlk
    simp only [hlk] at h
    simp [modN] at h
    subst h
    obtain ⟨Lk, ck, ek, hfk, hvk, -, -, hck⟩ := lookupP_agree κ .side S5
      (OM.Machine.State.setLocs (fun _ => 0) ["i", "x"] [t, e]) (i := t) (x := e)
      (by simp [OM.Machine.State.setLocs, OM.Machine.State.upd])
      (by simp [OM.Machine.State.setLocs, OM.Machine.State.upd]) hts
    rw [hview, lookup_encS, hlk] at hfk hvk
    rw [hview] at hck
    have e6 := evalF_call_ok (q := lookupP .side) (args := [.var "t", .var "e"]) (ds := ["f", "x"]) (L := L5)
      (by simp [evList, Exp.ev, hL5 "t" (by decide) (by decide) (by decide), ht,
        hL5 "e" (by decide) (by decide) (by decide), he]) ek
    set L6 := OM.Machine.State.setLocs L5 ["f", "x"] ((lookupP .side).rets.map Lk)
    obtain ⟨La, ca, ea, hca⟩ := assocSetP_agree κ .side S5
      (OM.Machine.State.setLocs (fun _ => 0) ["i", "x", "y"] [t, w, sideN sd]) (i := t) (x := w) (y := sideN sd)
      (by simp [OM.Machine.State.setLocs, OM.Machine.State.upd])
      (by simp [OM.Machine.State.setLocs, OM.Machine.State.upd])
      (by simp [OM.Machine.State.setLocs, OM.Machine.State.upd])
      (by simp [S5, LK.idOk, LK.recOk, htsz]) (by simp [S5, LK.recOk, htsz]) hts
      (fun a => by simp [LK.valid, sideN_le]) (by
        rw [hview]
        have := length_assocSet_le' (encS T.side) w (sideN sd)
        simp only [encS, List.length_map] at this ⊢; omega)
    rw [hview, assocSet_encS] at ea
    rw [hview] at hca
    have e7 := evalF_call_ok (q := assocSetP .side) (args := [.var "t", .var "w", .var "x"]) (ds := [])
      (L := L6) (by
        simp [evList, Exp.ev, L6, lookupP, OM.Machine.State.setLocs, OM.Machine.State.upd, hvk,
          hL5 "t" (by decide) (by decide) (by decide), ht, hL5 "w" (by decide) (by decide) (by decide), hw]) ea
    rw [put_table_side] at e7
    have e8 := evalF_ite_t (κ := κ) (c := .var "f") (f := .fail) (v := 1)
      (by simp [Exp.ev, L6, lookupP, OM.Machine.State.setLocs, OM.Machine.State.upd, hfk]) one_ne_zero e7
    have e9 := evalF_ite_t (κ := κ) (s := S5) (L := L5) (c := .rd (.n .draining) "t") (f := .skip) (v := 1)
      (by simp [Exp.ev, hL5 "t" (by decide) (by decide) (by decide), ht, htN, Fld.cap, Fld.get, NF.get, hdr, hd,
        b2n]) one_ne_zero (evalF_seq_ok2 e6 e8)
    refine ⟨_, _, evalF_seq_ok2 e1 (evalF_seq_ok2 e2 (evalF_seq_ok2 e3 (evalF_seq_ok2 e4 (evalF_seq_ok2 e5 e9)))),
      ?_⟩
    simp only [LK.view, List.length_map] at hcf hci hck hca
    simp only [Exp.cost, costList, List.map, List.sum_cons, List.sum_nil, List.length_cons, List.length_nil,
      Exp.add_def, Exp.sub_def, Exp.ofNat_def] at hcf hci hck hca ⊢
    have : (σ.nodes.getX t).table.length = T.table.length := rfl
    have : (σ.nodes.getX t).side.length = T.side.length := rfl
    omega
  · have hd' : T.draining = false := by simpa using hd
    simp only [hd', Bool.false_eq_true, if_false] at h
    simp [modN] at h
    subst h
    have e9 := evalF_ite_f (κ := κ) (s := S5) (L := L5) (c := .rd (.n .draining) "t")
      (t := (lookupP .side).call [.var "t", .var "e"] ["f", "x"] ;;
        .ite "f" ((assocSetP .side).call [.var "t", .var "w", .var "x"] []) .fail)
      (by simp [Exp.ev, hL5 "t" (by decide) (by decide) (by decide), ht, htN, Fld.cap, Fld.get, NF.get, hdr, hd',
        b2n]) evalF_skip
    have e9' := e9.trans (congrArg (fun x => Res.ok x L5 _) (put_table σ t tbl'))
    refine ⟨_, _, evalF_seq_ok2 e1 (evalF_seq_ok2 e2 (evalF_seq_ok2 e3 (evalF_seq_ok2 e4 (evalF_seq_ok2 e5 e9')))),
      ?_⟩
    simp only [LK.view, List.length_map] at hcf hci
    simp only [Exp.cost, costList, List.map, List.sum_cons, List.sum_nil, List.length_cons, List.length_nil,
      Exp.add_def, Exp.sub_def, Exp.ofNat_def] at hcf hci ⊢
    have : (σ.nodes.getX t).table.length = T.table.length := rfl
    omega

end OM.Impl
