import OM.Impl.Cut
import OM.Impl.TopTab
import OM.Proof.Top.RunStart

/-!
# M6: `startDrain` at Level M

The program builds the side list of `v` first (in place), so until its last step its state is
Level F's stage with `v`'s side list already set: `φ X = X` with `side v := side`. Every stage after
the side list touches other nodes or other fields, so it commutes with `φ`, and the last step sets
`side v := side` anyway.
-/

namespace OM.Impl

open OM.Model
open OM.Proof.Top
open OM.Machine (Reg BinOp UnOp)

local notation "upd" => OM.Machine.State.upd

/-- Level F's state with `v`'s side list already set. -/
def phiS (v : Nat) (side : List (Nat × Side)) (X : Core) : Core :=
  { X with nodes := X.nodes.modify v fun n => { n with side := side } }

theorem put_side_phi (X : Core) (v : Nat) (side : List (Nat × Side)) :
    LK.put X v (encS side) .side = phiS v side X := put_side_encS X v side

theorem Array.modify_push_lt {α : Type} (a : Array α) (x : α) (f : α → α) {i : Nat} (hi : i < a.size) :
    (a.modify i f).push x = (a.push x).modify i f := by
  apply Array.ext
  · simp
  · intro j h1 h2
    simp only [Array.getElem_modify, Array.getElem_push]
    simp only [Array.size_push, Array.size_modify] at h1
    by_cases e : j = a.size
    · subst e; simp [show i ≠ a.size by omega]
    · have : j < a.size := by omega
      simp [this, Array.getElem_modify]

/-! ### Steps -/

theorem evalF_pushN_ok {κ : Caps} {s : Core} {L : Loc} {x : Reg} (h : s.nodes.size < κ.tbl .N) :
    evalF κ (.push .N x) s L = .ok { s with nodes := s.nodes.push default } (upd L x s.nodes.size) pushCost := by
  simp [evalF, Tbl.size, Tbl.push, h]

theorem evalF_wrN_ok {κ : Caps} {s : Core} {L : Loc} {k : NF} {i e : Exp} {j w : Nat} (hi : i.ev κ s L = some j)
    (he : e.ev κ s L = some w) (hj : j < s.nodes.size) (hc : j < κ.tbl .N) (hk : k.ok w = true) :
    evalF κ (.wr (.n k) i e) s L = .ok { s with nodes := s.nodes.modify j (NF.set · w k) } L (1 + i.cost + e.cost) := by
  simp [evalF, hi, he, Fld.set, hj, hk]

/-! ### Stage 1: the two new nodes -/

def newNodesS : Stm :=
  .push .N "v1" ;; .wr (.n .height) "v1" "h" ;; .push .N "v2" ;; .wr (.n .height) "v2" "h"

theorem newNodesS_ok {κ : Caps} {t : Core} {L : Loc} {v : Nat} {side : List (Nat × Side)}
    (hh : L "h" = sH t v) (hv : v < t.nodes.size) (hcap : t.nodes.size + 2 ≤ κ.tbl .N) :
    ∃ L', evalF κ newNodesS (phiS v side t) L = .ok (phiS v side (sd1 t v)) L' (2 * pushCost + 6) ∧
      L' "v1" = t.nodes.size ∧ L' "v2" = t.nodes.size + 1 ∧
      ∀ r, r ≠ "v1" → r ≠ "v2" → L' r = L r := by
  set N := t.nodes.size
  set S0 := phiS v side t
  have hs : S0.nodes.size = N := by simp [S0, phiS, N]
  have e1 := evalF_pushN_ok (κ := κ) (s := S0) (L := L) (x := "v1") (by omega)
  rw [hs] at e1
  set S1 := { S0 with nodes := S0.nodes.push default }
  set L1 := upd L "v1" N
  have e2 := evalF_wrN_ok (κ := κ) (s := S1) (L := L1) (k := .height) (i := .var "v1") (e := .var "h") (j := N)
    (w := sH t v) (by simp [Exp.ev, L1, OM.Machine.State.upd]) (by simp [Exp.ev, L1, OM.Machine.State.upd, hh])
    (by simp [S1, hs]) (by omega) rfl
  set S2 := { S1 with nodes := S1.nodes.modify N (NF.set · (sH t v) .height) }
  have hs2 : S2.nodes.size = N + 1 := by simp [S2, S1, hs]
  have e3 := evalF_pushN_ok (κ := κ) (s := S2) (L := L1) (x := "v2") (by omega)
  rw [hs2] at e3
  set S3 := { S2 with nodes := S2.nodes.push default }
  set L3 := upd L1 "v2" (N + 1)
  have e4 := evalF_wrN_ok (κ := κ) (s := S3) (L := L3) (k := .height) (i := .var "v2") (e := .var "h")
    (j := N + 1) (w := sH t v) (by simp [Exp.ev, L3, OM.Machine.State.upd])
    (by simp [Exp.ev, L3, L1, OM.Machine.State.upd, hh]) (by simp [S3, hs2]) (by omega) rfl
  refine ⟨L3, ?_, by simp [L3, L1, OM.Machine.State.upd], by simp [L3, OM.Machine.State.upd],
    fun r h1 h2 => by simp [L3, L1, OM.Machine.State.upd, h1, h2]⟩
  have hfin : { S3 with nodes := S3.nodes.modify (N + 1) (NF.set · (sH t v) .height) } = phiS v side (sd1 t v) := by
    simp only [S3, S2, S1, S0, phiS, sd1]
    congr 1
    apply Array.ext_getX
    · simp
    · intro j
      have hvN : v ≠ N := by omega
      have hvN1 : v ≠ N + 1 := by omega
      simp only [getX_modify', getX_push', Array.size_push, Array.size_modify]
      rcases (show j = N + 1 ∨ j = N ∨ j < N ∨ N + 1 < j by omega) with rfl | rfl | hj | hj
      · simp [Ne.symm hvN1, N]; rfl
      · simp [Ne.symm hvN, N]; rfl
      · simp [show j ≠ N by omega, show j ≠ N + 1 by omega, N, hv, show v ≤ t.nodes.size + 1 by omega]
      · simp [show j ≠ N by omega, show j ≠ N + 1 by omega, show j ≠ v by omega, N]
  rw [← hfin]
  exact (evalF_seq_ok2 e1 (evalF_seq_ok2 e2 (evalF_seq_ok2 e3 e4))).trans (by simp [Exp.cost]; omega)

/-! ### Stage 2: `v1`, `v2` around `v` in every table holding `v` -/

theorem Array.modify_comm {α : Type} (a : Array α) {i j : Nat} (h : i ≠ j) (f g : α → α) :
    (a.modify i f).modify j g = (a.modify j g).modify i f := by
  apply Array.ext
  · simp
  · intro k h1 h2
    simp only [Array.getElem_modify]
    by_cases e1 : i = k <;> by_cases e2 : j = k <;> simp_all

theorem fold_modify_getX_notin {f : Array Node → Nat → Array Node}
    (hf : ∀ ns T u, u ≠ T → (f ns T).getX u = ns.getX u) {u : Nat} : ∀ (l : List Nat) (a : Array Node), u ∉ l →
    (l.foldl f a).getX u = a.getX u
  | [], _, _ => rfl
  | T :: l, a, hu => by
    simp only [List.foldl_cons]
    rw [fold_modify_getX_notin hf l _ (fun h => hu (List.mem_cons_of_mem _ h)),
      hf a T u (fun h => hu (by simp [h]))]

theorem fold_modify_size {f : Array Node → Nat → Array Node} (hf : ∀ ns T, (f ns T).size = ns.size) :
    ∀ (l : List Nat) (a : Array Node), (l.foldl f a).size = a.size
  | [], _ => rfl
  | T :: l, a => by simp only [List.foldl_cons]; rw [fold_modify_size hf l, hf]

/-- Level F after the insertions into the first `j` tables. -/
def aroundStep (t : Core) (v : Nat) (ns : Array Node) (T : Nat) : Array Node :=
  ns.modify T (aroundF (sd1 t v) v t.nodes.size (t.nodes.size + 1) (sF t v) T)

def sdJ (t : Core) (v j : Nat) : Core :=
  { sd1 t v with nodes := ((t.nodes.getX v).inTables.take j).foldl (aroundStep t v) (sd1 t v).nodes }

theorem sdJ_all (t : Core) (v : Nat) : sdJ t v (t.nodes.getX v).inTables.length = sd2 t v := by
  simp only [sdJ, sd2, List.take_length]; rfl

theorem sd1_getX (t : Core) (v : Nat) {u : Nat} (hu : u < t.nodes.size) : (sd1 t v).nodes.getX u = t.nodes.getX u := by
  simp only [sd1, getX_push', Array.size_push]; rw [if_neg (by omega), if_neg (by omega)]

def insBody : Stm :=
  "T" ::= .lrd .inTab false "v" "j" ;;
  roomP.call [.var "T", .var "v", 1] ["a"] ;;
  roomP.call [.var "T", .var "v", 0] ["b"] ;;
  tableInsertP.call [.var "T", .var "v", .var "v1", 1, .var "a"] [] ;;
  tableInsertP.call [.var "T", .var "v", .var "v2", 0, .var "b"] []

def insS : Stm := "m" ::= .llen .inTab "v" ;; .loop "j" "m" insBody

theorem nodup_getElem_notin_take {l : List Nat} (hnd : l.Nodup) {j : Nat} (hj : j < l.length) :
    l[j] ∉ l.take j := by
  intro h
  obtain ⟨i, hi, he⟩ := List.getElem_of_mem h
  simp only [List.length_take] at hi
  rw [List.getElem_take] at he
  have := (List.Nodup.getElem_inj_iff hnd).mp he
  omega

theorem aroundStep_getX (t : Core) (v : Nat) (ns : Array Node) (T u : Nat) (h : u ≠ T) :
    (aroundStep t v ns T).getX u = ns.getX u := by
  simp only [aroundStep, getX_modify']; rw [if_neg (fun e => h e.1)]

theorem aroundStep_size (t : Core) (v : Nat) (ns : Array Node) (T : Nat) : (aroundStep t v ns T).size = ns.size := by
  simp [aroundStep]

theorem sdJ_getX_notin {t : Core} {v j u : Nat} (hu : u ∉ (t.nodes.getX v).inTables.take j)
    (hlt : u < t.nodes.size) : (sdJ t v j).nodes.getX u = t.nodes.getX u := by
  simp only [sdJ]
  rw [fold_modify_getX_notin (aroundStep_getX t v) _ _ hu, sd1_getX t v hlt]

theorem sdJ_getX_notin' {t : Core} {v j u : Nat} (hu : u ∉ (t.nodes.getX v).inTables.take j) :
    (sdJ t v j).nodes.getX u = (sd1 t v).nodes.getX u := by
  simp only [sdJ]
  rw [fold_modify_getX_notin (aroundStep_getX t v) _ _ hu]

theorem sdJ_size (t : Core) (v j : Nat) : (sdJ t v j).nodes.size = t.nodes.size + 2 := by
  simp only [sdJ]; rw [fold_modify_size (aroundStep_size t v)]; simp [sd1]

theorem sdJ_succ (t : Core) (v j : Nat) (hj : j < (t.nodes.getX v).inTables.length) :
    (sdJ t v (j + 1)).nodes = aroundStep t v (sdJ t v j).nodes (t.nodes.getX v).inTables[j] := by
  simp only [sdJ]
  rw [List.take_succ_eq_append_getElem hj, List.foldl_append]; rfl

theorem phiS_getX_ne {v u : Nat} {side : List (Nat × Side)} {X : Core} (h : u ≠ v) :
    (phiS v side X).nodes.getX u = X.nodes.getX u := by
  simp only [phiS, getX_modify']; rw [if_neg (fun e : u = v ∧ v < X.nodes.size => h e.1)]

theorem phiS_getX_self {v : Nat} {side : List (Nat × Side)} {X : Core} (h : v < X.nodes.size) :
    (phiS v side X).nodes.getX v = { X.nodes.getX v with side := side } := by
  simp only [phiS, getX_modify', h, and_self, if_true]

theorem insStep_ok {κ : Caps} {t : Core} {L : Loc} {v j B : Nat} {side : List (Nat × Side)}
    (hv : v < t.nodes.size) (hnd : (t.nodes.getX v).inTables.Nodup) (hvT : v ∉ (t.nodes.getX v).inTables)
    (hroom : ∀ T ∈ (t.nodes.getX v).inTables, RoomOK t v T) (hj : j < (t.nodes.getX v).inTables.length)
    (hLv : L "v" = v) (hLv1 : L "v1" = t.nodes.size) (hLv2 : L "v2" = t.nodes.size + 1)
    (hvi : v < κ.lrec .inTab)
    (hcapT : ∀ T ∈ (t.nodes.getX v).inTables, T < κ.lrec .table ∧ T < κ.lrec .side ∧ T < κ.tbl .N ∧
      (t.nodes.getX T).table.length + 2 ≤ κ.lcap .table ∧ (t.nodes.getX T).side.length + 2 ≤ κ.lcap .side)
    (hB : ∀ T ∈ (t.nodes.getX v).inTables, (t.nodes.getX T).table.length ≤ B ∧ (t.nodes.getX T).side.length ≤ B) :
    ∃ L' c, evalF κ insBody (phiS v side (sdJ t v j)) (upd L "j" j) =
      .ok (phiS v side (sdJ t v (j + 1))) L' c ∧ c ≤ 1000 + 400 * B ∧
      ∀ r, r ≠ "j" → r ≠ "T" → r ≠ "a" → r ≠ "b" → L' r = L r := by
  set N := t.nodes.size
  set tabs := (t.nodes.getX v).inTables
  set T := tabs[j]
  set X := sdJ t v j
  set S := phiS v side X
  have hTm : T ∈ tabs := List.getElem_mem hj
  have hTn : T ∉ tabs.take j := nodup_getElem_notin_take hnd hj
  have hTv : T ≠ v := fun h => hvT (h ▸ hTm)
  have hTN : T < N := (hroom T hTm).lt
  have hvn : v ∉ tabs.take j := fun h => hvT (List.mem_of_mem_take h)
  have hST : S.nodes.getX T = t.nodes.getX T := by
    rw [phiS_getX_ne hTv]; exact sdJ_getX_notin hTn hTN
  have hSv : (S.nodes.getX v).inTables = tabs := by
    rw [phiS_getX_self (by rw [sdJ_size]; omega), sdJ_getX_notin hvn hv]
  have hroomS : RoomOK S v T := by unfold RoomOK; rw [hST]; exact hroom T hTm
  obtain ⟨hTt, hTs, hTNc, hcT, hcS⟩ := hcapT T hTm
  obtain ⟨hBt, hBs⟩ := hB T hTm
  -- the table
  set L0 := upd L "j" j
  have e1 := evalF_assign_ok (κ := κ) (s := S) (L := L0) (x := "T") (e := .lrd .inTab false "v" "j") (v := T) (by
    simp [Exp.ev, L0, OM.Machine.State.upd, hLv, hvi, LK.view, hSv, hj, T])
  set L1 := upd L0 "T" T
  have hL1 : ∀ r, r ≠ "j" → r ≠ "T" → L1 r = L r := fun r h1 h2 => by simp [L1, L0, OM.Machine.State.upd, h1, h2]
  -- the two labels
  set a := roomL S.P.beta (S.nodes.getX T).table v true
  set b := roomL S.P.beta (S.nodes.getX T).table v false
  obtain ⟨-, La, ca, ea, hla, hca⟩ := roomP_agree κ S
    (OM.Machine.State.setLocs (fun _ => 0) ["t", "e", "bf"] [T, v, 1]) (t := T) (e := v) (before := true)
    (by simp [OM.Machine.State.setLocs, OM.Machine.State.upd])
    (by simp [OM.Machine.State.setLocs, OM.Machine.State.upd])
    (by simp [OM.Machine.State.setLocs, OM.Machine.State.upd, b2n]) hTt (roomNextTo_run' hroomS true)
  have e2 := evalF_call_ok (q := roomP) (args := [.var "T", .var "v", 1]) (ds := ["a"]) (L := L1)
    (by simp [evList, Exp.ev, L1, L0, OM.Machine.State.upd, hLv]) ea
  set L2 := OM.Machine.State.setLocs L1 ["a"] (roomP.rets.map La)
  obtain ⟨-, Lb, cb, eb, hlb, hcb⟩ := roomP_agree κ S
    (OM.Machine.State.setLocs (fun _ => 0) ["t", "e", "bf"] [T, v, 0]) (t := T) (e := v) (before := false)
    (by simp [OM.Machine.State.setLocs, OM.Machine.State.upd])
    (by simp [OM.Machine.State.setLocs, OM.Machine.State.upd])
    (by simp [OM.Machine.State.setLocs, OM.Machine.State.upd, b2n]) hTt (roomNextTo_run' hroomS false)
  have e3 := evalF_call_ok (q := roomP) (args := [.var "T", .var "v", 0]) (ds := ["b"]) (L := L2)
    (by simp [evList, Exp.ev, L2, L1, L0, roomP, OM.Machine.State.setLocs, OM.Machine.State.upd, hLv]) eb
  set L3 := OM.Machine.State.setLocs L2 ["b"] (roomP.rets.map Lb)
  have hL3 : ∀ r, r ≠ "j" → r ≠ "T" → r ≠ "a" → r ≠ "b" → L3 r = L r := fun r h1 h2 h3 h4 => by
    simp only [L3, L2, roomP, OM.Machine.State.setLocs, List.map, OM.Machine.State.upd, if_neg h3, if_neg h4]
    exact hL1 r h1 h2
  have hL3T : L3 "T" = T := by simp [L3, L2, L1, roomP, OM.Machine.State.setLocs, OM.Machine.State.upd]
  have hL3a : L3 "a" = a := by simp [L3, L2, roomP, OM.Machine.State.setLocs, OM.Machine.State.upd, hla]; rfl
  have hL3b : L3 "b" = b := by simp [L3, roomP, OM.Machine.State.setLocs, OM.Machine.State.upd, hlb]; rfl
  -- the two insertions
  obtain ⟨A, le, Bs, htab, hA, hside, -, -⟩ := hroomS
  have hN1 : N ≠ v := by omega
  have hins := insertAroundIn_run (s := S) (T := T) (a := a) (b := b) (n2 := N + 1) htab hA hN1 hside
  have h1' := tableInsert_run (s := S) (t := T) (new := N) htab hA true a hside
  unfold insertAroundIn at hins
  obtain ⟨u, s1, h1, h2⟩ := run_bind_ok hins
  rw [h1'] at h1
  injection h1 with _ hs1
  subst hs1
  set s1 := { S with nodes := S.nodes.modify T (setTS (insTab A Bs v le N a true) (sideAfter (S.nodes.getX T) v N)) }
  have hTS : T < S.nodes.size := by simp [S, phiS, X, sdJ_size]; omega
  have hs1T : s1.nodes.getX T = setTS (insTab A Bs v le N a true) (sideAfter (S.nodes.getX T) v N) (S.nodes.getX T) := by
    simp only [s1, getX_modify', hTS, and_self, if_true]
  have hlenS : (S.nodes.getX T).table.length = A.length + Bs.length + 1 := by rw [htab]; simp; omega
  obtain ⟨L4', c4, e4', hc4⟩ := tableInsertP_agree κ S
    (OM.Machine.State.setLocs (fun _ => 0) ["t", "e", "w", "bf", "lab"] [T, v, N, 1, a]) (t := T) (e := v)
    (w := N) (before := true) (lab := a)
    (by simp [OM.Machine.State.setLocs, OM.Machine.State.upd])
    (by simp [OM.Machine.State.setLocs, OM.Machine.State.upd])
    (by simp [OM.Machine.State.setLocs, OM.Machine.State.upd])
    (by simp [OM.Machine.State.setLocs, OM.Machine.State.upd, b2n])
    (by simp [OM.Machine.State.setLocs, OM.Machine.State.upd]) hTt hTs hTNc
    (by rw [hST]; omega) (by rw [hST]; omega) h1'
  have e4 := evalF_call_ok (q := tableInsertP) (args := [.var "T", .var "v", .var "v1", 1, .var "a"]) (ds := [])
    (L := L3) (by
      simp [evList, Exp.ev, hL3T, hL3a, hL3 "v" (by decide) (by decide) (by decide) (by decide), hLv,
        hL3 "v1" (by decide) (by decide) (by decide) (by decide), hLv1]) e4'
  set L4 := OM.Machine.State.setLocs L3 [] (tableInsertP.rets.map L4')
  have hlen1 : (s1.nodes.getX T).table.length = (S.nodes.getX T).table.length + 1 := by
    rw [hs1T, hlenS]; simp [setTS, insTab]; omega
  have hside1 : (s1.nodes.getX T).side.length ≤ (S.nodes.getX T).side.length + 1 := by
    rw [hs1T]; simp only [setTS, sideAfter]; split
    · exact length_assocSet_le' _ _ _
    · omega
  obtain ⟨L5', c5, e5', hc5⟩ := tableInsertP_agree κ s1
    (OM.Machine.State.setLocs (fun _ => 0) ["t", "e", "w", "bf", "lab"] [T, v, N + 1, 0, b]) (t := T) (e := v)
    (w := N + 1) (before := false) (lab := b)
    (by simp [OM.Machine.State.setLocs, OM.Machine.State.upd])
    (by simp [OM.Machine.State.setLocs, OM.Machine.State.upd])
    (by simp [OM.Machine.State.setLocs, OM.Machine.State.upd])
    (by simp [OM.Machine.State.setLocs, OM.Machine.State.upd, b2n])
    (by simp [OM.Machine.State.setLocs, OM.Machine.State.upd]) hTt hTs hTNc
    (by rw [hlen1, hST]; omega) (by rw [hST] at hside1; omega) h2
  have e5 := evalF_call_ok (q := tableInsertP) (args := [.var "T", .var "v", .var "v2", 0, .var "b"]) (ds := [])
    (L := L4) (by
      simp [evList, Exp.ev, L4, OM.Machine.State.setLocs, hL3T, hL3b,
        hL3 "v" (by decide) (by decide) (by decide) (by decide), hLv,
        hL3 "v2" (by decide) (by decide) (by decide) (by decide), hLv2]) e5'
  have hG : aroundF (sd1 t v) v N (N + 1) (sF t v) T =
      setTS (aroundTab A Bs v le N (N + 1) a b) (sideAround (S.nodes.getX T) v N (N + 1)) := by
    have ha : a = roomL t.P.beta (A ++ (v, le) :: Bs) v true := by
      show roomL S.P.beta (S.nodes.getX T).table v true = _; rw [htab]; rfl
    have hb : b = roomL t.P.beta (A ++ (v, le) :: Bs) v false := by
      show roomL S.P.beta (S.nodes.getX T).table v false = _; rw [htab]; rfl
    unfold aroundF sF
    rw [sd1_getX t v hTN, ← hST, htab, aroundT_eq hA, ha, hb]
  have hfin : { S with nodes := S.nodes.modify T (setTS (aroundTab A Bs v le N (N + 1) a b)
      (sideAround (S.nodes.getX T) v N (N + 1))) } = phiS v side (sdJ t v (j + 1)) := by
    have hn := sdJ_succ t v j hj
    simp only [aroundStep] at hn
    simp only [S, phiS]
    rw [hn, hG, Array.modify_comm _ hTv]
    rfl
  rw [hfin] at e5
  refine ⟨_, _, evalF_seq_ok2 e1 (evalF_seq_ok2 e2 (evalF_seq_ok2 e3 (evalF_seq_ok2 e4 e5))), ?_, ?_⟩
  · rw [hST] at hca hcb hc4
    rw [hlen1, hST] at hc5
    rw [hST] at hside1
    have : (s1.nodes.getX T).side.length ≤ B + 1 := by omega
    simp only [Exp.cost, costList, List.map, List.sum_cons, List.sum_nil, List.length_cons, List.length_nil,
      Exp.ofNat_def] at hca hcb hc4 hc5 ⊢
    omega
  · intro r h1 h2 h3 h4
    simp only [OM.Machine.State.setLocs, tableInsertP, List.map]
    exact hL3 r h1 h2 h3 h4

theorem sdJ_zero (t : Core) (v : Nat) : sdJ t v 0 = sd1 t v := by simp [sdJ]

theorem insS_ok {κ : Caps} {t : Core} {L : Loc} {v B : Nat} {side : List (Nat × Side)}
    (hv : v < t.nodes.size) (hnd : (t.nodes.getX v).inTables.Nodup) (hvT : v ∉ (t.nodes.getX v).inTables)
    (hroom : ∀ T ∈ (t.nodes.getX v).inTables, RoomOK t v T)
    (hLv : L "v" = v) (hLv1 : L "v1" = t.nodes.size) (hLv2 : L "v2" = t.nodes.size + 1)
    (hvi : v < κ.lrec .inTab)
    (hcapT : ∀ T ∈ (t.nodes.getX v).inTables, T < κ.lrec .table ∧ T < κ.lrec .side ∧ T < κ.tbl .N ∧
      (t.nodes.getX T).table.length + 2 ≤ κ.lcap .table ∧ (t.nodes.getX T).side.length + 2 ≤ κ.lcap .side)
    (hB : ∀ T ∈ (t.nodes.getX v).inTables, (t.nodes.getX T).table.length ≤ B ∧ (t.nodes.getX T).side.length ≤ B) :
    ∃ L' c, evalF κ insS (phiS v side (sd1 t v)) L = .ok (phiS v side (sd2 t v)) L' c ∧
      c ≤ 5 + (t.nodes.getX v).inTables.length * (1001 + 400 * B) ∧
      ∀ r, r ≠ "m" → r ≠ "j" → r ≠ "T" → r ≠ "a" → r ≠ "b" → L' r = L r := by
  set m := (t.nodes.getX v).inTables.length
  have hSv : ((phiS v side (sd1 t v)).nodes.getX v).inTables = (t.nodes.getX v).inTables := by
    rw [phiS_getX_self (by simp [sd1]; omega), sd1_getX t v hv]
  have a1 := evalF_assign_ok (κ := κ) (s := phiS v side (sd1 t v)) (L := L) (x := "m") (e := .llen .inTab "v") (v := m)
    (by simp [Exp.ev, hLv, hvi, LK.view, hSv, m])
  set L1 := upd L "m" m
  obtain ⟨S', L', c, he, hc, hs', hF⟩ := evalF_loop (κ := κ) (x := "j") (n := .var "m") (b := insBody)
    (s := phiS v side (sd1 t v)) (L := L1) (N := m) (by simp [Exp.ev, L1, OM.Machine.State.upd])
    (fun j S L' => S = phiS v side (sdJ t v j) ∧
      ∀ r, r ≠ "m" → r ≠ "j" → r ≠ "T" → r ≠ "a" → r ≠ "b" → L' r = L r) (1000 + 400 * B)
    ⟨by rw [sdJ_zero], fun r h1 _ _ _ _ => by simp [L1, OM.Machine.State.upd, h1]⟩
    (by
      intro j hj S1 L2 ⟨hS1, hF2⟩
      subst hS1
      obtain ⟨L3, c3, e3, hc3, hF3⟩ := insStep_ok (κ := κ) (L := L2) (side := side) (B := B) hv hnd hvT hroom hj
        (by rw [hF2 "v" (by decide) (by decide) (by decide) (by decide) (by decide), hLv])
        (by rw [hF2 "v1" (by decide) (by decide) (by decide) (by decide) (by decide), hLv1])
        (by rw [hF2 "v2" (by decide) (by decide) (by decide) (by decide) (by decide), hLv2]) hvi hcapT hB
      exact ⟨_, L3, c3, e3, hc3, rfl, fun r h1 h2 h3 h4 h5 => (hF3 r h2 h3 h4 h5).trans (hF2 r h1 h2 h3 h4 h5)⟩)
  rw [hs', show m = (t.nodes.getX v).inTables.length from rfl, sdJ_all] at he
  refine ⟨L', _, evalF_seq_ok2 a1 he, ?_, hF⟩
  simp only [Exp.cost] at hc ⊢
  have e : m * (1 + (1000 + 400 * B)) = m * (1001 + 400 * B) := by ring
  rw [e] at hc; omega

/-! ### Stage 3: the tables of `v1`, `v2` -/

/-- `drainEntries`' test for entry `e` of `v`'s table. -/
def entOK (t : Core) (v e : Nat) : Bool :=
  sH t v == 1 || (t.nodes.getX v).children.contains e || (t.nodes.getX e).first != NIL

/-- `q := ` entry `e` is a drain entry on side `sd` (locals `v h e sd`). -/
def selE : Exp := ((("h" =ₑ 1) ||ₑ ("r" <ₑ "m")) ||ₑ (!ₑ (.rd (.n .first) "e" =ₑ 0))) &&ₑ ("f" &&ₑ ("x" =ₑ "sd"))
def selS : Stm :=
  (findP .children).call [.var "v", .var "e"] ["r"] ;;
  "m" ::= .llen .children "v" ;;
  (lookupP .side).call [.var "v", .var "e"] ["f", "x"] ;;
  "q" ::= selE

/-- What `selS` reads agrees with Level F's state `t`. -/
structure ReadOK (St t : Core) (v : Nat) (side : List (Nat × Side)) : Prop where
  tab : (St.nodes.getX v).table = (t.nodes.getX v).table
  kids : (St.nodes.getX v).children = (t.nodes.getX v).children
  side : (St.nodes.getX v).side = side
  first : ∀ e, (St.nodes.getX e).first = (t.nodes.getX e).first

theorem selS_ok {κ : Caps} {St t : Core} {L : Loc} {v e : Nat} {side : List (Nat × Side)} {sd : Side}
    (hR : ReadOK St t v side) (hLv : L "v" = v) (hLh : L "h" = sH t v) (hLe : L "e" = e) (hLs : L "sd" = sideN sd)
    (hvc : v < κ.lrec .children) (hvs : v < κ.lrec .side) (heN : e < κ.tbl .N) :
    ∃ L' c, evalF κ selS St L = .ok St L' c ∧
      L' "q" = (if entOK t v e = true ∧ lookup side e = some sd then 1 else 0) ∧
      c ≤ 120 + 20 * (t.nodes.getX v).children.length + 20 * side.length ∧
      ∀ r, r ≠ "r" → r ≠ "m" → r ≠ "f" → r ≠ "x" → r ≠ "q" → L' r = L r := by
  have hvC : LK.view St v .children = (t.nodes.getX v).children.map fun e => (e, 0) := by
    simp [LK.view, hR.kids]
  have hvS : LK.view St v .side = encS side := by simp [LK.view, hR.side]
  obtain ⟨Lf, cf, ef, hrf, hcf⟩ := findP_agree κ .children St
    (OM.Machine.State.setLocs (fun _ => 0) ["i", "x"] [v, e]) (i := v) (x := e)
    (by simp [OM.Machine.State.setLocs, OM.Machine.State.upd])
    (by simp [OM.Machine.State.setLocs, OM.Machine.State.upd]) hvc
  have e1 := evalF_call_ok (q := findP .children) (args := [.var "v", .var "e"]) (ds := ["r"]) (L := L)
    (by simp [evList, Exp.ev, hLv, hLe]) ef
  set L1 := OM.Machine.State.setLocs L ["r"] ((findP .children).rets.map Lf)
  have hL1 : ∀ r, r ≠ "r" → L1 r = L r := fun r h => by
    simp [L1, findP, OM.Machine.State.setLocs, OM.Machine.State.upd, h]
  have e2 := evalF_assign_ok (κ := κ) (s := St) (L := L1) (x := "m") (e := .llen .children "v")
    (v := (t.nodes.getX v).children.length) (by simp [Exp.ev, hL1 "v" (by decide), hLv, hvc, hvC])
  set L2 := upd L1 "m" (t.nodes.getX v).children.length
  obtain ⟨Lk, ck, ek, hfk, hvk, -, -, hck⟩ := lookupP_agree κ .side St
    (OM.Machine.State.setLocs (fun _ => 0) ["i", "x"] [v, e]) (i := v) (x := e)
    (by simp [OM.Machine.State.setLocs, OM.Machine.State.upd])
    (by simp [OM.Machine.State.setLocs, OM.Machine.State.upd]) hvs
  rw [hvS, lookup_encS] at hfk hvk
  rw [hvS] at hck
  have e3 := evalF_call_ok (q := lookupP .side) (args := [.var "v", .var "e"]) (ds := ["f", "x"]) (L := L2)
    (by simp [evList, Exp.ev, L2, OM.Machine.State.upd, hL1 "v" (by decide), hLv, hL1 "e" (by decide), hLe]) ek
  set L3 := OM.Machine.State.setLocs L2 ["f", "x"] ((lookupP .side).rets.map Lk)
  have hL3 : ∀ r, r ≠ "r" → r ≠ "m" → r ≠ "f" → r ≠ "x" → L3 r = L r := fun r h1 h2 h3 h4 => by
    simp only [L3, L2, lookupP, OM.Machine.State.setLocs, List.map, OM.Machine.State.upd, if_neg h2, if_neg h3,
      if_neg h4]
    exact hL1 r h1
  have hq : selE.ev κ St L3 = some (if entOK t v e = true ∧ lookup side e = some sd then 1 else 0) := by
    have h3r : L3 "r" = ((t.nodes.getX v).children.map fun e => (e, 0)).findIdx (·.1 == e) := by
      simp [L3, L2, L1, lookupP, findP, OM.Machine.State.setLocs, OM.Machine.State.upd, hrf, hvC]
    have h3m : L3 "m" = (t.nodes.getX v).children.length := by
      simp [L3, L2, lookupP, OM.Machine.State.setLocs, OM.Machine.State.upd]
    have h3f : L3 "f" = if ((lookup side e).map sideN).isSome then 1 else 0 := by
      simp [L3, lookupP, OM.Machine.State.setLocs, OM.Machine.State.upd, hfk]
    have h3x : L3 "x" = ((lookup side e).map sideN).getD 0 := by
      simp [L3, lookupP, OM.Machine.State.setLocs, OM.Machine.State.upd, hvk]
    have hc := findIdx_pair0 (t.nodes.getX v).children e
    simp only [selE, Exp.ev, h3r, h3m, h3f, h3x, hL3 "h" (by decide) (by decide) (by decide) (by decide), hLh,
      hL3 "e" (by decide) (by decide) (by decide) (by decide), hLe,
      hL3 "sd" (by decide) (by decide) (by decide) (by decide), hLs, Option.bind_some, heN, Fld.cap, Fld.get,
      NF.get, hR.first, if_true, OM.Machine.BinOp.eval, OM.Machine.UnOp.eval, Option.map_some, Exp.ofNat_def]
    simp only [hc]
    congr 1
    unfold entOK
    cases hl : lookup side e with
    | none => simp
    | some st =>
      cases st <;> cases sd <;> simp [sideN] <;>
        by_cases h1 : sH t v = 1 <;> by_cases h2 : (t.nodes.getX v).children.contains e = true <;>
        by_cases h3 : (t.nodes.getX e).first = 0 <;> simp_all [NIL]
  have e4 := evalF_assign_ok (κ := κ) (s := St) (L := L3) (x := "q") (e := selE) hq
  refine ⟨_, _, evalF_seq_ok2 e1 (evalF_seq_ok2 e2 (evalF_seq_ok2 e3 e4)), by simp [OM.Machine.State.upd], ?_, ?_⟩
  · simp only [List.length_map] at hcf hck
    simp only [Exp.cost, costList, List.map, List.sum_cons, List.sum_nil, List.length_cons, List.length_nil,
      Exp.ofNat_def, selE] at hcf hck ⊢
    simp only [LK.view, hR.kids, List.length_map] at hcf
    omega
  · intro r h1 h2 h3 h4 h5; simp only [OM.Machine.State.upd, if_neg h5]; exact hL3 r h1 h2 h3 h4

/-- The entries of `v`'s table that go to the new node on side `sd`. -/
def selP (t : Core) (v : Nat) (side : List (Nat × Side)) (sd : Side) (e : Nat) : Bool :=
  entOK t v e && lookup side e == some sd

def part (t : Core) (v : Nat) (side : List (Nat × Side)) (sd : Side) : List Nat :=
  ((t.nodes.getX v).table.map (·.1)).filter (selP t v side sd)

theorem sLeft_part (t : Core) (v : Nat) (side : List (Nat × Side)) : sLeft t v side = part t v side .left := by
  simp only [sLeft, sEntries, drainEntries, part, List.filter_filter, Node.order]
  congr 1; funext e; simp [selP, entOK, Bool.and_comm]

theorem sRight_part (t : Core) (v : Nat) (side : List (Nat × Side)) : sRight t v side = part t v side .right := by
  simp only [sRight, sEntries, drainEntries, part, List.filter_filter, Node.order]
  congr 1; funext e; simp [selP, entOK, Bool.and_comm]

/-- `evenTable` with the spacing `st`. -/
def evT (st : Nat) (l : List Nat) : List (Nat × Nat) := ((List.range l.length).zip l).map fun (i, e) => (e, (i + 1) * st)

theorem evenTable_evT (β : Nat) (l : List Nat) : evenTable β l = evT ((1 <<< β) / (l.length + 1)) l := rfl

theorem evT_append (st : Nat) (l : List Nat) (e : Nat) : evT st (l ++ [e]) = evT st l ++ [(e, (l.length + 1) * st)] := by
  simp only [evT, List.length_append, List.length_singleton, List.range_succ]
  rw [List.zip_append (by simp)]
  simp

theorem foldl_count (p : Nat → Bool) (l : List Nat) : ∀ n, n ≤ l.length →
    (List.range n).foldl (fun c j => c + if p (l.getD j 0) then 1 else 0) 0 = ((l.take n).filter p).length
  | 0, _ => by simp
  | n + 1, h => by
    rw [List.range_succ, List.foldl_append, foldl_count p l n (by omega), List.take_succ_eq_append_getElem (by omega),
      List.filter_append]
    simp only [List.foldl_cons, List.foldl_nil, List.getD_eq_getElem _ _ (show n < l.length by omega)]
    by_cases hp : p l[n] = true <;> simp [hp]

theorem ReadOK.put_table {St t : Core} {v w : Nat} {side : List (Nat × Side)} (hR : ReadOK St t v side)
    (hw : w ≠ v) (l : List (Nat × Nat)) : ReadOK (LK.put St w l .table) t v side := by
  have hg : ∀ u, u ≠ w → (LK.put St w l .table).nodes.getX u = St.nodes.getX u := by
    intro u hu; simp only [LK.put, getX_modify']; rw [if_neg (fun h => hu h.1)]
  have hf : ∀ u, ((LK.put St w l .table).nodes.getX u).first = (St.nodes.getX u).first := by
    intro u; simp only [LK.put, getX_modify']; split <;> rfl
  exact ⟨by rw [hg v (Ne.symm hw)]; exact hR.tab, by rw [hg v (Ne.symm hw)]; exact hR.kids,
    by rw [hg v (Ne.symm hw)]; exact hR.side, fun u => by rw [hf]; exact hR.first u⟩

def cntBody : Stm := "e" ::= .lrd .table false "v" "j" ;; selS ;; .ite "q" ("cnt" ::= "cnt" + 1) .skip
def bldBody : Stm :=
  "e" ::= .lrd .table false "v" "j" ;; selS ;;
  .ite "q" ("idx" ::= "idx" + 1 ;; .lgrow .table "w" "e" ("idx" * "st")) .skip
/-- **The table of a new node `w`**: the drain entries of side `sd`, evenly labelled. -/
def tabS : Stm :=
  "nt" ::= .llen .table "v" ;;
  "cnt" ::= 0 ;; .loop "j" "nt" cntBody ;;
  "st" ::= .bin .shl 1 (.prm .beta) / ("cnt" + 1) ;;
  "idx" ::= 0 ;; .loop "j" "nt" bldBody

theorem length_evT (st : Nat) (l : List Nat) : (evT st l).length = l.length := by simp [evT]

theorem tabS_ok {κ : Caps} {St t : Core} {L : Loc} {v w : Nat} {side : List (Nat × Side)} {sd : Side}
    (hR : ReadOK St t v side) (hP : St.P = t.P) (hw0 : (St.nodes.getX w).table = []) (hwv : w ≠ v)
    (hws : w < St.nodes.size)
    (hLv : L "v" = v) (hLw : L "w" = w) (hLh : L "h" = sH t v) (hLs : L "sd" = sideN sd)
    (hvc : v < κ.lrec .children) (hvs : v < κ.lrec .side) (hvt : v < κ.lrec .table) (hwt : w < κ.lrec .table)
    (hN : ∀ e ∈ (t.nodes.getX v).table.map (·.1), e < κ.tbl .N)
    (hcap : (t.nodes.getX v).table.length ≤ κ.lcap .table) :
    ∃ L' c, evalF κ tabS St L = .ok (LK.put St w (evenTable t.P.beta (part t v side sd)) .table) L' c ∧
      c ≤ 20 + (t.nodes.getX v).table.length * (320 + 40 * (t.nodes.getX v).children.length +
        40 * side.length) ∧
      ∀ r, r ≠ "nt" → r ≠ "cnt" → r ≠ "j" → r ≠ "e" → r ≠ "r" → r ≠ "m" → r ≠ "f" → r ≠ "x" → r ≠ "q" →
        r ≠ "st" → r ≠ "idx" → L' r = L r := by
  set o := (t.nodes.getX v).table.map (·.1)
  set n := (t.nodes.getX v).table.length
  set K := (t.nodes.getX v).children.length
  set p := selP t v side sd
  have hon : o.length = n := by simp [o, n]
  have hvT : LK.view St v .table = (t.nodes.getX v).table := by simp [LK.view, hR.tab]
  have hsel : ∀ e, (entOK t v e = true ∧ lookup side e = some sd) ↔ p e = true := by
    intro e; simp [p, selP]
  have hoj : ∀ j (hj : j < n), ((t.nodes.getX v).table[j]?.getD (0, 0)).1 = o[j]'(by omega) := by
    intro j hj; simp [o, List.getElem?_eq_getElem hj]
  -- the count
  have a1 := evalF_assign_ok (κ := κ) (s := St) (L := L) (x := "nt") (e := .llen .table "v") (v := n)
    (by simp [Exp.ev, hLv, hvt, hvT, n])
  have a2 := evalF_assign_ok (κ := κ) (s := St) (L := upd L "nt" n) (x := "cnt") (e := (0 : Exp)) (v := 0) rfl
  set L2 := upd (upd L "nt" n) "cnt" 0
  have hL2 : ∀ r, r ≠ "nt" → r ≠ "cnt" → L2 r = L r := fun r h1 h2 => by simp [L2, OM.Machine.State.upd, h1, h2]
  obtain ⟨L3, c3, e3, hc3, hF3, ha3⟩ := evalF_loop_pure (κ := κ) (x := "j") (n := .var "nt") (b := cntBody)
    (s := St) (L := L2) (N := n) (by simp [Exp.ev, L2, OM.Machine.State.upd])
    (fun L' => ∀ r, r ≠ "cnt" → r ≠ "j" → r ≠ "e" → r ≠ "r" → r ≠ "m" → r ≠ "f" → r ≠ "x" → r ≠ "q" →
      L' r = L2 r) (fun L' => L' "cnt") (fun c j => c + if p (o.getD j 0) then 1 else 0)
    (140 + 20 * K + 20 * side.length) (fun _ _ _ _ _ _ _ _ _ => rfl)
    (by
      intro j hj L' hF
      have hv' : L' "v" = v := by
        rw [hF "v" (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide),
          hL2 "v" (by decide) (by decide), hLv]
      have e1 := evalF_assign_ok (κ := κ) (s := St) (L := upd L' "j" j) (x := "e") (e := .lrd .table false "v" "j")
        (v := o[j]'(by omega)) (by
          have hj2 : j < (t.nodes.getX v).table.length := hj
          have hoj2 : (t.nodes.getX v).table[j].1 = o[j]'(by omega) := by simp [o]
          simp [Exp.ev, OM.Machine.State.upd, hv', hvt, hvT, hj2, hoj2])
      set L4 := upd (upd L' "j" j) "e" (o[j]'(by omega))
      obtain ⟨L5, c5, e5, hq5, hc5, hF5⟩ := selS_ok (κ := κ) (St := St) (t := t) (L := L4) (v := v)
        (e := o[j]'(by omega)) (side := side) (sd := sd) hR
        (by simp [L4, OM.Machine.State.upd, hv'])
        (by simp only [L4, OM.Machine.State.upd]; simp
            rw [hF "h" (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
              (by decide), hL2 "h" (by decide) (by decide), hLh])
        (by simp [L4, OM.Machine.State.upd])
        (by simp only [L4, OM.Machine.State.upd]; simp
            rw [hF "sd" (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
              (by decide), hL2 "sd" (by decide) (by decide), hLs])
        hvc hvs (hN _ (List.getElem_mem _))
      have hc5' : L5 "cnt" = L' "cnt" := by
        rw [hF5 "cnt" (by decide) (by decide) (by decide) (by decide) (by decide)]; simp [L4, OM.Machine.State.upd]
      have hgetD : o.getD j 0 = o[j]'(by omega) := List.getD_eq_getElem _ _ _
      by_cases hpj : p (o[j]'(by omega)) = true
      · have e6 := evalF_assign_ok (κ := κ) (s := St) (L := L5) (x := "cnt") (e := "cnt" + 1) (v := L' "cnt" + 1)
          (by simp [Exp.ev, OM.Machine.BinOp.eval, hc5'])
        refine ⟨_, _, evalF_seq_ok2 e1 (evalF_seq_ok2 e5 (evalF_ite_t (v := 1)
          (by simp [Exp.ev, hq5, (hsel _).mpr hpj]) one_ne_zero e6)), ?_, ?_, ?_⟩
        · simp [Exp.cost] at hc5 ⊢; omega
        · intro r h1 h2 h3 h4 h5 h6 h7 h8
          simp only [OM.Machine.State.upd, if_neg h1]
          rw [hF5 r h4 h5 h6 h7 h8]; simp only [L4, OM.Machine.State.upd, if_neg h2, if_neg h3]
          exact hF r h1 h2 h3 h4 h5 h6 h7 h8
        · rw [hgetD, if_pos hpj]; simp [OM.Machine.State.upd]
      · refine ⟨_, _, evalF_seq_ok2 e1 (evalF_seq_ok2 e5 (evalF_ite_f
          (by simp [Exp.ev, hq5]; intro a b; exact hpj ((hsel _).mp ⟨a, b⟩)) evalF_skip)), ?_, ?_, ?_⟩
        · simp [Exp.cost] at hc5 ⊢; omega
        · intro r h1 h2 h3 h4 h5 h6 h7 h8
          rw [hF5 r h4 h5 h6 h7 h8]; simp only [L4, OM.Machine.State.upd, if_neg h2, if_neg h3]
          exact hF r h1 h2 h3 h4 h5 h6 h7 h8
        · rw [hgetD, if_neg hpj, hc5']; rfl)
  have hcnt : L3 "cnt" = (part t v side sd).length := by
    have h0 : L2 "cnt" = 0 := by simp [L2, OM.Machine.State.upd]
    rw [ha3, h0, foldl_count p o n (by omega), ← hon, List.take_length]; rfl
  -- the spacing
  set pl := part t v side sd
  set st := (1 <<< t.P.beta) / (pl.length + 1)
  have a3 := evalF_assign_ok (κ := κ) (s := St) (L := L3) (x := "st") (e := .bin .shl 1 (.prm .beta) / ("cnt" + 1))
    (v := st) (by simp [Exp.ev, OM.Machine.BinOp.eval, PF.get, hP, hcnt, st, Nat.shiftLeft_eq])
  have a4 := evalF_assign_ok (κ := κ) (s := St) (L := upd L3 "st" st) (x := "idx") (e := (0 : Exp)) (v := 0) rfl
  set L5 := upd (upd L3 "st" st) "idx" 0
  have hL5 : ∀ r, r ≠ "nt" → r ≠ "cnt" → r ≠ "j" → r ≠ "e" → r ≠ "r" → r ≠ "m" → r ≠ "f" → r ≠ "x" → r ≠ "q" →
      r ≠ "st" → r ≠ "idx" → L5 r = L r := by
    intro r h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11
    simp only [L5, OM.Machine.State.upd, if_neg h10, if_neg h11]
    rw [hF3 r h2 h3 h4 h5 h6 h7 h8 h9, hL2 r h1 h2]
  -- the build
  have hwi : LK.table.idOk St w := by simp [LK.idOk, LK.recOk, hws]
  have hput0 : LK.put St w [] .table = St := by
    have := LK.put_view hwi; simp only [LK.view, hw0] at this; exact this
  have hR' : ∀ l, ReadOK (LK.put St w l .table) t v side := fun l => hR.put_table hwv l
  have hvT' : ∀ l, LK.view (LK.put St w l .table) v .table = (t.nodes.getX v).table := by
    intro l; rw [LK.view_put (by simp [LK.recOk, hws]) (by simp [LK.valid])]; simp [Ne.symm hwv, hvT]
  have hwT' : ∀ l, LK.view (LK.put St w l .table) w .table = l := by
    intro l; rw [LK.view_put (by simp [LK.recOk, hws]) (by simp [LK.valid])]; simp
  have hlenf : ∀ j, ((o.take j).filter p).length ≤ n := by
    intro j; have := List.length_filter_le p (o.take j); simp at this; omega
  obtain ⟨S6, L6, c6, e6, hc6, hS6, hi6, hF6⟩ := evalF_loop (κ := κ) (x := "j") (n := .var "nt") (b := bldBody)
    (s := St) (L := L5) (N := n) (by
      simp [Exp.ev, L5, OM.Machine.State.upd]
      rw [hF3 "nt" (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)]
      simp [L2, OM.Machine.State.upd])
    (fun j S L' => S = LK.put St w (evT st ((o.take j).filter p)) .table ∧
      L' "idx" = ((o.take j).filter p).length ∧
      ∀ r, r ≠ "j" → r ≠ "e" → r ≠ "r" → r ≠ "m" → r ≠ "f" → r ≠ "x" → r ≠ "q" → r ≠ "idx" → L' r = L5 r)
    (170 + 20 * K + 20 * side.length)
    ⟨by simp [evT, hput0], by simp [L5, OM.Machine.State.upd], fun _ _ _ _ _ _ _ _ _ => rfl⟩
    (by
      intro j hj S1 L' ⟨hS1, hidx, hF⟩
      subst hS1
      set fj := (o.take j).filter p
      set S1 := LK.put St w (evT st fj) .table
      have hvS1 : LK.view S1 v .table = (t.nodes.getX v).table := hvT' _
      have hwS1 : LK.view S1 w .table = evT st fj := hwT' _
      have hv' : L' "v" = v := by
        rw [hF "v" (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide),
          hL5 "v" (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
            (by decide) (by decide) (by decide), hLv]
      have hfr : ∀ r, r ≠ "j" → r ≠ "e" → r ≠ "r" → r ≠ "m" → r ≠ "f" → r ≠ "x" → r ≠ "q" → r ≠ "idx" →
          r ≠ "nt" → r ≠ "cnt" → r ≠ "st" → L' r = L r := by
        intro r h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11
        rw [hF r h1 h2 h3 h4 h5 h6 h7 h8, hL5 r h9 h10 h1 h2 h3 h4 h5 h6 h7 h11 h8]
      have e1 := evalF_assign_ok (κ := κ) (s := S1) (L := upd L' "j" j) (x := "e") (e := .lrd .table false "v" "j")
        (v := o[j]'(by omega)) (by
          have hj2 : j < (t.nodes.getX v).table.length := hj
          have hoj2 : (t.nodes.getX v).table[j].1 = o[j]'(by omega) := by simp [o]
          simp [Exp.ev, OM.Machine.State.upd, hv', hvt, hvS1, hj2, hoj2])
      set L4 := upd (upd L' "j" j) "e" (o[j]'(by omega))
      obtain ⟨L7, c7, e7, hq7, hc7, hF7⟩ := selS_ok (κ := κ) (St := S1) (t := t) (L := L4) (v := v)
        (e := o[j]'(by omega)) (side := side) (sd := sd) (hR' _)
        (by simp [L4, OM.Machine.State.upd, hv'])
        (by simp only [L4, OM.Machine.State.upd]; simp
            rw [hfr "h" (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
              (by decide) (by decide) (by decide) (by decide), hLh])
        (by simp [L4, OM.Machine.State.upd])
        (by simp only [L4, OM.Machine.State.upd]; simp
            rw [hfr "sd" (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
              (by decide) (by decide) (by decide) (by decide), hLs])
        hvc hvs (hN _ (List.getElem_mem _))
      have h7i : L7 "idx" = fj.length := by
        rw [hF7 "idx" (by decide) (by decide) (by decide) (by decide) (by decide)]
        simp [L4, OM.Machine.State.upd, hidx]
      have h7w : L7 "w" = w := by
        rw [hF7 "w" (by decide) (by decide) (by decide) (by decide) (by decide)]
        simp only [L4, OM.Machine.State.upd]; simp
        rw [hfr "w" (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
          (by decide) (by decide) (by decide) (by decide), hLw]
      have h7e : L7 "e" = o[j]'(by omega) := by
        rw [hF7 "e" (by decide) (by decide) (by decide) (by decide) (by decide)]; simp [L4, OM.Machine.State.upd]
      have h7st : L7 "st" = st := by
        rw [hF7 "st" (by decide) (by decide) (by decide) (by decide) (by decide)]
        simp only [L4, OM.Machine.State.upd]; simp
        rw [hF "st" (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)]
        simp [L5, OM.Machine.State.upd]
      have hfr7 : ∀ r, r ≠ "j" → r ≠ "e" → r ≠ "r" → r ≠ "m" → r ≠ "f" → r ≠ "x" → r ≠ "q" → r ≠ "idx" →
          L7 r = L5 r := by
        intro r h1 h2 h3 h4 h5 h6 h7 h8
        rw [hF7 r h3 h4 h5 h6 h7]; simp only [L4, OM.Machine.State.upd, if_neg h1, if_neg h2]
        exact hF r h1 h2 h3 h4 h5 h6 h7 h8
      have htk : (o.take (j + 1)).filter p = fj ++ (if p (o[j]'(by omega)) then [o[j]'(by omega)] else []) := by
        rw [List.take_succ_eq_append_getElem (by omega), List.filter_append]
        by_cases hpj : p (o[j]'(by omega)) = true <;> simp [hpj, fj]
      by_cases hpj : p (o[j]'(by omega)) = true
      · have e8 := evalF_assign_ok (κ := κ) (s := S1) (L := L7) (x := "idx") (e := "idx" + 1) (v := fj.length + 1)
          (by simp [Exp.ev, OM.Machine.BinOp.eval, h7i])
        set L8 := upd L7 "idx" (fj.length + 1)
        have hfj : fj.length + 1 ≤ n := by
          have := hlenf (j + 1); rw [htk, if_pos hpj] at this; simpa using this
        have hso := LK.set_ok (κ := κ) (s := S1) (i := w)
          (l := evT st fj ++ [(o[j]'(by omega), (fj.length + 1) * st)]) (k := .table)
          (by simp [S1, LK.recOk, hws]) (by simp [LK.valid]) (by simp [length_evT]; omega) hwt
        rw [LK.put_put] at hso
        have e9 : evalF κ (.lgrow .table "w" "e" ("idx" * "st")) S1 L8 =
            .ok (LK.put St w (evT st fj ++ [(o[j]'(by omega), (fj.length + 1) * st)]) .table) L8 24 := by
          simp only [evalF, Exp.ev, L8, OM.Machine.State.upd, h7w, h7e, h7st,
            OM.Machine.BinOp.eval, Option.bind_some, Exp.cost]
          simp only [show ("w" = "idx") = False by decide, show ("e" = "idx") = False by decide,
            show ("st" = "idx") = False by decide, show ("idx" = "idx") = True by decide, if_true, if_false,
            h7w, h7e, h7st]
          rw [hwS1, hso]
        rw [← evT_append, ← (if_pos hpj : (if p (o[j]'(by omega)) then [o[j]'(by omega)] else []) = _), ← htk] at e9
        refine ⟨_, _, _, evalF_seq_ok2 e1 (evalF_seq_ok2 e7 (evalF_ite_t (v := 1)
          (by simp [Exp.ev, hq7, (hsel _).mpr hpj]) one_ne_zero (evalF_seq_ok2 e8 e9))), ?_, rfl, ?_, ?_⟩
        · simp [Exp.cost] at hc7 ⊢; omega
        · simp only [L8, OM.Machine.State.upd, if_true]; rw [htk, if_pos hpj]; simp
        · intro r h1 h2 h3 h4 h5 h6 h7 h8
          simp only [L8, OM.Machine.State.upd, if_neg h8]; exact hfr7 r h1 h2 h3 h4 h5 h6 h7 h8
      · refine ⟨_, _, _, evalF_seq_ok2 e1 (evalF_seq_ok2 e7 (evalF_ite_f
          (by simp [Exp.ev, hq7]; intro a b; exact hpj ((hsel _).mp ⟨a, b⟩)) evalF_skip)), ?_, ?_, ?_, ?_⟩
        · simp [Exp.cost] at hc7 ⊢; omega
        · rw [htk, if_neg hpj, List.append_nil]
        · rw [htk, if_neg hpj, List.append_nil, h7i]
        · exact hfr7)
  rw [hS6, ← hon, List.take_length] at e6
  have hfin : evT st (o.filter p) = evenTable t.P.beta pl := by rw [evenTable_evT]; rfl
  rw [hfin] at e6
  refine ⟨L6, _, evalF_seq_ok2 a1 (evalF_seq_ok2 a2 (evalF_seq_ok2 e3 (evalF_seq_ok2 a3 (evalF_seq_ok2 a4 e6)))),
    ?_, ?_⟩
  · simp only [Exp.cost, Exp.div_def, Exp.add_def, Exp.ofNat_def] at hc3 hc6 ⊢
    have h1 : n * (1 + (140 + 20 * K + 20 * side.length)) + n * (1 + (170 + 20 * K + 20 * side.length)) ≤
        n * (320 + 40 * K + 40 * side.length) := by
      have : n * (1 + (140 + 20 * K + 20 * side.length)) + n * (1 + (170 + 20 * K + 20 * side.length)) =
          n * (312 + 40 * K + 40 * side.length) := by ring
      rw [this]; exact Nat.mul_le_mul_left _ (by omega)
    omega
  · intro r h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11
    rw [hF6 r h3 h4 h5 h6 h7 h8 h9 h11, hL5 r h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11]

theorem aroundStep_first (t : Core) (v : Nat) (ns : Array Node) (T e : Nat) :
    ((aroundStep t v ns T).getX e).first = (ns.getX e).first := by
  simp only [aroundStep, getX_modify']; split <;> rfl

theorem fold_aroundStep_first (t : Core) (v e : Nat) : ∀ (l : List Nat) (ns : Array Node),
    ((l.foldl (aroundStep t v) ns).getX e).first = (ns.getX e).first
  | [], _ => rfl
  | T :: l, ns => by simp only [List.foldl_cons]; rw [fold_aroundStep_first t v e l, aroundStep_first]

theorem sd1_first (t : Core) (v e : Nat) : ((sd1 t v).nodes.getX e).first = (t.nodes.getX e).first := by
  simp only [sd1, getX_push', Array.size_push]
  split
  · rw [getX_size_le (by omega)]; rfl
  · split
    · rw [getX_size_le (by omega)]; rfl
    · rfl

theorem sd2_first (t : Core) (v e : Nat) : ((sd2 t v).nodes.getX e).first = (t.nodes.getX e).first := by
  rw [← sdJ_all]; simp only [sdJ]; rw [fold_aroundStep_first, sd1_first]

theorem sd2_getX_v {t : Core} {v : Nat} (hv : v < t.nodes.size) (hvT : v ∉ (t.nodes.getX v).inTables) :
    (sd2 t v).nodes.getX v = t.nodes.getX v := by
  rw [← sdJ_all]; exact sdJ_getX_notin (fun h => hvT (List.mem_of_mem_take h)) hv

theorem sd2_getX_new {t : Core} {v u : Nat} (hroom : ∀ T ∈ (t.nodes.getX v).inTables, RoomOK t v T)
    (hu : t.nodes.size ≤ u) (hu2 : u < t.nodes.size + 2) : (sd2 t v).nodes.getX u = { height := sH t v } := by
  rw [← sdJ_all]
  rw [sdJ_getX_notin' (fun h => by have := (hroom u (List.mem_of_mem_take h)).lt; omega)]
  simp only [sd1, getX_push', Array.size_push]
  by_cases e : u = t.nodes.size + 1
  · rw [if_pos e]
  · rw [if_neg e, if_pos (by omega)]

theorem ReadOK.of_sd2 {t : Core} {v : Nat} {side : List (Nat × Side)} (hv : v < t.nodes.size)
    (hvT : v ∉ (t.nodes.getX v).inTables) : ReadOK (phiS v side (sd2 t v)) t v side := by
  have hsz : v < (sd2 t v).nodes.size := by rw [← sdJ_all, sdJ_size]; omega
  refine ⟨?_, ?_, ?_, fun e => ?_⟩
  · rw [phiS_getX_self hsz, sd2_getX_v hv hvT]
  · rw [phiS_getX_self hsz, sd2_getX_v hv hvT]
  · rw [phiS_getX_self hsz]
  · by_cases h : e = v
    · subst h; rw [phiS_getX_self hsz, sd2_getX_v hv hvT]
    · rw [phiS_getX_ne h, sd2_first]

theorem ReadOK.put_inTab {St t : Core} {v w : Nat} {side : List (Nat × Side)} (hR : ReadOK St t v side)
    (hw : w ≠ v) (l : List (Nat × Nat)) : ReadOK (LK.put St w l .inTab) t v side := by
  have hg : ∀ u, u ≠ w → (LK.put St w l .inTab).nodes.getX u = St.nodes.getX u := by
    intro u hu; simp only [LK.put, getX_modify']; rw [if_neg (fun h => hu h.1)]
  have hf : ∀ u, ((LK.put St w l .inTab).nodes.getX u).first = (St.nodes.getX u).first := by
    intro u; simp only [LK.put, getX_modify']; split <;> rfl
  exact ⟨by rw [hg v (Ne.symm hw)]; exact hR.tab, by rw [hg v (Ne.symm hw)]; exact hR.kids,
    by rw [hg v (Ne.symm hw)]; exact hR.side, fun u => by rw [hf]; exact hR.first u⟩

/-- A new node `w` takes `v`'s tables and its share of `v`'s entries (side `sd`). -/
def newTabS : Stm := "a" ::= .var "v" ;; copyS .inTab ;; tabS

theorem newTabS_ok {κ : Caps} {St t : Core} {L : Loc} {v w : Nat} {side : List (Nat × Side)} {sd : Side}
    (hR : ReadOK St t v side) (hP : St.P = t.P) (hw0 : (St.nodes.getX w).table = [])
    (hw1 : (St.nodes.getX w).inTables = []) (hwv : w ≠ v) (hws : w < St.nodes.size)
    (hvi : (St.nodes.getX v).inTables = (t.nodes.getX v).inTables)
    (hLv : L "v" = v) (hLw : L "w" = w) (hLh : L "h" = sH t v) (hLs : L "sd" = sideN sd)
    (hvc : v < κ.lrec .children) (hvs : v < κ.lrec .side) (hvt : v < κ.lrec .table) (hwt : w < κ.lrec .table)
    (hvI : v < κ.lrec .inTab) (hwI : w < κ.lrec .inTab)
    (hN : ∀ e ∈ (t.nodes.getX v).table.map (·.1), e < κ.tbl .N)
    (hcap : (t.nodes.getX v).table.length ≤ κ.lcap .table)
    (hcapI : (t.nodes.getX v).inTables.length ≤ κ.lcap .inTab) :
    ∃ L' c, evalF κ newTabS St L = .ok (LK.put (LK.put St w ((t.nodes.getX v).inTables.map fun e => (e, 0)) .inTab)
        w (evenTable t.P.beta (part t v side sd)) .table) L' c ∧
      c ≤ 30 + 40 * (t.nodes.getX v).inTables.length + (t.nodes.getX v).table.length *
        (320 + 40 * (t.nodes.getX v).children.length + 40 * side.length) ∧
      ∀ r, r ≠ "a" → r ≠ "n" → r ≠ "j" → r ≠ "nt" → r ≠ "cnt" → r ≠ "e" → r ≠ "r" → r ≠ "m" → r ≠ "f" →
        r ≠ "x" → r ≠ "q" → r ≠ "st" → r ≠ "idx" → L' r = L r := by
  have a1 := evalF_assign_ok (κ := κ) (s := St) (L := L) (x := "a") (e := .var "v") (v := v) (by simp [Exp.ev, hLv])
  set L1 := upd L "a" v
  have hvw : LK.view St w .inTab = [] := by simp [LK.view, hw1]
  have hvv : LK.view St v .inTab = (t.nodes.getX v).inTables.map fun e => (e, 0) := by simp [LK.view, hvi]
  obtain ⟨L2, c2, e2, hc2, hF2⟩ := copyS_ok (κ := κ) (k := .inTab) (s := St) (L := L1) (a := v) (w := w)
    (by simp [L1, OM.Machine.State.upd]) (by simp [L1, OM.Machine.State.upd, hLw]) hwv
    (by simp [LK.idOk, LK.recOk, hws]) (by simp [LK.recOk, hws]) hvI hwI (by rw [hvw, hvv]; simpa using hcapI)
  rw [hvw, hvv, List.nil_append] at e2
  rw [hvv] at hc2
  set St1 := LK.put St w ((t.nodes.getX v).inTables.map fun e => (e, 0)) .inTab
  have hgw : St1.nodes.getX w = { St.nodes.getX w with inTables := (t.nodes.getX v).inTables } := by
    simp [St1, LK.put, getX_modify', hws, Function.comp_def]
  have hfr2 : ∀ r, r ≠ "a" → r ≠ "n" → r ≠ "j" → L2 r = L r := fun r h1 h2 h3 => by
    rw [hF2 r h2 h3]; simp [L1, OM.Machine.State.upd, h1]
  obtain ⟨L3, c3, e3, hc3, hF3⟩ := tabS_ok (κ := κ) (St := St1) (t := t) (L := L2) (v := v) (w := w) (side := side)
    (sd := sd) (hR.put_inTab hwv _) (by simp [St1, LK.put, hP]) (by rw [hgw]; exact hw0)
    hwv (by simp [St1, LK.put, hws])
    (by rw [hfr2 "v" (by decide) (by decide) (by decide), hLv])
    (by rw [hfr2 "w" (by decide) (by decide) (by decide), hLw])
    (by rw [hfr2 "h" (by decide) (by decide) (by decide), hLh])
    (by rw [hfr2 "sd" (by decide) (by decide) (by decide), hLs]) hvc hvs hvt hwt hN hcap
  refine ⟨L3, _, evalF_seq_ok2 a1 (evalF_seq_ok2 e2 e3), ?_, ?_⟩
  · simp only [List.length_map, Exp.cost] at hc2 hc3 ⊢; omega
  · intro r h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 h13
    rw [hF3 r h4 h5 h3 h6 h7 h8 h9 h10 h11 h12 h13, hfr2 r h1 h2 h3]

def stage3S : Stm :=
  "w" ::= .var "v1" ;; "sd" ::= 0 ;; newTabS ;; "w" ::= .var "v2" ;; "sd" ::= 1 ;; newTabS

theorem stage3_state (t : Core) (v : Nat) (side : List (Nat × Side)) (hv : v < t.nodes.size) :
    LK.put (LK.put (LK.put (LK.put (phiS v side (sd2 t v)) t.nodes.size
      ((t.nodes.getX v).inTables.map fun e => (e, 0)) .inTab) t.nodes.size
        (evenTable t.P.beta (part t v side .left)) .table) (t.nodes.size + 1)
      ((t.nodes.getX v).inTables.map fun e => (e, 0)) .inTab) (t.nodes.size + 1)
        (evenTable t.P.beta (part t v side .right)) .table = phiS v side (sd4 t v side) := by
  simp only [LK.put, phiS, sd4, Array.modify_modify_same, ← sLeft_part, ← sRight_part]
  rw [Array.modify_comm _ (show v ≠ t.nodes.size by omega), Array.modify_comm _ (show v ≠ t.nodes.size + 1 by omega)]
  simp only [Function.comp_def, List.map_map, List.map_id']

theorem put_getX_ne_t {St : Core} {w u : Nat} {l : List (Nat × Nat)} (h : u ≠ w) :
    (LK.put St w l .table).nodes.getX u = St.nodes.getX u := by
  simp only [LK.put, getX_modify']; rw [if_neg (fun e => h e.1)]

theorem put_getX_ne_i {St : Core} {w u : Nat} {l : List (Nat × Nat)} (h : u ≠ w) :
    (LK.put St w l .inTab).nodes.getX u = St.nodes.getX u := by
  simp only [LK.put, getX_modify']; rw [if_neg (fun e => h e.1)]

theorem stage3S_ok {κ : Caps} {t : Core} {L : Loc} {v : Nat} {side : List (Nat × Side)}
    (hv : v < t.nodes.size) (hvT : v ∉ (t.nodes.getX v).inTables)
    (hroom : ∀ T ∈ (t.nodes.getX v).inTables, RoomOK t v T)
    (hLv : L "v" = v) (hLv1 : L "v1" = t.nodes.size) (hLv2 : L "v2" = t.nodes.size + 1) (hLh : L "h" = sH t v)
    (hvc : v < κ.lrec .children) (hvs : v < κ.lrec .side) (hvt : v < κ.lrec .table)
    (hwt : t.nodes.size + 1 < κ.lrec .table) (hvI : v < κ.lrec .inTab) (hwI : t.nodes.size + 1 < κ.lrec .inTab)
    (hN : ∀ e ∈ (t.nodes.getX v).table.map (·.1), e < κ.tbl .N)
    (hcap : (t.nodes.getX v).table.length ≤ κ.lcap .table)
    (hcapI : (t.nodes.getX v).inTables.length ≤ κ.lcap .inTab) :
    ∃ L' c, evalF κ stage3S (phiS v side (sd2 t v)) L = .ok (phiS v side (sd4 t v side)) L' c ∧
      c ≤ 70 + 80 * (t.nodes.getX v).inTables.length + 2 * ((t.nodes.getX v).table.length *
        (320 + 40 * (t.nodes.getX v).children.length + 40 * side.length)) ∧
      ∀ r, r ≠ "w" → r ≠ "sd" → r ≠ "a" → r ≠ "n" → r ≠ "j" → r ≠ "nt" → r ≠ "cnt" → r ≠ "e" → r ≠ "r" →
        r ≠ "m" → r ≠ "f" → r ≠ "x" → r ≠ "q" → r ≠ "st" → r ≠ "idx" → L' r = L r := by
  set N := t.nodes.size
  set S2 := phiS v side (sd2 t v)
  have hS2sz : S2.nodes.size = N + 2 := by simp [S2, phiS, ← sdJ_all, sdJ_size, N]
  have hNv : N ≠ v := by omega
  have hN1v : N + 1 ≠ v := by omega
  have hS2N : S2.nodes.getX N = { height := sH t v } := by
    rw [phiS_getX_ne hNv, sd2_getX_new hroom le_rfl (by omega)]
  have hS2N1 : S2.nodes.getX (N + 1) = { height := sH t v } := by
    rw [phiS_getX_ne hN1v, sd2_getX_new hroom (by omega) (by omega)]
  have hS2v : (S2.nodes.getX v).inTables = (t.nodes.getX v).inTables := by
    rw [phiS_getX_self (by rw [← sdJ_all, sdJ_size]; omega), sd2_getX_v hv hvT]
  have a1 := evalF_assign_ok (κ := κ) (s := S2) (L := L) (x := "w") (e := .var "v1") (v := N) (by simp [Exp.ev, hLv1])
  have a2 := evalF_assign_ok (κ := κ) (s := S2) (L := upd L "w" N) (x := "sd") (e := (0 : Exp)) (v := 0) rfl
  set L2 := upd (upd L "w" N) "sd" 0
  have hL2 : ∀ r, r ≠ "w" → r ≠ "sd" → L2 r = L r := fun r h1 h2 => by simp [L2, OM.Machine.State.upd, h1, h2]
  obtain ⟨L3, c3, e3, hc3, hF3⟩ := newTabS_ok (κ := κ) (St := S2) (t := t) (L := L2) (v := v) (w := N) (side := side)
    (sd := .left) (ReadOK.of_sd2 hv hvT) rfl (by rw [hS2N]) (by rw [hS2N]) hNv (by omega) hS2v
    (by rw [hL2 "v" (by decide) (by decide), hLv]) (by simp [L2, OM.Machine.State.upd])
    (by rw [hL2 "h" (by decide) (by decide), hLh]) (by simp [L2, OM.Machine.State.upd, sideN]) hvc hvs hvt
    (by omega) hvI (by omega) hN hcap hcapI
  set X1 := LK.put (LK.put S2 N ((t.nodes.getX v).inTables.map fun e => (e, 0)) .inTab) N
    (evenTable t.P.beta (part t v side .left)) .table
  have hX1N1 : X1.nodes.getX (N + 1) = { height := sH t v } := by
    rw [put_getX_ne_t (by omega), put_getX_ne_i (by omega), hS2N1]
  have hX1v : (X1.nodes.getX v).inTables = (t.nodes.getX v).inTables := by
    rw [put_getX_ne_t (Ne.symm hNv), put_getX_ne_i (Ne.symm hNv), hS2v]
  have hfr3 : ∀ r, r ≠ "w" → r ≠ "sd" → r ≠ "a" → r ≠ "n" → r ≠ "j" → r ≠ "nt" → r ≠ "cnt" → r ≠ "e" → r ≠ "r" →
      r ≠ "m" → r ≠ "f" → r ≠ "x" → r ≠ "q" → r ≠ "st" → r ≠ "idx" → L3 r = L r := by
    intro r h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 h13 h14 h15
    rw [hF3 r h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 h13 h14 h15, hL2 r h1 h2]
  have a3 := evalF_assign_ok (κ := κ) (s := X1) (L := L3) (x := "w") (e := .var "v2") (v := N + 1)
    (by simp [Exp.ev, hfr3 "v2" (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), hLv2])
  have a4 := evalF_assign_ok (κ := κ) (s := X1) (L := upd L3 "w" (N + 1)) (x := "sd") (e := (1 : Exp)) (v := 1) rfl
  set L4 := upd (upd L3 "w" (N + 1)) "sd" 1
  have hL4 : ∀ r, r ≠ "w" → r ≠ "sd" → r ≠ "a" → r ≠ "n" → r ≠ "j" → r ≠ "nt" → r ≠ "cnt" → r ≠ "e" → r ≠ "r" →
      r ≠ "m" → r ≠ "f" → r ≠ "x" → r ≠ "q" → r ≠ "st" → r ≠ "idx" → L4 r = L r := by
    intro r h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 h13 h14 h15
    simp only [L4, OM.Machine.State.upd, if_neg h1, if_neg h2]
    exact hfr3 r h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 h13 h14 h15
  obtain ⟨L5, c5, e5, hc5, hF5⟩ := newTabS_ok (κ := κ) (St := X1) (t := t) (L := L4) (v := v) (w := N + 1)
    (side := side) (sd := .right) (((ReadOK.of_sd2 hv hvT).put_inTab hNv _).put_table hNv _) (by simp [X1, LK.put, S2, phiS]; rfl)
    (by rw [hX1N1]) (by rw [hX1N1]) hN1v (by simp [X1, LK.put, hS2sz]) hX1v
    (by rw [hL4 "v" (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), hLv])
    (by simp [L4, OM.Machine.State.upd])
    (by rw [hL4 "h" (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), hLh])
    (by simp [L4, OM.Machine.State.upd, sideN]) hvc hvs hvt hwt hvI hwI hN hcap hcapI
  rw [stage3_state t v side hv] at e5
  refine ⟨L5, _, evalF_seq_ok2 a1 (evalF_seq_ok2 a2 (evalF_seq_ok2 e3 (evalF_seq_ok2 a3 (evalF_seq_ok2 a4 e5)))),
    ?_, ?_⟩
  · simp only [Exp.cost] at hc3 hc5 ⊢; omega
  · intro r h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 h13 h14 h15
    rw [hF5 r h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 h13 h14 h15, hL4 r h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 h13 h14 h15]

end OM.Impl
