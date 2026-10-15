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

end OM.Impl
