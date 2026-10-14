import OM.Proof.Cost.GSteps

/-!
# Split moves and group removal
-/

namespace OM.Proof

open OM.Model

set_option linter.deprecated false

/-! ### Split moves -/

section moves
variable (s : Core) (p : Nat)

/-- The label of the element moved to the left sibling. -/
def labMoveL : Nat :=
  if gF s (gLl s p) = NIL then cE s.P else eL s (gLs s (gLl s p)) + s.P.D_e

/-- The label of the element moved to the right sibling. -/
def labMoveR : Nat :=
  if gF s (gRr s p) = NIL then cE s.P else eL s (gF s (gRr s p)) - s.P.D_e

def sizeAdj (s : Core) (a b : Nat) : Core :=
  let s2 := { s with Gs := s.Gs.modify a fun X => { X with size := X.size - 1 } }
  { s2 with Gs := s2.Gs.modify b fun X => { X with size := X.size + 1 } }

/-- The state after moving the first element of `p` to its left sibling. -/
def moveLState : Core :=
  sizeAdj (moveFirstLeft s p (gLl s p) (gF s p) (labMoveL s p)) p (gLl s p)

/-- The state after moving the last element of `p` to its right sibling. -/
def moveRState : Core :=
  sizeAdj (moveLastRight s p (gRr s p) (gLs s p) (labMoveR s p)) p (gRr s p)

end moves

/-- What a successful left move needs: `p` alive and non-empty, the left sibling lighter and
adjacent, and room for a pushed label. -/
structure MoveLOK (s : Core) (p : Nat) : Prop where
  live : LiveG s p
  ne : gF s p ≠ NIL
  dir : gSz s (gLl s p) ≤ gSz s (gRr s p)
  adj : gN s (gLl s p) = p
  room : gF s (gLl s p) ≠ NIL → eL s (gLs s (gLl s p)) + s.P.D_e < 1 <<< s.P.B_e
  D : 0 < s.P.D_e
  chk : gC s (gLl s p) = gC s p

structure MoveROK (s : Core) (p : Nat) : Prop where
  live : LiveG s p
  ne : gF s p ≠ NIL
  dir : gSz s (gRr s p) < gSz s (gLl s p)
  adj : gP s (gRr s p) = p
  room : gF s (gRr s p) ≠ NIL → s.P.D_e ≤ eL s (gF s (gRr s p))
  D : 0 < s.P.D_e
  chk : gC s (gRr s p) = gC s p

theorem getX_modify_chk (a : Array Group) (i j : Nat) (f : Group → Group)
    (hf : ∀ X, (f X).chk = X.chk) : ((a.modify i f).getX j).chk = (a.getX j).chk := by
  rw [Array.getX_modify]
  by_cases h : i = j ∧ i < a.size
  · rw [if_pos h, hf]
  · rw [if_neg h]

/-- `groupSplitStep` after a successful move into a sibling in the same chunk. -/
theorem groupSplitStep_tail {s s1 : Core} {p d : Nat} (hm : (moveElem p).run s = .ok d s1)
    (hne : gF s p ≠ NIL) (hc : (p != NIL && decide (p < s.Gs.size) && (s.Gs.getX p).alive) = true)
    (hchk : (s1.Gs.getX d).chk = (s.Gs.getX p).chk) :
    (groupSplitStep p).run s = .ok true (sizeAdj s1 p d) := by
  unfold groupSplitStep
  rw [run_getG_bind, run_get_bind, run_require_bind, if_pos hc,
    if_neg (fun h => hne (beq_iff_eq.mp h)), run_bind, hm]
  dsimp only
  unfold modG
  rw [run_modify_bind, run_modify_bind, run_getG_bind]
  rw [getX_modify_chk _ _ _ (fun X => { X with size := X.size + 1 }) (fun _ => rfl),
    getX_modify_chk _ _ _ (fun X => { X with size := X.size - 1 }) (fun _ => rfl), hchk]
  rw [bne_self_eq_false, if_neg Bool.false_ne_true]
  rfl

theorem moveElem_left {s : Core} {p : Nat} (h : MoveLOK s p) :
    (moveElem p).run s = .ok (gLl s p) (moveFirstLeft s p (gLl s p) (gF s p) (labMoveL s p)) := by
  obtain ⟨⟨h0, hs, ha⟩, hne, hdir, hadj, hroom, hD, -⟩ := h
  unfold moveElem
  simp only [run_getP_bind, run_getG_bind, run_get_bind, run_require_bind]
  have hc' : (p != NIL && decide (p < s.Gs.size) && (s.Gs.getX p).alive &&
      (s.Gs.getX p).first != NIL) = true := by
    simp only [Bool.and_eq_true, bne_iff_ne, ne_eq, decide_eq_true_eq]
    exact ⟨⟨⟨h0, hs⟩, ha⟩, hne⟩
  rw [if_pos hc', if_pos hdir, run_require_bind, if_pos (beq_iff_eq.mpr hadj)]
  unfold labMoveL
  by_cases he : gF s (gLl s p) = NIL
  · rw [if_pos (beq_iff_eq.mpr he), if_pos he]; simp [cE]
  · rw [if_neg (fun h => he (beq_iff_eq.mp h)), if_neg he]
    simp only [run_getE_bind]
    rw [run_bind, run_after]
    have := hroom he
    simp only [eL, gLs, gLl, gF] at this he ⊢
    rw [if_neg (by omega)]
    simp

theorem moveElem_right {s : Core} {p : Nat} (h : MoveROK s p) :
    (moveElem p).run s = .ok (gRr s p) (moveLastRight s p (gRr s p) (gLs s p) (labMoveR s p)) := by
  obtain ⟨⟨h0, hs, ha⟩, hne, hdir, hadj, hroom, hD, -⟩ := h
  unfold moveElem
  simp only [run_getP_bind, run_getG_bind, run_get_bind, run_require_bind]
  have hc' : (p != NIL && decide (p < s.Gs.size) && (s.Gs.getX p).alive &&
      (s.Gs.getX p).first != NIL) = true := by
    simp only [Bool.and_eq_true, bne_iff_ne, ne_eq, decide_eq_true_eq]
    exact ⟨⟨⟨h0, hs⟩, ha⟩, hne⟩
  rw [if_pos hc', if_neg (by simp only [gSz, gLl, gRr] at hdir ⊢; omega), run_require_bind,
    if_pos (beq_iff_eq.mpr hadj)]
  unfold labMoveR
  by_cases he : gF s (gRr s p) = NIL
  · rw [if_pos (beq_iff_eq.mpr he), if_pos he]; simp [cE]
  · rw [if_neg (fun h => he (beq_iff_eq.mp h)), if_neg he]
    simp only [run_getE_bind]
    rw [run_bind, run_before]
    have := hroom he
    simp only [eL, gF, gRr] at this he ⊢
    rw [if_neg (by omega)]
    simp

theorem LiveG.cond {s : Core} {p : Nat} (h : LiveG s p) :
    (p != NIL && decide (p < s.Gs.size) && (s.Gs.getX p).alive) = true := by
  obtain ⟨h0, hs, ha⟩ := h
  simp only [Bool.and_eq_true, bne_iff_ne, ne_eq, decide_eq_true_eq]; exact ⟨⟨h0, hs⟩, ha⟩

theorem groupSplitStep_left {s : Core} {p : Nat} (h : MoveLOK s p) :
    (groupSplitStep p).run s = .ok true (moveLState s p) := by
  refine groupSplitStep_tail (moveElem_left h) h.ne h.live.cond ?_
  have := (moveFirstLeft_same (s := s) (g := p) (gl := gLl s p) (e := gF s p)
    (lab := labMoveL s p)).2.2.1 (gLl s p)
  have hc := h.chk
  simp only [gC] at this hc
  rw [this, hc]

theorem groupSplitStep_right {s : Core} {p : Nat} (h : MoveROK s p) :
    (groupSplitStep p).run s = .ok true (moveRState s p) := by
  refine groupSplitStep_tail (moveElem_right h) h.ne h.live.cond ?_
  have := (moveLastRight_same (s := s) (g := p) (gr := gRr s p) (e := gLs s p)
    (lab := labMoveR s p)).2.2.1 (gRr s p)
  have hc := h.chk
  simp only [gC] at this hc
  rw [this, hc]

def quietG (X : Group) : Group := { X with st := .quiet, src := NIL }

def removeState (s : Core) (p : Nat) : Core :=
  let s1 := unlinkGroup s p
  let s2 := { s1 with Gs := s1.Gs.modify (gLl s p) quietG }
  { s2 with Gs := s2.Gs.modify (gRr s p) quietG }

theorem unlinkGroup_getX_lr (s : Core) (p z : Nat) :
    ((unlinkGroup s p).Gs.getX z).l = (s.Gs.getX z).l ∧ ((unlinkGroup s p).Gs.getX z).r = (s.Gs.getX z).r ∧
    ((unlinkGroup s p).Gs.getX z).st = (s.Gs.getX z).st ∧ ((unlinkGroup s p).Gs.getX z).src = (s.Gs.getX z).src ∧
    ((unlinkGroup s p).Gs.getX z).size = (s.Gs.getX z).size ∧ (unlinkGroup s p).P = s.P := by
  refine ⟨?_, ?_, ?_, ?_, ?_, rfl⟩ <;>
    simp only [unlinkGroup, Array.getX_modify, Array.getX_ite, Array.size_modify', Array.size_ite] <;>
    split_ifs <;> rfl

@[simp] theorem run_getG' (i : Nat) (s : Core) : (getG i).run s = .ok (s.Gs.getX i) s := rfl
@[simp] theorem run_getP' (s : Core) : (getP).run s = .ok s.P s := rfl

theorem removeGroup_ok {s : Core} {p : Nat} (hp : LiveG s p) (he : gF s p = NIL)
    (hlr : gLl s p ≠ gRr s p)
    (hl : gSt s (gLl s p) = .overflow ∧ gSrc s (gLl s p) = p)
    (hr : gSt s (gRr s p) = .overflow ∧ gSrc s (gRr s p) = p)
    (hszl : gSz s (gLl s p) < s.P.G) (hszr : gSz s (gRr s p) < s.P.G) :
    (removeGroup p).run s = .ok () (removeState s p) := by
  obtain ⟨h0, hs, ha⟩ := hp
  unfold removeGroup
  have hu : (unlinkStep p).run s = .ok () (unlinkGroup s p) := by
    rcases unlinkStep_run s p with ⟨-, -, -, -, h⟩ | ⟨msg, h⟩
    · exact h
    · exfalso; revert h; unfold unlinkStep
      simp only [run_getG_bind, run_get_bind, run_require_bind]
      rw [if_pos (by simp only [Bool.and_eq_true, bne_iff_ne, ne_eq, decide_eq_true_eq, beq_iff_eq]; exact ⟨⟨⟨h0, hs⟩, ha⟩, he⟩)]
      simp
  rw [run_bind, hu]
  dsimp only
  obtain ⟨u1, u2, -, -, -, uP⟩ := unlinkGroup_getX_lr s p p
  obtain ⟨-, -, l3, l4, l5, -⟩ := unlinkGroup_getX_lr s p (gLl s p)
  obtain ⟨-, -, r3, r4, r5, -⟩ := unlinkGroup_getX_lr s p (gRr s p)
  simp only [gLl, gRr, gSt, gSrc, gSz] at l3 l4 l5 r3 r4 r5 hl hr hlr hszl hszr
  have nl : ¬ s.P.G ≤ (s.Gs.getX (s.Gs.getX p).l).size := by omega
  have nr : ¬ s.P.G ≤ (s.Gs.getX (s.Gs.getX p).r).size := by omega
  simp [modG, Array.getX_modify, u1, u2, l3, l4, l5, r3, r4, r5, hl, hr, hlr, Ne.symm hlr, uP,
    List.forIn_cons, apply_ite (f := Group.size), nl, nr]
  rfl

theorem groupSplitStep_remove {s : Core} {p : Nat} (hp : LiveG s p) (he : gF s p = NIL)
    (hlr : gLl s p ≠ gRr s p)
    (hl : gSt s (gLl s p) = .overflow ∧ gSrc s (gLl s p) = p)
    (hr : gSt s (gRr s p) = .overflow ∧ gSrc s (gRr s p) = p)
    (hszl : gSz s (gLl s p) < s.P.G) (hszr : gSz s (gRr s p) < s.P.G) :
    (groupSplitStep p).run s = .ok false (removeState s p) := by
  unfold groupSplitStep
  rw [run_getG_bind, run_get_bind, run_require_bind, if_pos hp.cond, if_pos (beq_iff_eq.mpr he),
    run_bind, removeGroup_ok hp he hlr hl hr hszl hszr]
  rfl

end OM.Proof

namespace OM.Proof

open OM.Model

set_option linter.deprecated false

/-! ### Runs of adjacent groups -/

/-- Two adjacent groups' runs are adjacent in the element list. -/
theorem INV.runs_adj {s : Core} {A : Abs} (hI : INV s A) {l p : Nat} (hl : l ∈ A.glist)
    (hadj : gN s l = p) (hp0 : p ≠ NIL) :
    ∃ X Y, A.elist = X ++ runOf s A.elist l ++ runOf s A.elist p ++ Y ∧
      ∀ z ∈ X ++ Y, eG s z ≠ l ∧ eG s z ≠ p := by
  have hnd := hI.gList.nodup
  obtain ⟨g1, g2, e⟩ := succOf_split ((hI.gList.next l hl).symm.trans hadj) hp0
  refine ⟨(g1.map (runOf s A.elist)).flatten, (g2.map (runOf s A.elist)).flatten, ?_, ?_⟩
  · conv_lhs => rw [hI.elist_runs, e]
    simp
  · rw [e] at hnd
    have hd := (List.nodup_append.mp hnd)
    have hl1 : l ∉ g1 := fun h => hd.2.2 l h l (by simp) rfl
    have hp1 : p ∉ g1 := fun h => hd.2.2 p h p (by simp) rfl
    have h2 := List.nodup_cons.mp (List.nodup_cons.mp hd.2.1).2
    have hl2 : l ∉ g2 := fun h => (List.nodup_cons.mp hd.2.1).1 (by simp [h])
    have hp2 : p ∉ g2 := h2.1
    intro z hz
    simp only [List.mem_append, List.mem_flatten, List.mem_map] at hz
    rcases hz with ⟨_, ⟨b, hb, rfl⟩, hzb⟩ | ⟨_, ⟨b, hb, rfl⟩, hzb⟩
    · rw [(mem_runOf.mp hzb).2]
      exact ⟨fun h => hl1 (h ▸ hb), fun h => hp1 (h ▸ hb)⟩
    · rw [(mem_runOf.mp hzb).2]
      exact ⟨fun h => hl2 (h ▸ hb), fun h => hp2 (h ▸ hb)⟩

theorem filter_nil_of {p : Nat → Bool} {L : List Nat} (h : ∀ z ∈ L, p z = false) :
    L.filter p = [] := List.filter_eq_nil_iff.mpr fun z hz => by simp [h z hz]

theorem nodup_mid {A B : List Nat} {e : Nat} (h : (A ++ e :: B).Nodup) : e ∉ A ∧ e ∉ B :=
  ⟨fun hA => (List.nodup_append.mp h).2.2 e hA e (by simp) rfl,
   (List.nodup_cons.mp (List.nodup_append.mp h).2.1).1⟩

/-- Moving element `e` from the front of `p`'s run to the end of the adjacent `l`'s run. -/
theorem runOf_moveFront {s s' : Core} {L X Y rest : List Nat} {l p e : Nat}
    (hL : L = X ++ runOf s L l ++ (e :: rest) ++ Y)
    (hXY : ∀ z ∈ X ++ Y, eG s z ≠ l ∧ eG s z ≠ p) (hrest : ∀ z ∈ rest, eG s z = p)
    (hRl : ∀ z ∈ runOf s L l, eG s z = l) (he : eG s e = p) (hlp : l ≠ p)
    (hnd : L.Nodup) (heG : ∀ z, eG s' z = if z = e then l else eG s z) (b : Nat) :
    runOf s' L b = if b = l then runOf s L l ++ [e] else if b = p then rest else runOf s L b := by
  generalize hR : runOf s L l = R at hL hRl
  have hnd' := hnd
  rw [hL, show X ++ R ++ e :: rest ++ Y = (X ++ R) ++ e :: (rest ++ Y) by simp] at hnd'
  obtain ⟨h1, h2⟩ := nodup_mid hnd'
  simp only [List.mem_append, not_or] at h1 h2
  have hfilt : ∀ {M : List Nat} (q : Nat), e ∉ M →
      M.filter (fun z => decide (eG s' z = q)) = M.filter (fun z => decide (eG s z = q)) := by
    intro M q hM
    exact List.filter_congr fun z hz => by rw [heG, if_neg (fun (h : z = e) => hM (h ▸ hz))]
  unfold runOf
  rw [hL]
  simp only [List.filter_append, List.filter_cons]
  rw [hfilt b h1.1, hfilt b h1.2, hfilt b h2.1, hfilt b h2.2, heG, if_pos rfl]
  have hXn : ∀ q, q = l ∨ q = p → X.filter (fun z => decide (eG s z = q)) = [] := by
    intro q hq; refine filter_nil_of fun z hz => ?_
    have := hXY z (by simp [hz]); rcases hq with rfl | rfl <;> simp [this.1, this.2]
  have hYn : ∀ q, q = l ∨ q = p → Y.filter (fun z => decide (eG s z = q)) = [] := by
    intro q hq; refine filter_nil_of fun z hz => ?_
    have := hXY z (by simp [hz]); rcases hq with rfl | rfl <;> simp [this.1, this.2]
  by_cases hbl : b = l
  · subst hbl
    have hRe : R.filter (fun z => decide (eG s z = b)) = R :=
      List.filter_eq_self.mpr fun z hz => by simp [hRl z hz]
    have hrn : rest.filter (fun z => decide (eG s z = b)) = [] :=
      filter_nil_of fun z hz => by simp [hrest z hz, Ne.symm hlp]
    rw [hXn b (Or.inl rfl), hYn b (Or.inl rfl), hRe, hrn]
    simp
  · by_cases hbp : b = p
    · subst hbp
      have hRn : R.filter (fun z => decide (eG s z = b)) = [] :=
        filter_nil_of fun z hz => by simp [hRl z hz, hlp]
      have hre : rest.filter (fun z => decide (eG s z = b)) = rest :=
        List.filter_eq_self.mpr fun z hz => by simp [hrest z hz]
      rw [hXn b (Or.inr rfl), hYn b (Or.inr rfl), hRn, hre]
      simp [hlp, Ne.symm hlp]
    · simp only [if_neg hbl, if_neg hbp, he, Ne.symm hbl, Ne.symm hbp, decide_false]

/-- Moving element `e` from the back of `p`'s run to the front of the adjacent `r`'s run. -/
theorem runOf_moveBack {s s' : Core} {L X Y front : List Nat} {p r e : Nat}
    (hL : L = X ++ (front ++ [e]) ++ runOf s L r ++ Y)
    (hXY : ∀ z ∈ X ++ Y, eG s z ≠ p ∧ eG s z ≠ r) (hfront : ∀ z ∈ front, eG s z = p)
    (hRr : ∀ z ∈ runOf s L r, eG s z = r) (he : eG s e = p) (hpr : p ≠ r)
    (hnd : L.Nodup) (heG : ∀ z, eG s' z = if z = e then r else eG s z) (b : Nat) :
    runOf s' L b = if b = r then e :: runOf s L r else if b = p then front else runOf s L b := by
  generalize hR : runOf s L r = R at hL hRr
  have hnd' := hnd
  rw [hL, show X ++ (front ++ [e]) ++ R ++ Y = (X ++ front) ++ e :: (R ++ Y) by simp] at hnd'
  obtain ⟨h1, h2⟩ := nodup_mid hnd'
  simp only [List.mem_append, not_or] at h1 h2
  have hfilt : ∀ {M : List Nat} (q : Nat), e ∉ M →
      M.filter (fun z => decide (eG s' z = q)) = M.filter (fun z => decide (eG s z = q)) := by
    intro M q hM
    exact List.filter_congr fun z hz => by rw [heG, if_neg (fun (h : z = e) => hM (h ▸ hz))]
  unfold runOf
  rw [hL]
  simp only [List.filter_append, List.filter_cons, List.filter_nil]
  rw [hfilt b h1.1, hfilt b h1.2, hfilt b h2.1, hfilt b h2.2, heG, if_pos rfl]
  have hXn : ∀ q, q = p ∨ q = r → X.filter (fun z => decide (eG s z = q)) = [] := by
    intro q hq; refine filter_nil_of fun z hz => ?_
    have := hXY z (by simp [hz]); rcases hq with rfl | rfl <;> simp [this.1, this.2]
  have hYn : ∀ q, q = p ∨ q = r → Y.filter (fun z => decide (eG s z = q)) = [] := by
    intro q hq; refine filter_nil_of fun z hz => ?_
    have := hXY z (by simp [hz]); rcases hq with rfl | rfl <;> simp [this.1, this.2]
  by_cases hbr : b = r
  · subst hbr
    have hfn : front.filter (fun z => decide (eG s z = b)) = [] :=
      filter_nil_of fun z hz => by simp [hfront z hz, hpr]
    have hRe : R.filter (fun z => decide (eG s z = b)) = R :=
      List.filter_eq_self.mpr fun z hz => by simp [hRr z hz]
    rw [hXn b (Or.inr rfl), hYn b (Or.inr rfl), hfn, hRe]
    simp
  · by_cases hbp : b = p
    · subst hbp
      have hfe : front.filter (fun z => decide (eG s z = b)) = front :=
        List.filter_eq_self.mpr fun z hz => by simp [hfront z hz]
      have hRn : R.filter (fun z => decide (eG s z = b)) = [] :=
        filter_nil_of fun z hz => by simp [hRr z hz, Ne.symm hpr]
      rw [hXn b (Or.inl rfl), hYn b (Or.inl rfl), hfe, hRn]
      simp [hpr, Ne.symm hpr]
    · simp only [if_neg hbr, if_neg hbp, he, Ne.symm hbr, Ne.symm hbp, decide_false]

end OM.Proof

namespace OM.Proof

open OM.Model

set_option linter.deprecated false

/-! ### The records after a move -/

theorem sizeAdj_getX (t : Core) (a b z : Nat) (hab : a ≠ b) (ha : a < t.Gs.size) (hb : b < t.Gs.size) :
    (sizeAdj t a b).Gs.getX z =
      if z = a then { t.Gs.getX z with size := (t.Gs.getX z).size - 1 }
      else if z = b then { t.Gs.getX z with size := (t.Gs.getX z).size + 1 } else t.Gs.getX z := by
  simp only [sizeAdj, Array.getX_modify, Array.size_modify']
  by_cases h1 : z = a
  · subst h1; simp [ha, hab, Ne.symm hab]
  · by_cases h2 : z = b
    · subst h2; simp [hb, h1, Ne.symm h1]
    · simp [h1, h2, Ne.symm h1, Ne.symm h2]

theorem moveFirstLeft_fields (s : Core) (g gl e lab z : Nat) :
    gSt (moveFirstLeft s g gl e lab) z = gSt s z ∧ gSrc (moveFirstLeft s g gl e lab) z = gSrc s z ∧
    gLl (moveFirstLeft s g gl e lab) z = gLl s z ∧ gRr (moveFirstLeft s g gl e lab) z = gRr s z ∧
    gSz (moveFirstLeft s g gl e lab) z = gSz s z := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;>
    simp only [moveFirstLeft, gSt, gSrc, gLl, gRr, gSz, Array.getX_modify, Array.size_modify'] <;>
    split_ifs <;> simp_all

theorem moveLastRight_fields (s : Core) (g gr e lab z : Nat) :
    gSt (moveLastRight s g gr e lab) z = gSt s z ∧ gSrc (moveLastRight s g gr e lab) z = gSrc s z ∧
    gLl (moveLastRight s g gr e lab) z = gLl s z ∧ gRr (moveLastRight s g gr e lab) z = gRr s z ∧
    gSz (moveLastRight s g gr e lab) z = gSz s z := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;>
    simp only [moveLastRight, gSt, gSrc, gLl, gRr, gSz, Array.getX_modify, Array.size_modify'] <;>
    split_ifs <;> simp_all

/-- What a move does to the fields the cost invariants read. -/
structure MoveSpec (s s' : Core) (src dst e lab : Nat) : Prop where
  links : GLinks s s'
  sz : ∀ z, gSz s' z = if z = src then gSz s src - 1 else if z = dst then gSz s dst + 1 else gSz s z
  eG : ∀ z, eG s' z = if z = e then dst else eG s z
  eL : ∀ z, eL s' z = if z = e then lab else eL s z
  head : s'.head = s.head
  P : s'.P = s.P
  E : s'.E.size = s.E.size ∧ (∀ z, eN s' z = eN s z) ∧ (∀ z, eP s' z = eP s z) ∧
    (∀ z, (s'.E.getX z).live = (s.E.getX z).live) ∧ (∀ z, (s'.E.getX z).h = (s.E.getX z).h)
  tail : s'.tail = s.tail
  C : s'.C = s.C

theorem moveLState_spec {s : Core} {p : Nat} (hlp : gLl s p ≠ p) (hp : p < s.Gs.size)
    (hl : gLl s p < s.Gs.size) (he : gF s p < s.E.size) :
    MoveSpec s (moveLState s p) p (gLl s p) (gF s p) (labMoveL s p) := by
  obtain ⟨sN, sP, sC, sL, sA, sGs, seN, seP, sLive, sH, sEs, sCC, sF, sHd, sT, sFG, sFC⟩ :=
    moveFirstLeft_same (s := s) (g := p) (gl := gLl s p) (e := gF s p) (lab := labMoveL s p)
  have hGs : ∀ z, (moveLState s p).Gs.getX z = _ := fun z =>
    sizeAdj_getX (moveFirstLeft s p (gLl s p) (gF s p) (labMoveL s p)) p (gLl s p) z
      (Ne.symm hlp) (by rw [sGs]; exact hp) (by rw [sGs]; exact hl)
  have F := moveFirstLeft_fields s p (gLl s p) (gF s p) (labMoveL s p)
  have fld : ∀ {β : Type} (f : Group → β), (∀ X v, f { X with size := v } = f X) →
      ∀ z, f ((moveLState s p).Gs.getX z) = f ((moveFirstLeft s p (gLl s p) (gF s p) (labMoveL s p)).Gs.getX z) := by
    intro β f hf z; rw [hGs z]; split_ifs <;> simp [hf]
  refine ⟨⟨by simp [moveLState, sizeAdj, sGs], fun z => ?_, fun z => ?_, fun z => ?_, fun z => ?_,
    fun z => ?_, fun z => ?_, fun z => ?_⟩, fun z => ?_, fun z => ?_, fun z => ?_, sHd, rfl,
    ⟨sEs, seN, seP, sLive, sH⟩, sT, sCC⟩
  · show (_ : Group).st = _; rw [fld Group.st (fun _ _ => rfl)]; exact (F z).1
  · show (_ : Group).src = _; rw [fld Group.src (fun _ _ => rfl)]; exact (F z).2.1
  · show (_ : Group).l = _; rw [fld Group.l (fun _ _ => rfl)]; exact (F z).2.2.1
  · show (_ : Group).r = _; rw [fld Group.r (fun _ _ => rfl)]; exact (F z).2.2.2.1
  · show (_ : Group).next = _; rw [fld Group.next (fun _ _ => rfl)]; exact sN z
  · show (_ : Group).chk = _; rw [fld Group.chk (fun _ _ => rfl)]; exact sC z
  · show (_ : Group).alive = _; rw [fld Group.alive (fun _ _ => rfl)]; exact sA z
  · show (_ : Group).size = _
    rw [hGs z]
    have := (F z).2.2.2.2; simp only [gSz] at this
    by_cases h1 : z = p
    · subst h1; simp [this]
    · by_cases h2 : z = gLl s p
      · subst h2; simp [h1, this]
      · simp [h1, h2, this]
  · show ((moveLState s p).E.getX z).grp = _
    have := moveFirstLeft_eG (s := s) (g := p) (gl := gLl s p) (e := gF s p) (lab := labMoveL s p) z
    simp only [eG] at this
    simp only [moveLState, sizeAdj]
    rw [this]; simp [he]
  · show ((moveLState s p).E.getX z).lab = _
    have := moveFirstLeft_eL (s := s) (g := p) (gl := gLl s p) (e := gF s p) (lab := labMoveL s p) z
    simp only [eL] at this
    simp only [moveLState, sizeAdj]
    rw [this]; simp [he]

theorem moveRState_spec {s : Core} {p : Nat} (hrp : gRr s p ≠ p) (hp : p < s.Gs.size)
    (hr : gRr s p < s.Gs.size) (he : gLs s p < s.E.size) :
    MoveSpec s (moveRState s p) p (gRr s p) (gLs s p) (labMoveR s p) := by
  obtain ⟨sN, sP, sC, sL, sA, sGs, seN, seP, sLive, sH, sEs, sCC, sF, sHd, sT, sFG, sFC⟩ :=
    moveLastRight_same (s := s) (g := p) (gr := gRr s p) (e := gLs s p) (lab := labMoveR s p)
  have hGs : ∀ z, (moveRState s p).Gs.getX z = _ := fun z =>
    sizeAdj_getX (moveLastRight s p (gRr s p) (gLs s p) (labMoveR s p)) p (gRr s p) z
      (Ne.symm hrp) (by rw [sGs]; exact hp) (by rw [sGs]; exact hr)
  have F := moveLastRight_fields s p (gRr s p) (gLs s p) (labMoveR s p)
  have fld : ∀ {β : Type} (f : Group → β), (∀ X v, f { X with size := v } = f X) →
      ∀ z, f ((moveRState s p).Gs.getX z) = f ((moveLastRight s p (gRr s p) (gLs s p) (labMoveR s p)).Gs.getX z) := by
    intro β f hf z; rw [hGs z]; split_ifs <;> simp [hf]
  refine ⟨⟨by simp [moveRState, sizeAdj, sGs], fun z => ?_, fun z => ?_, fun z => ?_, fun z => ?_,
    fun z => ?_, fun z => ?_, fun z => ?_⟩, fun z => ?_, fun z => ?_, fun z => ?_, sHd, rfl,
    ⟨sEs, seN, seP, sLive, sH⟩, sT, sCC⟩
  · show (_ : Group).st = _; rw [fld Group.st (fun _ _ => rfl)]; exact (F z).1
  · show (_ : Group).src = _; rw [fld Group.src (fun _ _ => rfl)]; exact (F z).2.1
  · show (_ : Group).l = _; rw [fld Group.l (fun _ _ => rfl)]; exact (F z).2.2.1
  · show (_ : Group).r = _; rw [fld Group.r (fun _ _ => rfl)]; exact (F z).2.2.2.1
  · show (_ : Group).next = _; rw [fld Group.next (fun _ _ => rfl)]; exact sN z
  · show (_ : Group).chk = _; rw [fld Group.chk (fun _ _ => rfl)]; exact sC z
  · show (_ : Group).alive = _; rw [fld Group.alive (fun _ _ => rfl)]; exact sA z
  · show (_ : Group).size = _
    rw [hGs z]
    have := (F z).2.2.2.2; simp only [gSz] at this
    by_cases h1 : z = p
    · subst h1; simp [this]
    · by_cases h2 : z = gRr s p
      · subst h2; simp [h1, this]
      · simp [h1, h2, this]
  · show ((moveRState s p).E.getX z).grp = _
    have := moveLastRight_eG (s := s) (g := p) (gr := gRr s p) (e := gLs s p) (lab := labMoveR s p) z
    simp only [eG] at this
    simp only [moveRState, sizeAdj]
    rw [this]; simp [he]
  · show ((moveRState s p).E.getX z).lab = _
    have := moveLastRight_eL (s := s) (g := p) (gr := gRr s p) (e := gLs s p) (lab := labMoveR s p) z
    simp only [eL] at this
    simp only [moveRState, sizeAdj]
    rw [this]; simp [he]

end OM.Proof

namespace OM.Proof

open OM.Model

set_option linter.deprecated false

/-! ### `GInvE` across a move -/

/-- The family members of a splitting group other than `p` are not in `p`'s family. -/
theorem FamOK.disjoint {s : Core} {p q : Nat} (Fp : FamOK s p) (Fq : FamOK s q) (hpq : p ≠ q)
    (hps : gSt s p = .splitting) (hqs : gSt s q = .splitting) :
    q ≠ gLl s p ∧ q ≠ gRr s p ∧ gLl s q ≠ gLl s p ∧ gLl s q ≠ gRr s p ∧ gLl s q ≠ p ∧
      gRr s q ≠ gLl s p ∧ gRr s q ≠ gRr s p ∧ gRr s q ≠ p := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro e; have := Fp.lSt; rw [← e, hqs] at this; cases this
  · intro e; have := Fp.rSt; rw [← e, hqs] at this; cases this
  · intro e; have h1 := Fq.lSrc; rw [e, Fp.lSrc] at h1; exact hpq h1
  · intro e; have h1 := Fq.lSrc; rw [e, Fp.rSrc] at h1; exact hpq h1
  · intro e; have := Fq.lSt; rw [e, hps] at this; cases this
  · intro e; have h1 := Fq.rSrc; rw [e, Fp.lSrc] at h1; exact hpq h1
  · intro e; have h1 := Fq.rSrc; rw [e, Fp.rSrc] at h1; exact hpq h1
  · intro e; have := Fq.rSt; rw [e, hps] at this; cases this

theorem FamOK.lp {s : Core} {A : Abs} (hI : INV s A) {p : Nat} (F : FamOK s p) (hp : LiveG s p) :
    gLl s p ≠ p := by
  intro e; have := F.lAdj; rw [e] at this
  have hp' := hI.mem_glist_iff.mpr hp
  rw [hI.gList.next p hp'] at this
  exact succOf_ne_self hI.gList.nodup p hp.1 this

theorem FamOK.rp {s : Core} {A : Abs} (hI : INV s A) {p : Nat} (F : FamOK s p) (hp : LiveG s p) :
    gRr s p ≠ p := by
  intro e; have := F.rAdj; rw [e] at this
  have hp' := hI.mem_glist_iff.mpr hp
  rw [hI.gList.next p hp'] at this
  exact succOf_ne_self hI.gList.nodup p hp.1 this

theorem FamOK.lr {s : Core} {A : Abs} (hI : INV s A) {p : Nat} (F : FamOK s p) (hp : LiveG s p) :
    gLl s p ≠ gRr s p := by
  intro e
  have h1 := F.lAdj; have h2 := F.rAdj
  rw [e] at h1
  have hr' := hI.mem_glist_iff.mpr F.rLive
  have hp' := hI.mem_glist_iff.mpr hp
  -- `r` precedes `p` and `p` precedes `r`
  obtain ⟨l1, l2, e1⟩ := succOf_split ((hI.gList.next _ hr').symm.trans h1) hp.1
  rw [hI.gList.next p hp', e1] at h2
  have hnd := hI.gList.nodup
  rw [e1] at hnd
  rw [show l1 ++ gRr s p :: p :: l2 = (l1 ++ [gRr s p]) ++ p :: l2 by simp,
    succOf_mid (by simpa using hnd)] at h2
  cases l2 with
  | nil => exact F.rLive.1 (by simpa using h2.symm)
  | cons a t =>
    have ha : a = gRr s p := by simpa using h2
    rw [ha] at hnd
    have := (List.nodup_append.mp hnd).2.1
    simp only [List.nodup_cons, List.mem_cons, true_or, not_true_eq_false, false_and,
      or_true] at this

/-- The run of a non-empty group starts at its `first` element. -/
theorem INV.run_head {s : Core} {A : Abs} (hI : INV s A) {g : Nat} (hg : g ∈ A.glist)
    (hne : gF s g ≠ NIL) : ∃ rest, runOf s A.elist g = gF s g :: rest := by
  have hE := (hI.gEnds g hg).1
  rw [hI.elts_eq hg] at hE
  cases h : runOf s A.elist g with
  | nil => rw [h] at hE; exact absurd hE hne
  | cons a t => rw [h] at hE; exact ⟨t, by simp [hE]⟩

/-- The run of a non-empty group ends at its `last` element. -/
theorem INV.run_last {s : Core} {A : Abs} (hI : INV s A) {g : Nat} (hg : g ∈ A.glist)
    (hne : gF s g ≠ NIL) : ∃ front, runOf s A.elist g = front ++ [gLs s g] := by
  have hE := hI.gEnds g hg
  rw [hI.elts_eq hg] at hE
  rcases (runOf s A.elist g).eq_nil_or_concat with h | ⟨front, a, h⟩
  · rw [h] at hE; exact absurd hE.1 hne
  · rw [List.concat_eq_append] at h
    rw [h] at hE ⊢; simp only [Ends] at hE
    refine ⟨front, ?_⟩
    rw [hE.2]; simp

theorem ginv_moveL {s : Core} {A : Abs} {gh : GGh} {δ : Nat → Nat} {p : Nat} (hI : INV s A)
    (hG : GInvE s A.elist gh δ p) (hp : LiveG s p) (hs : gSt s p = .splitting)
    (hne : gF s p ≠ NIL) :
    GInvE (moveLState s p) A.elist
      ⟨gh.hv, Function.update gh.pb (gLl s p) (gh.pb (gLl s p) + 1), gh.pf⟩ δ p := by
  have Fp := hG.fam p hp hs
  generalize hldef : gLl s p = l at *
  have hp' := hI.mem_glist_iff.mpr hp
  have hl' := hI.mem_glist_iff.mpr (hldef ▸ Fp.lLive)
  have hlp : l ≠ p := hldef ▸ Fp.lp hI hp
  have hlL : LiveG s l := hldef ▸ Fp.lLive
  obtain ⟨rest, hrun⟩ := hI.run_head hp' hne
  have he : gF s p ∈ A.elist := (mem_runOf.mp (hrun ▸ (by simp : gF s p ∈ gF s p :: rest))).1
  have heG : eG s (gF s p) = p := (mem_runOf.mp (hrun ▸ (by simp : gF s p ∈ gF s p :: rest))).2
  have M := moveLState_spec (s := s) (p := p) (hldef ▸ hlp) hp.2.1 (hldef ▸ hlL.2.1)
    ((hI.eAlloc _).mp he).2
  rw [hldef] at M
  generalize moveLState s p = s' at M ⊢
  generalize gF s p = e at hrun he heG M
  obtain ⟨X, Y, hL, hXY⟩ := hI.runs_adj hl' (hldef ▸ Fp.lAdj) hp.1
  rw [hrun] at hL
  have hRun := runOf_moveFront hL hXY
    (fun z hz => (mem_runOf.mp (hrun ▸ (by simp [hz] : z ∈ e :: rest))).2)
    (fun z hz => (mem_runOf.mp hz).2) heG hlp hI.eList.nodup M.eG
  have hK := M.links
  have hLive : ∀ b, LiveG s' b ↔ LiveG s b := hK.liveG
  have hszp : gSz s p = rest.length + 1 := by rw [hG.sz p hp, hrun]; simp
  have hSzO : ∀ z, z ≠ l → z ≠ p → gSz s' z = gSz s z := by
    intro z h1 h2; rw [M.sz, if_neg h2, if_neg h1]
  have hSzl : gSz s' l = gSz s l + 1 := by rw [M.sz, if_neg hlp, if_pos rfl]
  have hSzp : gSz s' p = gSz s p - 1 := by rw [M.sz, if_pos rfl]
  have hRO : ∀ z, z ≠ l → z ≠ p → runOf s' A.elist z = runOf s A.elist z := by
    intro z h1 h2; rw [hRun, if_neg h1, if_neg h2]
  have heR : e ∉ runOf s A.elist l := fun h => by
    have := (mem_runOf.mp h).2; rw [heG] at this; exact hlp this.symm
  have heRest : e ∉ rest := fun h => by
    have hnd := hI.eList.nodup.filter (fun z => decide (eG s z = p))
    change (runOf s A.elist p).Nodup at hnd
    rw [hrun] at hnd; exact (List.nodup_cons.mp hnd).1 h
  have hEL : ∀ z, z ≠ e → eL s' z = eL s z := fun z h => by rw [M.eL, if_neg h]
  have hrl : gRr s p ≠ l := fun h => (hldef ▸ Fp.lr hI hp) h.symm
  have hrp : gRr s p ≠ p := Fp.rp hI hp
  have hfamT : famT s' p = famT s p := by
    simp only [famT, hK.l, hK.r, hldef, hSzl, hSzp, hSzO _ hrl hrp]; omega
  have hfamO : ∀ q, LiveG s q → gSt s q = .splitting → q ≠ p → famT s' q = famT s q := by
    intro q hq hqs hqp
    have D := Fp.disjoint (hG.fam q hq hqs) (Ne.symm hqp) hs hqs
    rw [hldef] at D
    simp only [famT, hK.l, hK.r, hSzO _ D.1 hqp, hSzO _ D.2.2.1 D.2.2.2.2.1,
      hSzO _ D.2.2.2.2.2.1 D.2.2.2.2.2.2.2]
  have hlst : gSt s l = .overflow := hldef ▸ Fp.lSt
  have hlsrc : gSrc s l = p := hldef ▸ Fp.lSrc
  -- the label of the moved element
  have hlab : labMoveL s p = if runOf s A.elist l = [] then cE s.P
      else eL s (gLs s l) + s.P.D_e := by
    unfold labMoveL; rw [hldef]
    by_cases h : gF s l = NIL
    · rw [if_pos h, if_pos ((hI.first_nil_iff hl').mp h)]
    · rw [if_neg h, if_neg (fun h' => h ((hI.first_nil_iff hl').mpr h'))]
  refine
    { sz := ?_, fam := ?_, ovf := ?_, notDead := ?_, quiet := ?_, split := ?_, gaps := ?_,
      range := ?_, ghQ := ?_, ghO := ?_, ghS := ?_ }
  · intro z hz
    rw [hLive] at hz
    by_cases h1 : z = l
    · subst h1; rw [hSzl, hRun, if_pos rfl, hG.sz _ hz]; simp
    · by_cases h2 : z = p
      · subst h2; rw [hSzp, hRun, if_neg h1, if_pos rfl, hszp]; simp
      · rw [hSzO z h1 h2, hRO z h1 h2]; exact hG.sz z hz
  · intro z hz hzs; rw [hLive] at hz; rw [hK.st] at hzs; exact hK.famOK (hG.fam z hz hzs)
  · intro z hz hzs; rw [hLive] at hz; rw [hK.st] at hzs; exact hK.ovf (hG.ovf z hz hzs)
  · intro z hz; rw [hLive] at hz; rw [hK.st]; exact hG.notDead z hz
  · intro z hz hzs
    rw [hLive] at hz; rw [hK.st] at hzs
    have h1 : z ≠ l := by rintro rfl; rw [hlst] at hzs; cases hzs
    have h2 : z ≠ p := by rintro rfl; rw [hs] at hzs; cases hzs
    rw [hSzO z h1 h2, hRO z h1 h2, M.head, M.P]
    exact hG.quiet z hz hzs
  · intro z hz hzs hzp
    rw [hLive] at hz; rw [hK.st] at hzs
    have D := Fp.disjoint (hG.fam z hz hzs) (Ne.symm hzp) hs hzs
    rw [hldef] at D
    have := hG.split z hz hzs hzp
    unfold G1 at this ⊢
    rw [M.P, hK.l, hK.r, hSzO _ D.1 hzp, hSzO _ D.2.2.1 D.2.2.2.2.1,
      hSzO _ D.2.2.2.2.2.1 D.2.2.2.2.2.2.2]
    exact this
  · intro z hz
    rw [hLive] at hz
    simp only [M.P]
    by_cases h1 : z = l
    · subst h1
      rw [hRun, if_pos rfl]
      show ((runOf s A.elist z ++ [e]).map (eL s')).IsChain (fun a b => a + s.P.D_e / 2 ^ gh.hv z ≤ b)
      by_cases hemp : runOf s A.elist z = []
      · rw [hemp]; simp
      · have hz' : gF s z ≠ NIL := fun h => hemp ((hI.first_nil_iff hl').mp h)
        obtain ⟨front, hfr⟩ := hI.run_last hl' hz'
        have hc := hG.gaps z hz
        rw [hfr] at hc ⊢
        rw [show front ++ [gLs s z] ++ [e] = front ++ gLs s z :: e :: [] by simp]
        rw [show front ++ [gLs s z] = front ++ gLs s z :: [] by simp] at hc
        refine isChain_insert' hc (fun w hw => hEL w (fun h => heR (by rw [hfr]; exact h ▸ hw)))
          ?_ (by simp)
        rw [M.eL, if_pos rfl, hlab, if_neg hemp]
        have := Nat.div_le_self s.P.D_e (2 ^ gh.hv z); omega
    · by_cases h2 : z = p
      · subst h2
        rw [hRun, if_neg h1, if_pos rfl]
        have hc := hG.gaps z hz
        rw [hrun, List.map_cons] at hc
        have := hc.tail
        rw [List.map_congr_left fun w hw => hEL w (fun h => heRest (h ▸ hw))]
        exact this
      · rw [hRO z h1 h2]
        rw [List.map_congr_left fun w hw => hEL w (fun h => by
          subst h; have := (mem_runOf.mp hw).2; rw [heG] at this; exact h2 this.symm)]
        exact hG.gaps z hz
  · intro z hz w hw
    rw [hLive] at hz
    simp only [M.P]
    by_cases h1 : z = l
    · subst h1
      rw [hRun, if_pos rfl] at hw
      simp only [Function.update_self]
      rcases List.mem_append.mp hw with hw | hw
      · rw [hEL w (fun h => heR (h ▸ hw))]
        obtain ⟨q1, q2⟩ := hG.range z hz w hw
        exact ⟨q1, by have := Nat.le_add_right (gh.pb z * s.P.D_e) s.P.D_e; rw [Nat.add_mul]; omega⟩
      · simp only [List.mem_singleton] at hw
        subst hw
        rw [M.eL, if_pos rfl, hlab]
        split
        · constructor <;> simp
        · next hemp =>
          have hz' : gF s z ≠ NIL := fun h => hemp ((hI.first_nil_iff hl').mp h)
          obtain ⟨front, hfr⟩ := hI.run_last hl' hz'
          obtain ⟨q1, q2⟩ := hG.range z hz (gLs s z) (by rw [hfr]; simp)
          rw [Nat.add_mul]; constructor <;> omega
    · rw [hEL w (fun h => by
        subst h
        by_cases h2 : z = p
        · subst h2; rw [hRun, if_neg h1, if_pos rfl] at hw; exact heRest hw
        · rw [hRO z h1 h2] at hw; have := (mem_runOf.mp hw).2; rw [heG] at this
          exact h2 this.symm)]
      simp only [Function.update_of_ne h1]
      by_cases h2 : z = p
      · subst h2; rw [hRun, if_neg h1, if_pos rfl] at hw
        exact hG.range z hz w (by rw [hrun]; simp [hw])
      · rw [hRO z h1 h2] at hw; exact hG.range z hz w hw
  · intro z hz hzs
    rw [hLive] at hz; rw [hK.st] at hzs
    have h1 : z ≠ l := by rintro rfl; rw [hlst] at hzs; cases hzs
    have h2 : z ≠ p := by rintro rfl; rw [hs] at hzs; cases hzs
    simp only [M.P, hSzO z h1 h2, Function.update_of_ne h1]
    exact hG.ghQ z hz hzs
  · intro z hz hzs
    rw [hLive] at hz; rw [hK.st] at hzs
    simp only [M.P, hK.src]
    by_cases h1 : z = l
    · subst h1
      rw [hlsrc, hfamT, hSzl]; simp only [Function.update_self]
      obtain ⟨q1, q2⟩ := hG.ghO z hz hzs
      rw [hlsrc] at q1
      exact ⟨q1, by omega⟩
    · have h2 : z ≠ p := by rintro rfl; rw [hs] at hzs; cases hzs
      obtain ⟨o1, o2, -⟩ := hG.ovf z hz hzs
      simp only [Function.update_of_ne h1, hSzO z h1 h2]
      by_cases hq : gSrc s z = p
      · rw [hq, hfamT]; have := hG.ghO z hz hzs; rw [hq] at this; exact this
      · rw [hfamO _ o1 o2 hq]; exact hG.ghO z hz hzs
  · intro z hz hzs
    rw [hLive] at hz; rw [hK.st] at hzs
    have h1 : z ≠ l := by rintro rfl; rw [hlst] at hzs; cases hzs
    simp only [M.P, Function.update_of_ne h1]
    by_cases h2 : z = p
    · subst h2; rw [hfamT]; exact hG.ghS z hz hzs
    · rw [hfamO z hz hzs h2]; exact hG.ghS z hz hzs

end OM.Proof

namespace OM.Proof

open OM.Model

set_option linter.deprecated false

theorem ginv_moveR {s : Core} {A : Abs} {gh : GGh} {δ : Nat → Nat} {p : Nat} (hI : INV s A)
    (hG : GInvE s A.elist gh δ p) (hp : LiveG s p) (hs : gSt s p = .splitting)
    (hne : gF s p ≠ NIL) (hroom : gF s (gRr s p) ≠ NIL → s.P.D_e ≤ eL s (gF s (gRr s p))) :
    GInvE (moveRState s p) A.elist
      ⟨gh.hv, gh.pb, Function.update gh.pf (gRr s p) (gh.pf (gRr s p) + 1)⟩ δ p := by
  have Fp := hG.fam p hp hs
  have hrl0 : gRr s p ≠ gLl s p := fun h => Fp.lr hI hp h.symm
  have hlp0 : gLl s p ≠ p := Fp.lp hI hp
  generalize hrdef : gRr s p = r at *
  have hp' := hI.mem_glist_iff.mpr hp
  have hr' := hI.mem_glist_iff.mpr (hrdef ▸ Fp.rLive)
  have hrp : r ≠ p := hrdef ▸ Fp.rp hI hp
  have hrL : LiveG s r := hrdef ▸ Fp.rLive
  obtain ⟨front, hrun⟩ := hI.run_last hp' hne
  have he : gLs s p ∈ A.elist := (mem_runOf.mp (hrun ▸ (by simp : gLs s p ∈ front ++ [gLs s p]))).1
  have heG : eG s (gLs s p) = p :=
    (mem_runOf.mp (hrun ▸ (by simp : gLs s p ∈ front ++ [gLs s p]))).2
  have M := moveRState_spec (s := s) (p := p) (hrdef ▸ hrp) hp.2.1 (hrdef ▸ hrL.2.1)
    ((hI.eAlloc _).mp he).2
  rw [hrdef] at M
  generalize moveRState s p = s' at M ⊢
  generalize gLs s p = e at hrun he heG M
  obtain ⟨X, Y, hL, hXY⟩ := hI.runs_adj hp' (hrdef ▸ Fp.rAdj) (hrdef ▸ hrL.1)
  rw [hrun] at hL
  have hRun := runOf_moveBack hL hXY
    (fun z hz => (mem_runOf.mp (hrun ▸ (by simp [hz] : z ∈ front ++ [e]))).2)
    (fun z hz => (mem_runOf.mp hz).2) heG (Ne.symm hrp) hI.eList.nodup M.eG
  have hK := M.links
  have hLive : ∀ b, LiveG s' b ↔ LiveG s b := hK.liveG
  have hszp : gSz s p = front.length + 1 := by rw [hG.sz p hp, hrun]; simp
  have hSzO : ∀ z, z ≠ r → z ≠ p → gSz s' z = gSz s z := by
    intro z h1 h2; rw [M.sz, if_neg h2, if_neg h1]
  have hSzr : gSz s' r = gSz s r + 1 := by rw [M.sz, if_neg hrp, if_pos rfl]
  have hSzp : gSz s' p = gSz s p - 1 := by rw [M.sz, if_pos rfl]
  have hRO : ∀ z, z ≠ r → z ≠ p → runOf s' A.elist z = runOf s A.elist z := by
    intro z h1 h2; rw [hRun, if_neg h1, if_neg h2]
  have heR : e ∉ runOf s A.elist r := fun h => by
    have := (mem_runOf.mp h).2; rw [heG] at this; exact hrp this.symm
  have heF : e ∉ front := fun h => by
    have hnd := hI.eList.nodup.filter (fun z => decide (eG s z = p))
    change (runOf s A.elist p).Nodup at hnd
    rw [hrun] at hnd
    exact (List.nodup_append.mp hnd).2.2 e h e (by simp) rfl
  have hEL : ∀ z, z ≠ e → eL s' z = eL s z := fun z h => by rw [M.eL, if_neg h]
  have hfamT : famT s' p = famT s p := by
    simp only [famT, hK.l, hK.r, hrdef, hSzr, hSzp, hSzO _ hrl0.symm hlp0]; omega
  have hfamO : ∀ q, LiveG s q → gSt s q = .splitting → q ≠ p → famT s' q = famT s q := by
    intro q hq hqs hqp
    have D := Fp.disjoint (hG.fam q hq hqs) (Ne.symm hqp) hs hqs
    rw [hrdef] at D
    simp only [famT, hK.l, hK.r, hSzO _ D.2.1 hqp, hSzO _ D.2.2.2.1 D.2.2.2.2.1,
      hSzO _ D.2.2.2.2.2.2.1 D.2.2.2.2.2.2.2]
  have hrst : gSt s r = .overflow := hrdef ▸ Fp.rSt
  have hrsrc : gSrc s r = p := hrdef ▸ Fp.rSrc
  have hlab : labMoveR s p = if runOf s A.elist r = [] then cE s.P
      else eL s (gF s r) - s.P.D_e := by
    unfold labMoveR; rw [hrdef]
    by_cases h : gF s r = NIL
    · rw [if_pos h, if_pos ((hI.first_nil_iff hr').mp h)]
    · rw [if_neg h, if_neg (fun h' => h ((hI.first_nil_iff hr').mpr h'))]
  refine
    { sz := ?_, fam := ?_, ovf := ?_, notDead := ?_, quiet := ?_, split := ?_, gaps := ?_,
      range := ?_, ghQ := ?_, ghO := ?_, ghS := ?_ }
  · intro z hz
    rw [hLive] at hz
    by_cases h1 : z = r
    · subst h1; rw [hSzr, hRun, if_pos rfl, hG.sz _ hz]; simp
    · by_cases h2 : z = p
      · subst h2; rw [hSzp, hRun, if_neg h1, if_pos rfl, hszp]; simp
      · rw [hSzO z h1 h2, hRO z h1 h2]; exact hG.sz z hz
  · intro z hz hzs; rw [hLive] at hz; rw [hK.st] at hzs; exact hK.famOK (hG.fam z hz hzs)
  · intro z hz hzs; rw [hLive] at hz; rw [hK.st] at hzs; exact hK.ovf (hG.ovf z hz hzs)
  · intro z hz; rw [hLive] at hz; rw [hK.st]; exact hG.notDead z hz
  · intro z hz hzs
    rw [hLive] at hz; rw [hK.st] at hzs
    have h1 : z ≠ r := by rintro rfl; rw [hrst] at hzs; cases hzs
    have h2 : z ≠ p := by rintro rfl; rw [hs] at hzs; cases hzs
    rw [hSzO z h1 h2, hRO z h1 h2, M.head, M.P]
    exact hG.quiet z hz hzs
  · intro z hz hzs hzp
    rw [hLive] at hz; rw [hK.st] at hzs
    have D := Fp.disjoint (hG.fam z hz hzs) (Ne.symm hzp) hs hzs
    rw [hrdef] at D
    have := hG.split z hz hzs hzp
    unfold G1 at this ⊢
    rw [M.P, hK.l, hK.r, hSzO _ D.2.1 hzp, hSzO _ D.2.2.2.1 D.2.2.2.2.1,
      hSzO _ D.2.2.2.2.2.2.1 D.2.2.2.2.2.2.2]
    exact this
  · intro z hz
    rw [hLive] at hz
    simp only [M.P]
    by_cases h1 : z = r
    · subst h1
      rw [hRun, if_pos rfl]
      by_cases hemp : runOf s A.elist z = []
      · rw [hemp]; simp
      · have hz' : gF s z ≠ NIL := fun h => hemp ((hI.first_nil_iff hr').mp h)
        obtain ⟨rest, hre⟩ := hI.run_head hr' hz'
        have hc := hG.gaps z hz
        rw [hre] at hc ⊢
        have hc' : (([] ++ gF s z :: rest).map (eL s')).IsChain
            (fun a b => a + s.P.D_e / 2 ^ gh.hv z ≤ b) := by
          rw [List.map_congr_left fun w hw => hEL w (fun h => heR (by rw [hre]; simpa [h] using hw))]
          simpa using hc
        have hgap : eL s' e + s.P.D_e / 2 ^ gh.hv z ≤ eL s' (gF s z) := by
          rw [M.eL, if_pos rfl, hlab, if_neg hemp, hEL _ (fun h => heR (by rw [hre, ← h]; simp))]
          have := hroom hz'
          have := Nat.div_le_self s.P.D_e (2 ^ gh.hv z)
          omega
        rw [List.map_cons, List.map_cons, List.isChain_cons_cons]
        exact ⟨hgap, by simpa using hc'⟩
    · by_cases h2 : z = p
      · subst h2
        rw [hRun, if_neg h1, if_pos rfl]
        have hc := hG.gaps z hz
        rw [hrun] at hc
        rw [List.map_congr_left fun w hw => hEL w (fun h => heF (h ▸ hw))]
        exact (List.isChain_append.mp (by simpa using hc)).1
      · rw [hRO z h1 h2]
        rw [List.map_congr_left fun w hw => hEL w (fun h => by
          subst h; have := (mem_runOf.mp hw).2; rw [heG] at this; exact h2 this.symm)]
        exact hG.gaps z hz
  · intro z hz w hw
    rw [hLive] at hz
    simp only [M.P]
    by_cases h1 : z = r
    · subst h1
      rw [hRun, if_pos rfl] at hw
      simp only [Function.update_self]
      rcases List.mem_cons.mp hw with hw | hw
      · subst hw
        rw [M.eL, if_pos rfl, hlab]
        split
        · constructor <;> simp
        · next hemp =>
          have hz' : gF s z ≠ NIL := fun h => hemp ((hI.first_nil_iff hr').mp h)
          obtain ⟨rest, hre⟩ := hI.run_head hr' hz'
          obtain ⟨q1, q2⟩ := hG.range z hz (gF s z) (by rw [hre]; simp)
          have := hroom hz'
          rw [Nat.add_mul]; constructor <;> omega
      · rw [hEL w (fun h => heR (h ▸ hw))]
        obtain ⟨q1, q2⟩ := hG.range z hz w hw
        exact ⟨by have := Nat.le_add_right (gh.pf z * s.P.D_e) s.P.D_e; rw [Nat.add_mul]; omega, q2⟩
    · rw [hEL w (fun h => by
        subst h
        by_cases h2 : z = p
        · subst h2; rw [hRun, if_neg h1, if_pos rfl] at hw; exact heF hw
        · rw [hRO z h1 h2] at hw; have := (mem_runOf.mp hw).2; rw [heG] at this
          exact h2 this.symm)]
      simp only [Function.update_of_ne h1]
      by_cases h2 : z = p
      · subst h2; rw [hRun, if_neg h1, if_pos rfl] at hw
        exact hG.range z hz w (by rw [hrun]; simp [hw])
      · rw [hRO z h1 h2] at hw; exact hG.range z hz w hw
  · intro z hz hzs
    rw [hLive] at hz; rw [hK.st] at hzs
    have h1 : z ≠ r := by rintro rfl; rw [hrst] at hzs; cases hzs
    have h2 : z ≠ p := by rintro rfl; rw [hs] at hzs; cases hzs
    simp only [M.P, hSzO z h1 h2, Function.update_of_ne h1]
    exact hG.ghQ z hz hzs
  · intro z hz hzs
    rw [hLive] at hz; rw [hK.st] at hzs
    simp only [M.P, hK.src]
    by_cases h1 : z = r
    · subst h1
      rw [hrsrc, hfamT, hSzr]; simp only [Function.update_self]
      obtain ⟨q1, q2⟩ := hG.ghO z hz hzs
      rw [hrsrc] at q1
      exact ⟨q1, by omega⟩
    · have h2 : z ≠ p := by rintro rfl; rw [hs] at hzs; cases hzs
      obtain ⟨o1, o2, -⟩ := hG.ovf z hz hzs
      simp only [Function.update_of_ne h1, hSzO z h1 h2]
      by_cases hq : gSrc s z = p
      · rw [hq, hfamT]; have := hG.ghO z hz hzs; rw [hq] at this; exact this
      · rw [hfamO _ o1 o2 hq]; exact hG.ghO z hz hzs
  · intro z hz hzs
    rw [hLive] at hz; rw [hK.st] at hzs
    have h1 : z ≠ r := by rintro rfl; rw [hrst] at hzs; cases hzs
    simp only [M.P, Function.update_of_ne h1]
    by_cases h2 : z = p
    · subst h2; rw [hfamT]; exact hG.ghS z hz hzs
    · rw [hfamO z hz hzs h2]; exact hG.ghS z hz hzs

end OM.Proof
