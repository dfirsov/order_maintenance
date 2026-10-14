import OM.Proof.Correct.Good
import OM.Spec

/-!
# Element insertion preserves INV-S (Lemma 3.2, first case)

`insertElem x h` either fails its label guard and changes nothing, or links a new element `y`
right after `x` in `x`'s group, with a label strictly between those of `x` and its successor
in the group.
-/

namespace OM.Proof

open OM.Model

set_option linter.deprecated false

/-! ### Reading INV-S -/

theorem INV.elist_flatten (A : Abs) : A.elist = (A.glist.map A.elts).flatten := by
  simp [Abs.elist, List.flatMap_def]

theorem INV.glist_flatten (A : Abs) : A.glist = (A.chunks.map A.grps).flatten := by
  simp [Abs.glist, List.flatMap_def]

theorem INV.mem_elist {s : Core} {A : Abs} (h : INV s A) {e : Nat} (he : e ∈ A.elist) :
    eG s e ∈ A.glist ∧ e ∈ A.elts (eG s e) := by
  simp only [Abs.elist, List.mem_flatMap] at he
  obtain ⟨g, hg, he⟩ := he
  rw [h.grp g hg e he]; exact ⟨hg, he⟩

theorem INV.mem_glist {s : Core} {A : Abs} (h : INV s A) {g : Nat} (hg : g ∈ A.glist) :
    gC s g ∈ A.chunks ∧ g ∈ A.grps (gC s g) := by
  simp only [Abs.glist, List.mem_flatMap] at hg
  obtain ⟨c, hc, hg⟩ := hg
  rw [h.chk c hc g hg]; exact ⟨hc, hg⟩

theorem Abs.elts_sub_elist (A : Abs) {g e : Nat} (hg : g ∈ A.glist) (he : e ∈ A.elts g) :
    e ∈ A.elist := by
  simp only [Abs.elist, List.mem_flatMap]; exact ⟨g, hg, he⟩

theorem Abs.grps_sub_glist (A : Abs) {c g : Nat} (hc : c ∈ A.chunks) (hg : g ∈ A.grps c) :
    g ∈ A.glist := by
  simp only [Abs.glist, List.mem_flatMap]; exact ⟨c, hc, hg⟩

/-- Inside a group's run, the element after `x` is its successor in the run. -/
theorem INV.eN_in_run {s : Core} {A : Abs} (h : INV s A) {g x : Nat} (hg : g ∈ A.glist)
    (hx : x ∈ A.elts g) (hl : (A.elts g).getLast? ≠ some x) : eN s x = succOf (A.elts g) x := by
  rw [h.eList.next x (A.elts_sub_elist hg hx), INV.elist_flatten]
  have hnd := h.eList.nodup
  rw [INV.elist_flatten] at hnd
  exact succOf_flatten hnd (List.mem_map.mpr ⟨g, hg, rfl⟩) hx hl

/-! ### Lists -/

theorem isChain_insert {l1 l2 : List Nat} {x y : Nat} {f f' : Nat → Nat}
    (hs : ((l1 ++ x :: l2).map f).IsChain (· < ·)) (hagree : ∀ z ∈ l1 ++ x :: l2, f' z = f z)
    (hxy : f x < f' y) (hy2 : ∀ w ∈ l2.head?, f' y < f w) :
    ((l1 ++ x :: y :: l2).map f').IsChain (· < ·) := by
  have e1 : l1.map f' = l1.map f := List.map_congr_left fun z hz => hagree z (by simp [hz])
  have e2 : l2.map f' = l2.map f := List.map_congr_left fun z hz => hagree z (by simp [hz])
  have ex : f' x = f x := hagree x (by simp)
  simp only [List.map_append, List.map_cons, e1, e2, ex] at hs ⊢
  rw [List.isChain_append] at hs ⊢
  refine ⟨hs.1, ?_, ?_⟩
  · rw [List.isChain_cons_cons]
    refine ⟨hxy, ?_⟩
    rw [List.isChain_cons]
    refine ⟨fun w hw => ?_, (List.isChain_cons.mp hs.2.1).2⟩
    cases l2 with
    | nil => simp at hw
    | cons a t =>
      simp only [List.map_cons, List.head?_cons, Option.mem_def, Option.some.injEq] at hw
      subst hw; exact hy2 a (by simp)
  · intro a ha b hb
    simp only [List.head?_cons, Option.mem_def, Option.some.injEq] at hb
    subst hb
    exact hs.2.2 a ha (f x) (by simp)

theorem insertAfterL_append (x y : Nat) (a b : List Nat) :
    OM.Spec.insertAfterL x y (a ++ b) =
      if x ∈ a then OM.Spec.insertAfterL x y a ++ b else a ++ OM.Spec.insertAfterL x y b := by
  induction a with
  | nil => simp
  | cons c t ih =>
    simp only [List.cons_append, OM.Spec.insertAfterL, List.mem_cons]
    by_cases hc : c = x
    · simp [hc]
    · simp only [hc, if_false, ih, Ne.symm hc, false_or]
      split <;> simp

theorem insertAfterL_not_mem {x y : Nat} {l : List Nat} (h : x ∉ l) :
    OM.Spec.insertAfterL x y l = l := by
  induction l with
  | nil => rfl
  | cons c t ih =>
    simp only [List.mem_cons, not_or] at h
    simp [OM.Spec.insertAfterL, Ne.symm h.1, ih h.2]

theorem insertAfterL_mid {l1 l2 : List Nat} {x y : Nat} (h : x ∉ l1) :
    OM.Spec.insertAfterL x y (l1 ++ x :: l2) = l1 ++ x :: y :: l2 := by
  rw [insertAfterL_append, if_neg h]
  simp [OM.Spec.insertAfterL]

theorem flatMap_insertAfter {L : List Nat} {F F' : Nat → List Nat} {g x y : Nat}
    (hnd : (L.flatMap F).Nodup) (hgnd : L.Nodup) (hg : g ∈ L) (hx : x ∈ F g)
    (hF : ∀ b, F' b = if b = g then OM.Spec.insertAfterL x y (F g) else F b) :
    L.flatMap F' = OM.Spec.insertAfterL x y (L.flatMap F) := by
  induction L with
  | nil => simp at hg
  | cons b t ih =>
    simp only [List.flatMap_cons] at hnd ⊢
    rw [insertAfterL_append, hF b]
    simp only [List.nodup_cons] at hgnd
    by_cases hb : b = g
    · subst hb
      simp only [if_true, hx]
      congr 1
      refine List.flatMap_congr fun b' hb' => ?_
      rw [hF b', if_neg (fun (e : b' = b) => hgnd.1 (e ▸ hb'))]
    · have hxb : x ∉ F b := by
        intro hxb
        have hgt : g ∈ t := by simpa [Ne.symm hb] using hg
        have : x ∈ t.flatMap F := List.mem_flatMap.mpr ⟨g, hgt, hx⟩
        exact (List.nodup_append.mp hnd).2.2 x hxb x this rfl
      simp only [hb, if_false, hxb]
      congr 1
      exact ih (List.nodup_append.mp hnd).2.1 hgnd.2 (by simpa [Ne.symm hb] using hg)

end OM.Proof

/-! ### Linking a new element -/

namespace OM.Proof

open OM.Model

set_option linter.deprecated false

section link
variable (s : Core) (x lab h : Nat)

/-- The abstract nesting after inserting `y` after `x` in `x`'s group. -/
def Abs.insElem (A : Abs) (g x y : Nat) : Abs :=
  { A with elts := fun b => if b = g then OM.Spec.insertAfterL x y (A.elts g) else A.elts b }

theorem linkElem_eN (z : Nat) (hx : x < s.E.size) :
    eN (linkElem s x s.E.size lab h) z =
      if z = x then s.E.size else if z = s.E.size then eN s x else eN s z := by
  simp only [linkElem, eN]
  by_cases hzx : z = x
  · subst hzx; simp [hx, Nat.le_of_lt hx, apply_ite (f := Elem.next)]
  · by_cases hzy : z = s.E.size
    · subst hzy
      simp [Ne.symm hzx, hzx, apply_ite (f := Elem.next)]
    · simp [Ne.symm hzx, hzx, hzy, apply_ite (f := Elem.next)]

theorem linkElem_eP (z : Nat) (hx : x < s.E.size) (hns : eN s x = NIL ∨ eN s x < s.E.size) :
    eP (linkElem s x s.E.size lab h) z =
      if z = s.E.size then x else if z = eN s x ∧ eN s x ≠ NIL then s.E.size else eP s z := by
  simp only [linkElem, eP, eN] at hns ⊢
  by_cases hzy : z = s.E.size
  · subst hzy
    have : (s.E.getX x).next ≠ s.E.size := by
      rcases hns with h | h
      · rw [h]; unfold NIL; omega
      · omega
    simp [apply_ite (f := Elem.prev), this, Ne.symm this]
  · by_cases hzn : z = (s.E.getX x).next ∧ (s.E.getX x).next ≠ NIL
    · obtain ⟨rfl, hn⟩ := hzn
      have hlt : (s.E.getX x).next < s.E.size := by rcases hns with h | h <;> simp_all
      simp [hzy, hn, apply_ite (f := Elem.prev), Nat.le_of_lt hlt]
    · simp only [not_and, ne_eq, not_not] at hzn
      by_cases hz : z = (s.E.getX x).next
      · have := hzn hz; subst hz
        simp [hzy, this, apply_ite (f := Elem.prev)]
      · simp [hzy, hz, Ne.symm hz, apply_ite (f := Elem.prev)]

theorem linkElem_eG (z : Nat) :
    eG (linkElem s x s.E.size lab h) z = if z = s.E.size then eG s x else eG s z := by
  simp only [linkElem, eG]
  by_cases hzy : z = s.E.size
  · subst hzy; simp [apply_ite (f := Elem.grp)]
  · simp [hzy, apply_ite (f := Elem.grp)]

theorem linkElem_eL (z : Nat) :
    eL (linkElem s x s.E.size lab h) z = if z = s.E.size then lab else eL s z := by
  simp only [linkElem, eL]
  by_cases hzy : z = s.E.size
  · subst hzy; simp [apply_ite (f := Elem.lab)]
  · simp [hzy, apply_ite (f := Elem.lab)]

theorem linkElem_live (z : Nat) :
    ((linkElem s x s.E.size lab h).E.getX z).live = if z = s.E.size then true else (s.E.getX z).live := by
  simp only [linkElem]
  by_cases hzy : z = s.E.size
  · subst hzy; simp [apply_ite (f := Elem.live)]
  · simp [hzy, apply_ite (f := Elem.live)]

theorem linkElem_h (z : Nat) :
    ((linkElem s x s.E.size lab h).E.getX z).h = if z = s.E.size then h else (s.E.getX z).h := by
  simp only [linkElem]
  by_cases hzy : z = s.E.size
  · subst hzy; simp [apply_ite (f := Elem.h)]
  · simp [hzy, apply_ite (f := Elem.h)]

theorem linkElem_Esize : (linkElem s x s.E.size lab h).E.size = s.E.size + 1 := by
  simp [linkElem]

end link

end OM.Proof

namespace OM.Proof

open OM.Model

set_option linter.deprecated false

theorem INV.size_pos {s : Core} {A : Abs} (h : INV s A) {x : Nat} (hx : x ∈ A.elist) :
    1 ≤ x ∧ x < s.E.size := (h.eAlloc x).mp hx

theorem INV.eN_mem {s : Core} {A : Abs} (h : INV s A) {x : Nat} (hx : x ∈ A.elist) :
    eN s x = NIL ∨ eN s x ∈ A.elist := by
  rw [h.eList.next x hx]
  rcases succOf_mem_or (l := A.elist) (x := x) with h' | h'
  · exact Or.inr h'
  · exact Or.inl h'

/-- **Linking a new element preserves INV-S** when its label lies above `x`'s, and below the
label of `x`'s successor if that successor is in the same group. -/
theorem inv_linkElem {s : Core} {A : Abs} (hI : INV s A) {x lab h : Nat} (hx : x ∈ A.elist)
    (hlab1 : eL s x < lab) (hlab2 : x ≠ gLs s (eG s x) → lab < eL s (eN s x)) :
    INV (linkElem s x s.E.size lab h) (A.insElem (eG s x) x s.E.size) ∧
      (A.insElem (eG s x) x s.E.size).elist = OM.Spec.insertAfterL x s.E.size A.elist := by
  obtain ⟨hg, hxg⟩ := hI.mem_elist hx
  generalize hgdef : eG s x = g at hg hxg hlab2 ⊢
  generalize hydef : s.E.size = y
  have hx1 := hI.size_pos hx
  rw [hydef] at hx1
  have hyl : y ∉ A.elist := fun hm => by have := (hI.eAlloc y).mp hm; omega
  have hy0 : y ≠ NIL := by unfold NIL; omega
  have hns : eN s x = NIL ∨ eN s x < y := by
    rcases hI.eN_mem hx with h' | h'
    · exact Or.inl h'
    · exact Or.inr (hydef ▸ ((hI.eAlloc _).mp h').2)
  have hel : (A.insElem g x y).elist = OM.Spec.insertAfterL x y A.elist := by
    unfold Abs.insElem Abs.elist
    simp only [Abs.glist] at *
    exact flatMap_insertAfter hI.eList.nodup hI.gList.nodup hg hxg fun b => rfl
  refine ⟨?_, hel⟩
  obtain ⟨l1, l2, hsplit⟩ := List.mem_iff_append.mp hx
  have hnd := hI.eList.nodup
  rw [hsplit] at hnd
  have hx1' : x ∉ l1 := fun h => (List.nodup_append.mp hnd).2.2 x h x (by simp) rfl
  have hnew : (A.insElem g x y).elist = l1 ++ x :: y :: l2 := by
    rw [hel, hsplit, insertAfterL_mid hx1']
  have hgl : (A.insElem g x y).glist = A.glist := rfl
  obtain ⟨r1, r2, hrun⟩ := List.mem_iff_append.mp hxg
  have hrnd : (A.elts g).Nodup := by
    have := hI.eList.nodup; rw [INV.elist_flatten] at this
    exact List.nodup_flatten.mp this |>.1 _ (List.mem_map.mpr ⟨g, hg, rfl⟩)
  have hr1 : x ∉ r1 := by
    rw [hrun] at hrnd; exact fun h => (List.nodup_append.mp hrnd).2.2 x h x (by simp) rfl
  have hins : (A.insElem g x y).elts g = r1 ++ x :: y :: r2 := by
    simp [Abs.insElem, hrun, insertAfterL_mid hr1]
  have hother : ∀ b, b ≠ g → (A.insElem g x y).elts b = A.elts b := by
    intro b hb; simp [Abs.insElem, hb]
  -- accessors of the new state
  have eNs : ∀ z, eN (linkElem s x y lab h) z =
      if z = x then y else if z = y then eN s x else eN s z := by
    intro z; rw [← hydef]; exact linkElem_eN s x lab h z (hydef ▸ hx1.2)
  have ePs : ∀ z, eP (linkElem s x y lab h) z =
      if z = y then x else if z = eN s x ∧ eN s x ≠ NIL then y else eP s z := by
    intro z; rw [← hydef]; exact linkElem_eP s x lab h z (hydef ▸ hx1.2) (hydef ▸ hns)
  have eGs : ∀ z, eG (linkElem s x y lab h) z = if z = y then g else eG s z := by
    intro z; rw [← hydef, ← hgdef]; exact linkElem_eG s x lab h z
  have eLs : ∀ z, eL (linkElem s x y lab h) z = if z = y then lab else eL s z := by
    intro z; rw [← hydef]; exact linkElem_eL s x lab h z
  have hgsz : g < s.Gs.size := hI.gAlloc g hg
  have hGs : ∀ b, (linkElem s x y lab h).Gs.getX b = if g = b then
      { s.Gs.getX b with last := if (s.Gs.getX b).last = x then y else (s.Gs.getX b).last,
                         size := (s.Gs.getX b).size + 1 } else s.Gs.getX b := by
    intro b
    show (s.Gs.modify (s.E.getX x).grp _).getX b = _
    rw [Array.getX_modify]
    have hg' : (s.E.getX x).grp = g := hgdef
    rw [hg']
    by_cases hb : g = b
    · subst hb; simp [hgsz]
    · simp [hb]
  have gN' : ∀ b, gN (linkElem s x y lab h) b = gN s b := by
    intro b; simp only [gN, hGs]; split <;> rfl
  have gP' : ∀ b, gP (linkElem s x y lab h) b = gP s b := by
    intro b; simp only [gP, hGs]; split <;> rfl
  have gF' : ∀ b, gF (linkElem s x y lab h) b = gF s b := by
    intro b; simp only [gF, hGs]; split <;> rfl
  have gC' : ∀ b, gC (linkElem s x y lab h) b = gC s b := by
    intro b; simp only [gC, hGs]; split <;> rfl
  have gL' : ∀ b, gL (linkElem s x y lab h) b = gL s b := by
    intro b; simp only [gL, hGs]; split <;> rfl
  have gA' : ∀ b, gA (linkElem s x y lab h) b = gA s b := by
    intro b; simp only [gA, hGs]; split <;> rfl
  have gLs' : ∀ b, gLs (linkElem s x y lab h) b = if b = g ∧ gLs s b = x then y else gLs s b := by
    intro b; simp only [gLs, hGs]
    by_cases hb : b = g
    · subst hb; simp
    · simp [Ne.symm hb, hb]
  have hGsize : (linkElem s x y lab h).Gs.size = s.Gs.size := by simp [linkElem]
  have hEsize : (linkElem s x y lab h).E.size = y + 1 := by
    rw [← hydef]; exact linkElem_Esize s x lab h
  have hmem : ∀ z ∈ l1 ++ x :: y :: l2, z ≠ y → z ∈ A.elist := by
    intro z hz hzy; rw [hsplit]; exact (mem_insert_iff.mp hz).resolve_left hzy
  -- `x` is the last of its group iff it is the group's `last`
  have hlastx : gLs s g = x ↔ r2 = [] := by
    rw [(hI.gEnds g hg).2, hrun]
    constructor
    · intro e
      cases r2 with
      | nil => rfl
      | cons a t =>
        exfalso
        rw [show r1 ++ x :: a :: t = (r1 ++ [x]) ++ a :: t by simp, getLastD_append_cons] at e
        rw [hrun] at hrnd
        have hm := getLastD_cons_mem a t NIL
        rw [e] at hm
        exact (List.nodup_cons.mp (List.nodup_append.mp hrnd).2.1).1 hm
    · rintro rfl; simp
  refine
    { eList := ?_, eAlloc := ?_, tail := ?_, gList := ?_, gAlloc := ?_, gPos := ?_, gAlive := ?_,
      gOut := ?_, free := ?_, freeNodup := ?_, cList := ?_, cAlloc := ?_, cOut := ?_,
      gEnds := ?_, cEnds := ?_, grp := ?_, chk := ?_, eSorted := ?_, gSorted := ?_,
      cSorted := ?_ }
  · -- element list
    rw [hnew]
    have hL := hI.eList
    rw [hsplit] at hL
    refine LList.insert_after hL (by rw [← hsplit]; exact hyl) hy0 (fun z _ => eNs z)
      (fun z hz => ?_)
    rw [ePs z]
    by_cases hzy : z = y
    · rw [if_pos hzy, if_pos hzy]
    · have hz0 : z ≠ NIL := fun e => hI.eList.nonil (e ▸ hmem z hz hzy)
      rw [if_neg hzy, if_neg hzy]
      by_cases hzn : z = eN s x
      · rw [if_pos ⟨hzn, hzn ▸ hz0⟩, if_pos hzn]
      · rw [if_neg (fun h => hzn h.1), if_neg hzn]
  · intro e
    rw [hnew, hEsize]
    rw [mem_insert_iff, ← hsplit, hI.eAlloc e, hydef]
    have := hx1.1
    constructor
    · rintro (rfl | ⟨h1, h2⟩)
      · exact ⟨by omega, by omega⟩
      · exact ⟨h1, by omega⟩
    · rintro ⟨h1, h2⟩
      by_cases hey : e = y
      · exact Or.inl hey
      · exact Or.inr ⟨h1, by omega⟩
  · -- tail
    rw [hnew]
    have ht := hI.tail
    rw [hsplit] at ht
    simp only [linkElem, beq_iff_eq]
    cases l2 with
    | nil => simp at ht; simp [ht]
    | cons a t =>
      rw [show l1 ++ x :: a :: t = (l1 ++ [x]) ++ a :: t by simp, getLastD_append_cons] at ht
      have hxt : s.tail ≠ x := by
        intro e
        have hm := getLastD_cons_mem a t NIL
        rw [← ht, e] at hm
        exact (List.nodup_cons.mp (List.nodup_append.mp hnd).2.1).1 hm
      rw [if_neg hxt, ht, show l1 ++ x :: y :: a :: t = (l1 ++ [x, y]) ++ a :: t by simp,
        getLastD_append_cons]
  · rw [hgl]
    have : gN (linkElem s x y lab h) = gN s := funext gN'
    have h2 : gP (linkElem s x y lab h) = gP s := funext gP'
    rw [this, h2]; exact hI.gList
  · intro b hb; rw [hGsize]; exact hI.gAlloc b hb
  · rw [hGsize]; exact hI.gPos
  · intro b hb1 hb2; rw [gA', hgl]; rw [hGsize] at hb2; exact hI.gAlive b hb1 hb2
  · intro b hb; rw [gN', gP']; exact hI.gOut b hb
  · intro b hb; rw [hGsize]; exact hI.free b hb
  · exact hI.freeNodup
  · exact hI.cList
  · exact hI.cAlloc
  · exact hI.cOut
  · intro b hb
    rw [hgl] at hb
    rw [gF', gLs']
    by_cases hbg : b = g
    · subst hbg
      rw [hins]
      have he := hI.gEnds b hb
      rw [hrun] at he
      refine ⟨by rw [he.1]; cases r1 <;> simp, ?_⟩
      by_cases hr2 : r2 = []
      · subst hr2; simp [hlastx.mpr rfl]
      · have : ¬ gLs s b = x := fun e => hr2 (hlastx.mp e)
        simp only [this, and_false, if_false]
        obtain ⟨a, t, rfl⟩ := List.exists_cons_of_ne_nil hr2
        rw [he.2, show r1 ++ x :: a :: t = (r1 ++ [x]) ++ a :: t by simp, getLastD_append_cons,
          show r1 ++ x :: y :: a :: t = (r1 ++ [x, y]) ++ a :: t by simp,
          getLastD_append_cons]
    · rw [hother b hbg]
      simp only [hbg, false_and, if_false]
      exact hI.gEnds b hb
  · exact hI.cEnds
  · intro b hb e he
    rw [hgl] at hb
    rw [eGs]
    by_cases hbg : b = g
    · subst hbg
      rw [hins] at he
      by_cases hey : e = y
      · simp [hey]
      · rw [if_neg hey]
        apply hI.grp b hb e
        rw [hrun]; exact (mem_insert_iff.mp he).resolve_left hey
    · rw [hother b hbg] at he
      have hey : e ≠ y := fun e' => hyl (e' ▸ A.elts_sub_elist hb he)
      rw [if_neg hey]; exact hI.grp b hb e he
  · intro c hc b hb; rw [gC']; exact hI.chk c hc b hb
  · intro b hb
    rw [hgl] at hb
    by_cases hbg : b = g
    · subst hbg
      rw [hins]
      have hs := hI.eSorted b hb
      rw [hrun] at hs
      refine isChain_insert hs (fun z hz => ?_) ?_ ?_
      · rw [eLs, if_neg]; intro e; subst e
        exact hyl (A.elts_sub_elist hb (hrun ▸ hz))
      · rw [eLs, if_pos rfl]; exact hlab1
      · intro w hw
        rw [eLs, if_pos rfl]
        have hr2 : r2 ≠ [] := by rintro rfl; simp at hw
        have hnl : x ≠ gLs s b := fun e => hr2 (hlastx.mp e.symm)
        have := hlab2 hnl
        -- the successor of `x` in the element list is the head of `r2`
        have hnotlast : (A.elts b).getLast? ≠ some x := by
          rw [hrun]
          obtain ⟨a, t, rfl⟩ := List.exists_cons_of_ne_nil hr2
          intro e
          rw [show r1 ++ x :: a :: t = (r1 ++ [x]) ++ a :: t by simp,
            List.getLast?_append_of_ne_nil _ (by simp)] at e
          have hm : x ∈ a :: t := List.mem_of_getLast? e
          rw [hrun] at hrnd
          exact (List.nodup_cons.mp (List.nodup_append.mp hrnd).2.1).1 hm
        have hsucc : eN s x = w := by
          rw [hI.eN_in_run hb hxg hnotlast, hrun, succOf_mid (hrun ▸ hrnd)]
          cases r2 with
          | nil => simp at hw
          | cons a t => simp at hw; simp [hw]
        rw [← hsucc]; exact this
    · rw [hother b hbg]
      have : ((A.elts b).map (eL (linkElem s x y lab h))) = (A.elts b).map (eL s) := by
        refine List.map_congr_left fun z hz => ?_
        rw [eLs, if_neg]; intro e; subst e; exact hyl (A.elts_sub_elist hb hz)
      rw [this]; exact hI.eSorted b hb
  · intro c hc
    have : gL (linkElem s x y lab h) = gL s := funext gL'
    rw [this]; exact hI.gSorted c hc
  · exact hI.cSorted

end OM.Proof

namespace OM.Proof

open OM.Model

set_option linter.deprecated false

/-- What `insertElem` does: it fails its label guard and changes nothing, or it links the new
element `E.size` after `x` with a label above `x`'s, and below that of `x`'s successor unless
`x` is its group's last element. -/
theorem insertElem_run (s : Core) (x hh : Nat) :
    (∃ lab, eL s x < lab ∧ (x ≠ gLs s (eG s x) → lab < eL s (eN s x)) ∧
        (insertElem x hh).run s = .ok s.E.size (linkElem s x s.E.size lab hh)) ∨
    (∃ msg, (insertElem x hh).run s = .error (.guard msg) s) := by
  unfold insertElem
  simp only [run_getP_bind, run_getE_bind, run_getG_bind]
  by_cases hl : x = (s.Gs.getX (s.E.getX x).grp).last
  · rw [if_pos (beq_iff_eq.mpr hl), run_bind, run_after]
    by_cases hg : (s.E.getX x).lab + s.P.D_e ≥ 1 <<< s.P.B_e ∨
        (s.E.getX x).lab + s.P.D_e ≤ (s.E.getX x).lab
    · right; refine ⟨"elem: no room after last", ?_⟩; rw [if_pos hg]
    · left
      refine ⟨(s.E.getX x).lab + s.P.D_e, ?_, fun h => (h hl).elim, ?_⟩
      · simp only [not_or] at hg; simp only [eL]; omega
      · rw [if_neg hg]; simp only [run_get_bind, run_modify_bind, run_pure]
  · rw [if_neg (fun h => hl (beq_iff_eq.mp h))]
    simp only [run_getE_bind]
    rw [run_bind, run_between]
    by_cases hg : (s.E.getX x).lab + 1 ≥ (s.E.getX (s.E.getX x).next).lab
    · right; refine ⟨"elem: no room between", ?_⟩; rw [if_pos hg]
    · left
      refine ⟨((s.E.getX x).lab + (s.E.getX (s.E.getX x).next).lab) / 2, ?_, fun _ => ?_, ?_⟩
      · simp only [eL]; omega
      · simp only [eL, eN]; omega
      · rw [if_neg hg]; simp only [run_get_bind, run_modify_bind, run_pure]

end OM.Proof
