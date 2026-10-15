import OM.Impl.Job
import OM.Impl.Reservation
import OM.Proof.Top.PresDrain
import OM.Proof.Top.PresFinish
import OM.Proof.Top.StartRun
import OM.Proof.Top.InsStart

/-!
# M6: the glue for the top structure

Level F's top proofs establish the hypotheses of the run lemmas inside their proofs. Here they
are exported as lemmas from the top invariant, so that the Level M case lemmas apply.
-/

namespace OM.Proof.Top

open OM.Model OM.Proof

set_option linter.deprecated false

/-- **The hypotheses of a sweep step that moves a chunk** (those of `drainStep_move`, and the shape
facts the Level M program needs), from the order invariant: the proof of `Shape.drain_run`. -/
theorem Shape.drain_move_hyps {s : Core} {cl : List Nat} {ord : Nat → List Nat} (S : Shape (ts s) cl ord) {v : Nat}
    (hg : ghostN (ts s) v) (hne : rng (ts s) cl v ≠ []) (hL : LList (cN s) (cP s) s.firstChunk cl) :
    let y := dsY s v
    let h := ht (ts s) v
    let pv := digit (ts s) y (h + 1)
    let vb := digit (ts s) y h
    let pt := ((nd (ts s) (pp (ts s) y (h + 1))).lab? (dsT s v)).getD 0
    let tb := ((nd (ts s) (dsT s v)).lab? (pp (ts s) y (h - 1))).getD 0
    (s.nodes.getX v).alive = true ∧ (s.nodes.getX v).first ≠ NIL ∧
    (goesLeft s v ∨
      lookup (s.nodes.getX v).side (belowY s v (s.nodes.getX v).first) = some .right ∧
      lookup (s.nodes.getX v).side (belowY s v (s.nodes.getX v).last) = some .right) ∧
    (s.nodes.getX v).height + 1 < (s.path.getX (dsY s v)).size ∧
    (s.nodes.getX ((s.path.getX (dsY s v)).getX ((s.nodes.getX v).height + 1))).lab? (dsT s v) = some pt ∧
    (s.nodes.getX (dsT s v)).lab? (belowY s v (dsY s v)) = some tb ∧
    (s.nodes.getX ((s.path.getX (dsY s v)).getX ((s.nodes.getX v).height + 1))).lab? v = some pv ∧
    (s.nodes.getX v).lab? (belowY s v (dsY s v)) = some vb ∧
    (pv <<< ((s.nodes.getX v).height * s.P.beta)) |||
        (vb <<< (((s.nodes.getX v).height - 1) * s.P.beta)) ≤ (s.C.getX (dsY s v)).tag ∧
    TagOK s (dsY s v) (dsTag s v pt tb pv vb) ∧
    1 ≤ (s.nodes.getX v).height ∧ (s.path.getX (dsY s v)).size = s.P.H + 1 ∧
    tb < 2 ^ s.P.beta ∧ vb < 2 ^ s.P.beta ∧ dsT s v ≠ v ∧ v < s.nodes.size ∧ dsT s v < s.nodes.size ∧
    dsY s v ∈ cl ∧ (s.nodes.getX v).height < s.P.H ∧
    (s.path.getX (dsY s v)).getX ((s.nodes.getX v).height + 1) < s.nodes.size := by
  intro y h pv vb pt tb
  obtain ⟨hvt, hv, htz, hlive, hht, hh1, hhH⟩ := S.ds_basics hg hne
  obtain ⟨hy, hanc, hLe, hRi, hside⟩ := S.pick hg hne
  obtain ⟨hycl, hypp, -, hbel, -⟩ := S.rng_ghost hg hy
  obtain ⟨m1, m2, m3, m4⟩ := S.ds_mem hg hne
  have hXN := (S.isN_pp hycl (by omega) (show h + 1 ≤ _ by omega)).1
  have hcl : cl.Nodup := S.ord0 ▸ S.ordNodup 0
  -- the tag of the new path
  set tag := dsTag s v pt tb pv vb with htag
  have T := dsS_sameTree (tag := tag) hvt hv htz
  have hpp := S.ds_pp hg hne tag
  have hd1 : digit (ts (dsS s v tag)) y (h + 1) = pt := by
    unfold digit; rw [T.lab?, hpp, hpp, if_neg (fun e => by omega), if_pos ⟨rfl, rfl⟩]
  have hd0 : digit (ts (dsS s v tag)) y h = tb := by
    unfold digit; rw [T.lab?, hpp, hpp, if_pos ⟨rfl, rfl⟩, if_neg (fun e => by omega)]
  have hP : (ts (dsS s v tag)).P = (ts s).P := dsS_P s v tag
  have hrep := tagUp_replace2 (s := ts s) (s' := ts (dsS s v tag)) (c := y) (c' := y)
    (by rw [hP]) (h := h) (k := (ts s).P.H) hh1 (by omega)
    (fun i _ _ hi1 hi2 => S.ds_digit hg hne tag y i hi1 (Or.inl hi2))
  have hvbl : vb < 2 ^ s.P.beta := S.digit_lt hycl hh1 (by omega)
  have htbl : tb < 2 ^ s.P.beta := lab_lt S.toShapeT hlive.1 (getD_of_mem m2)
  have hor1 := lor_shift_eq_add (pv := pv) (h := h) hvbl hh1
  have hor2 := lor_shift_eq_add (pv := pt) (h := h) htbl hh1
  have htagy : (s.C.getX y).tag = tagF (ts s) y := S.tags y hycl
  have e1 : tagF (ts (dsS s v tag)) y = tagF (ts s) y -
      (pv * 2 ^ (h * s.P.beta) + vb * 2 ^ ((h - 1) * s.P.beta)) +
      (pt * 2 ^ (h * s.P.beta) + tb * 2 ^ ((h - 1) * s.P.beta)) := by
    unfold tagF; rw [hP, hrep.2, hd1, hd0]; rfl
  have e2 : tag = (s.C.getX y).tag - (pv * 2 ^ (h * s.P.beta) + vb * 2 ^ ((h - 1) * s.P.beta)) +
      (pt * 2 ^ (h * s.P.beta) + tb * 2 ^ ((h - 1) * s.P.beta)) := by
    rw [htag]; unfold dsTag
    show (s.C.getX y).tag - ((pv <<< (h * s.P.beta)) ||| (vb <<< ((h - 1) * s.P.beta))) +
      ((pt <<< (h * s.P.beta)) ||| (tb <<< ((h - 1) * s.P.beta))) = _
    rw [hor1, hor2]
  have hnew : tag = tagF (ts (dsS s v tag)) y := by rw [e1, e2, htagy]
  have hpv : pv = ((nd (ts s) (pp (ts s) y (h + 1))).lab? v).getD 0 := by
    simp only [pv, digit, Nat.add_sub_cancel]; rw [show pp (ts s) y h = v from hypp]
  have hvb' : vb = ((nd (ts s) v).lab? (pp (ts s) y (h - 1))).getD 0 := by
    simp only [vb, digit]; rw [show pp (ts s) y h = v from hypp]
  refine ⟨hg.1.2.2, ?_, hside, ?_, getD_of_mem m1, ?_, (by rw [hpv]; exact getD_of_mem m3), ?_, ?_, ?_,
    hh1, S.pathSize y hycl, htbl, hvbl, Ne.symm hvt, hv, htz, hycl, hhH, ?_⟩
  · obtain ⟨hf, -⟩ := S.ends v hg.1
    show (nd (ts s) v).first ≠ NIL
    rw [hf]
    exact fun e => hL.nonil (e ▸ (S.rng_sub v).subset (headD_mem hne NIL))
  · show h + 1 < ((ts s).path.getX y).size
    rw [S.pathSize y hycl]; omega
  · show (nd (ts s) (dsT s v)).lab? (belowY s v y) = some tb
    rw [hbel]; exact getD_of_mem m2
  · show (nd (ts s) v).lab? (belowY s v y) = some vb
    rw [hbel, hvb']; exact getD_of_mem m4
  · show (pv <<< (h * s.P.beta)) ||| (vb <<< ((h - 1) * s.P.beta)) ≤ (s.C.getX y).tag
    rw [hor1, htagy]; unfold tagF; exact hrep.1
  · -- the guard: the new tag lies between the neighbours' tags (Lemma T1 after the step)
    have ST := S.drain_shapeT hg hne tag
    refine ⟨fun hp => ?_, fun hn => ?_⟩
    · rw [hL.prev y hycl] at hp ⊢
      generalize hq : predOf cl y = q at hp ⊢
      obtain ⟨l1, l2, e⟩ := predOf_split hq hp
      have hb : Before cl q y := by
        rw [e]
        have : l1 ++ q :: y :: l2 = (l1 ++ [q]) ++ y :: l2 := by simp
        rw [this]; exact before_split (by simp)
      have hpcl := hb.mem_left
      have hpy := hb.ne hcl
      show (s.C.getX q).tag < tag
      rw [show (s.C.getX q).tag = (ts s).tag q from rfl, S.tags _ hpcl,
        ← S.ds_tagF_other hg hne tag _ hpy]
      exact lt_of_lt_of_eq (ST.tagF_lt hb) hnew.symm
    · rw [hL.next y hycl] at hn ⊢
      generalize hq : succOf cl y = q at hn ⊢
      obtain ⟨l1, l2, e⟩ := succOf_split hq hn
      have hb : Before cl y q := by
        rw [e]
        have : l1 ++ y :: q :: l2 = (l1 ++ [y]) ++ q :: l2 := by simp
        rw [this]; exact before_split (by simp)
      have hpcl := hb.mem_right
      have hpy := hb.ne hcl
      show tag < (s.C.getX q).tag
      rw [show (s.C.getX q).tag = (ts s).tag q from rfl, S.tags _ hpcl,
        ← S.ds_tagF_other hg hne tag _ (Ne.symm hpy)]
      exact lt_of_eq_of_lt hnew (ST.tagF_lt hb)
  · have h2 := hXN.2.1
    unfold pp at h2; rw [if_neg (by omega)] at h2; exact h2


theorem len_le_two_of {l : List Nat} {a b : Nat} (hnd : l.Nodup) (h : ∀ x ∈ l, x = a ∨ x = b) : l.length ≤ 2 := by
  have hs : l.toFinset ⊆ {a, b} := fun x hx => by
    rcases h x (List.mem_toFinset.mp hx) with e | e <;> simp [e]
  rw [← List.toFinset_card_of_nodup hnd]
  exact (Finset.card_le_card hs).trans (Finset.card_le_two)

/-- An entry lies in at most two tables (invariant Q). -/
theorem Shape.tabs_len {t : TS} {cl : List Nat} {ord : Nat → List Nat} (S : Shape t cl ord) {h e : Nat}
    (he : Ent ord h e) : (tabs t h e).length ≤ 2 :=
  len_le_two_of (S.tabsNodup h e he) (fun X hX => S.Q h e X he hX)

/-- **The hypotheses of a sweep step that ends the drain** (those of `drainStep_finish`, and the
shape facts the Level M program needs). -/
theorem Shape.drain_finish_hyps {s : Core} {cl : List Nat} {ord : Nat → List Nat} (S : Shape (ts s) cl ord)
    {v : Nat} (hg : ghostN (ts s) v) (hemp : rng (ts s) cl v = []) :
    (s.nodes.getX v).alive = true ∧ (s.nodes.getX v).first = NIL ∧ (s.nodes.getX v).inTables.Nodup ∧
    (∀ T ∈ (s.nodes.getX v).inTables, v ∈ (s.nodes.getX T).order) ∧ v ≠ 0 ∧ v < s.nodes.size ∧
    ((s.nodes.getX v).height - 1 ≠ 0 → v ∉ (s.nodes.getX v).order) ∧
    (∀ T ∈ (s.nodes.getX v).inTables, T < s.nodes.size) ∧
    (s.nodes.getX v).t1 < s.nodes.size ∧ (s.nodes.getX v).t2 < s.nodes.size ∧
    (∀ e ∈ (s.nodes.getX v).order, (s.nodes.getX v).height - 1 ≠ 0 →
      e < s.nodes.size ∧ (s.nodes.getX e).inTables.length ≤ 2) ∧
    (∀ e ∈ (s.nodes.getX v).order, (s.nodes.getX v).height - 1 = 0 → e ∈ cl ∧ (s.cin.getX e).length ≤ 2) := by
  obtain ⟨hv, hno, hni, hvo, hvi, h1, h2, h12, ho1, ho2, hi1, hi2, hoi, hin, hent⟩ := S.fin_facts hg
  obtain ⟨hl1, hl2, -, -, -, -, -, -, -, -, -⟩ := S.ghost v hg
  refine ⟨hg.1.2.2, ?_, hni, fun T hT => ?_, hg.1.1, hv, hvo, fun T hT => (hin T hT).1.2.1, hl1.1.2.1, hl2.1.2.1,
    fun e he h0 => ⟨(hent e he h0).1.2.1, ?_⟩, fun e he h0 => ?_⟩
  · obtain ⟨hf, -⟩ := S.ends v hg.1
    show (nd (ts s) v).first = NIL
    rw [hf, hemp]; rfl
  · have hvent : Ent ord (ht (ts s) v) v :=
      (S.ordMem _ (S.htN v hg.1).1 (S.htN v hg.1).2 v).mpr ⟨hg.1, rfl⟩
    have := S.tabsIff _ v T hvent
    unfold tabs at this; rw [if_neg (by have := (S.htN v hg.1).1; omega)] at this
    exact (this.mp hT).2.2
  · have hE : Ent ord (ht (ts s) v - 1) e := S.tabEnt v hg.1 e he
    have hL := S.tabs_len hE
    have h0' : ht (ts s) v - 1 ≠ 0 := h0
    unfold tabs at hL; rw [if_neg h0'] at hL
    exact hL
  · have hE : Ent ord (ht (ts s) v - 1) e := S.tabEnt v hg.1 e he
    have h0' : ht (ts s) v - 1 = 0 := h0
    rw [h0'] at hE
    have hE' : e ∈ ord 0 := hE
    rw [S.ord0] at hE'
    refine ⟨hE', ?_⟩
    have := S.tabs_len hE
    unfold tabs at this; rw [if_pos rfl] at this
    exact this

end OM.Proof.Top

namespace OM.Impl

open OM.Model OM.Proof OM.Proof.Top

/-- **The capacities the top structure's programs need**, at state `s`: the record counts below the
capacities (with room for the two records a step may add), node capacity covering chunk indices,
and list capacities above the invariant bounds (tables of at most 160 entries, entries in at most
2 tables). -/
structure TopCaps (κ : Caps) (s : Core) : Prop where
  N : s.nodes.size + 2 ≤ κ.tbl .N
  NC : s.C.size ≤ κ.tbl .N
  C : s.C.size + 2 ≤ κ.tbl .C
  rc : s.nodes.size + 2 ≤ κ.lrec .children
  rs : s.nodes.size + 2 ≤ κ.lrec .side
  rt : s.nodes.size + 2 ≤ κ.lrec .table
  ri : s.nodes.size + 2 ≤ κ.lrec .inTab
  rcin : s.nodes.size + s.C.size + 2 ≤ κ.lrec .cin
  alp : s.nodes.size + s.C.size + 2 ≤ κ.arr .lpar
  lt : 162 ≤ κ.lcap .table
  ls : 322 ≤ κ.lcap .side
  li : 322 ≤ κ.lcap .inTab
  lcin : 322 ≤ κ.lcap .cin
  lc : 162 ≤ κ.lcap .children
  pw : κ.pw = s.P.H + 1

/-- A table holds at most 160 entries, and so does a side list (`TabLen`). -/
theorem tab_le_160 {t : TS} {dr n0 : Nat → Nat} (h : TabLen t dr n0) (X : Nat) :
    (nd t X).table.length ≤ 160 ∧ (nd t X).side.length ≤ 160 := by
  obtain ⟨a, b, c⟩ := h X
  have : (Top.order t X).length = (nd t X).table.length := by simp [Top.order, Node.order]
  omega

/-- The cost bound of `startDrain`, from tables of at most 160 entries and entries in at most two
tables. -/
def sdBound : Nat := sdCost 160 160 2 160 160 160

theorem sdCost_le {K T I S B P : Nat} (hK : K ≤ 160) (hT : T ≤ 160) (hI : I ≤ 2) (hS : S ≤ 160) (hB : B ≤ 160)
    (hP : P ≤ 160) : sdCost K T I S B P ≤ sdBound := by
  unfold sdBound sdCost; gcongr

/-- **`startDrain` agrees at a drain start** (the context of `sr_run`). -/
theorem sdAgree_walk {κ : Caps} {s : Core} {cl : List Nat} {ord : Nat → List Nat} {dr n0 : Nat → Nat}
    {j : Job} {v : Nat} (hpc : j.pc = .walk (some v)) (hv0 : v ≠ NIL) (hI : InvJ (ts s) cl ord dr n0 (some j))
    (hlp : (nd (ts s) v).livePar ≠ NIL) (hTP : TopParams s.P) (hof : (nd (ts s) v).overflowOf = NIL)
    (hW : Wd s.P (ht (ts s) v) < (nd (ts s) v).weight + 2)
    {side : List (Nat × Side)} (hside : sSideO (wiC s v) v = some side)
    (hlook : ∀ x, lookup side x =
      if 2 ≤ ht (ts s) v ∧ x ∈ sEntries (wiC s v) v ∧ (nd (ts s) x).draining = true then
        lookup (sidesOf (order (ts s) v) ((nd (ts s) v).children.getD (sK (wiC s v) v) 0)) (nd (ts s) x).t1
      else lookup (sidesOf (order (ts s) v) ((nd (ts s) v).children.getD (sK (wiC s v) v) 0)) x)
    (hcl : CLok s cl) (K : TopCaps κ s) :
    ∃ D, D ≤ sdBound ∧ SDAgree κ (wiC s v) v D := by
  have S := hI.shape
  obtain ⟨hvl, -⟩ := sd_live hpc hv0 hI hlp
  obtain ⟨hl, hlh, hvL⟩ := sd_up hpc hv0 hI hlp
  obtain ⟨h1, hhH⟩ := sd_ht hpc hv0 hI hlp
  obtain ⟨hk2, hk1, hkn⟩ := sp_k hpc hv0 hI hlp hTP hof hW
  have H := sr_hyps hpc hv0 hI hlp hTP hof hW hlook
  have W := wiC_sameTree s v
  have hsz : (wiC s v).nodes.size = s.nodes.size := by simp [wiC]
  have hCsz : (wiC s v).C.size = s.C.size := rfl
  have hent : Ent ord (ht (ts s) v) v := (S.ordMem _ h1 (S.htN v hvl.1).2 v).mpr ⟨hvl.1, rfl⟩
  have hTL := tab_le_160 hI.len
  have hsh : sH (wiC s v) v = ht (ts s) v := sd_h_eq s v
  obtain ⟨hknd, hksub, hk⟩ := S.kids v hvl
  -- the entries and children, by height
  have hkeys : ∀ e ∈ ((wiC s v).nodes.getX v).table.map (·.1),
      (ht (ts s) v - 1 ≠ 0 → e < s.nodes.size) ∧ (ht (ts s) v - 1 = 0 → e < s.C.size) := by
    intro e he
    have hwt : ((wiC s v).nodes.getX v).table = (nd (ts s) v).table := W.table v
    have he' : e ∈ Top.order (ts s) v := by rw [hwt] at he; simpa [Top.order, Node.order] using he
    have hE : Ent ord (ht (ts s) v - 1) e := S.tabEnt v hvl.1 e he'
    refine ⟨fun h0 => ?_, fun h0 => ?_⟩
    · exact ((S.ordMem _ (by omega) (by have := (S.htN v hvl.1).2; omega) e).mp hE).1.2.1
    · rw [h0] at hE
      have hE0 : e ∈ ord 0 := hE
      rw [S.ord0] at hE0
      have := (hcl.2 e).mp hE0; omega
  have hkid : ∀ e ∈ (nd (ts s) v).children,
      (ht (ts s) v ≠ 1 → e < s.nodes.size ∧ e ≠ v) ∧ (ht (ts s) v = 1 → e < s.C.size) := by
    intro e he
    refine ⟨fun h0 => ⟨H.kid h0 e he, fun hev => ?_⟩, fun h0 => ?_⟩
    · have hm : e ∈ ord (ht (ts s) v - 1) := hksub.subset he
      have := ((S.ordMem _ (by omega) (by have := (S.htN v hvl.1).2; omega) e).mp hm).2
      rw [hev] at this; omega
    · have hm : e ∈ ord (ht (ts s) v - 1) := hksub.subset he
      rw [h0, Nat.sub_self, S.ord0] at hm
      have := (hcl.2 e).mp hm; omega
  have hkl : (nd (ts s) v).children.length ≤ 160 := by
    have := (sp_kids_sub hpc hv0 hI hlp hTP hof hW).length_le
    have hl2 := (hTL v).1
    simp only [Top.order, Node.order, List.length_map] at this; omega
  have hpl : (nd (ts s) (nd (ts s) v).livePar).children.length ≤ 160 := by
    obtain ⟨-, hsub', -⟩ := S.kids _ hl
    have h2 := (sublist_of_subset_common hsub' (S.O1 _ hl.1) (S.ordNodup _)
      (fun e he => S.kid_mem hI.time hl he)).length_le
    have hl2 := (hTL (nd (ts s) v).livePar).1
    simp only [Top.order, Node.order, List.length_map] at h2; omega
  have hvent : Ent ord (ht (ts s) v) v := hent
  -- the tables holding `v` sit one level up
  have hTv : ∀ T ∈ (nd (ts s) v).inTables, ht (ts s) T = ht (ts s) v + 1 ∧ T < s.nodes.size := by
    intro T hT
    have := S.tabsIff _ v T hvent
    unfold tabs at this; rw [if_neg (by omega)] at this
    obtain ⟨a, b, -⟩ := this.mp hT
    exact ⟨b, a.2.1⟩
  have hinv : (nd (ts s) v).inTables.length ≤ 2 := by
    have := S.tabs_len hvent
    unfold tabs at this; rw [if_neg (by omega)] at this; exact this
  have htl : ∀ e ∈ ((wiC s v).nodes.getX v).table.map (·.1), tabsLen (wiC s v) (sH (wiC s v) v - 1) e ≤ 2 := by
    intro e he
    have hwt : ((wiC s v).nodes.getX v).table = (nd (ts s) v).table := W.table v
    have he' : e ∈ Top.order (ts s) v := by rw [hwt] at he; simpa [Top.order, Node.order] using he
    have hE : Ent ord (ht (ts s) v - 1) e := S.tabEnt v hvl.1 e he'
    have hL := S.tabs_len hE
    rw [hsh]; unfold tabsLen tabs at *
    by_cases h0 : ht (ts s) v - 1 = 0
    · rw [if_pos h0] at hL ⊢; exact hL
    · rw [if_neg h0] at hL ⊢; rw [H.w_inTables]; exact hL
  have hTt : ((wiC s v).nodes.getX v).table.length ≤ 160 := by rw [H.w_table]; exact (hTL v).1
  have hsl : side.length ≤ 160 := by
    have := sp_side_len hpc hv0 hI hlp hTP hof hW hside
    have := (hTL v).1
    simp only [Top.order, Node.order, List.length_map] at *; omega
  refine ⟨_, sdCost_le (by rw [H.w_children]; exact hkl) hTt (by rw [H.w_inTables]; exact hinv) hsl le_rfl
    (by rw [H.w_livePar, H.w_children]; exact hpl), sdAgree_ok (B := 160) (side := side) (by rw [sd_kids_eq]; exact hk2) (fun h => by omega) hside
    (fun T hT => ?_) H.t_nd
    (fun e he => by
      rw [sd_kids_eq] at he
      rw [sw_kid hpc hv0 hI hlp hTP hof hW hlook he]; rfl)
    (by rw [H.w_livePar, H.w_children]; exact hvL) H.t_hv
    (fun h => by rw [H.w_inTables] at h; have := (hTv v h).1; omega)
    (fun h0 h => by rw [H.w_children] at h; exact (hkid v h).1 (by rw [hsh] at h0; exact h0) |>.2 rfl)
    (fun h0 e he => by rw [hsz]; exact (hkeys e he).1 (by rwa [hsh] at h0))
    (fun e he => by
      by_cases h0 : ht (ts s) v - 1 = 0
      · have := (hkeys e he).2 h0
        exact ⟨by have := K.NC; omega, fun _ => by have := K.rcin; omega⟩
      · have := (hkeys e he).1 h0
        exact ⟨by have := K.N; omega, fun h => absurd (by rwa [hsh] at h) h0⟩)
    (fun h0 e he => by rw [H.w_children] at he; rw [hsz]; exact ((hkid e he).1 (by rwa [hsh] at h0)).1)
    (fun h0 e he => by
      rw [H.w_children] at he; have := (hkid e he).2 (by rwa [hsh] at h0); have := K.alp; omega)
    H.t_hL (by rw [H.w_livePar]; exact H.hLv)
    (fun T hT => by rw [H.w_table, H.w_side]; exact hTL T)
    (by rw [hsz]; exact K.N) (by rw [hsz]; exact K.rc) (by rw [hsz]; exact K.rs) (by rw [hsz]; exact K.rt)
    (by rw [hsz]; exact K.ri) (by rw [hsz]; have := K.rcin; omega) (by rw [hsz]; have := K.alp; omega)
    (fun T hT => by rw [H.w_table, H.w_side]; have := hTL T; have := K.lt; have := K.ls; omega)
    (by have := K.ls; omega) (by have := K.lt; omega)
    (by rw [H.w_inTables]; have := K.li; omega)
    (fun e he => by have := htl e he; have := K.li; have := K.lcin; split <;> omega)
    (by rw [H.w_children]; have := K.lc; omega)
    (by rw [H.w_livePar, H.w_children]; have := K.lc; omega)⟩
  · rw [H.w_inTables] at hT
    obtain ⟨A, le, Bs, htab, hA, hsd, h1, h2, -⟩ := room_up hI hTP hvl.1 hT 0 0
    exact ⟨A, le, Bs, by rw [H.w_table]; exact htab, hA, by rw [H.w_draining, H.w_side]; exact hsd, h1, h2⟩

/-- A chunk of the chunk list links to chunks of the list (or `NIL`). -/
theorem CLok.links {s : Core} {cl : List Nat} (h : CLok s cl) {c : Nat} (hc : c ∈ cl) :
    (s.C.getX c).next < s.C.size ∧ (s.C.getX c).prev < s.C.size := by
  have hc' := (h.2 c).mp hc
  have hn : (s.C.getX c).next = succOf cl c := h.1.next c hc
  have hp : (s.C.getX c).prev = predOf cl c := h.1.prev c hc
  constructor
  · rw [hn]; rcases succOf_mem_or (l := cl) (x := c) with e | e
    · exact ((h.2 _).mp e).2
    · rw [e]; simp [NIL]; omega
  · rw [hp]; rcases predOf_mem_or (l := cl) (x := c) with e | e
    · exact ((h.2 _).mp e).2
    · rw [e]; simp [NIL]; omega

/-- The cost bound of one sweep step (`drainStep`), from tables of at most 160 entries and entries
in at most two tables: the end of a drain dominates. -/
def dsBound : Nat := 300 + 160 * (171 + 100 * 160) + 2 * (301 + 200 * 160)

/-- **A sweep step that moves a chunk agrees** (outside a preparation). -/
theorem dsAgree_moveI {κ : Caps} {s : Core} {cl : List Nat} {ord : Nat → List Nat} (S : Shape (ts s) cl ord)
    {dr n0 : Nat → Nat} (hTL : TabLen (ts s) dr n0)
    {v : Nat} (hg : ghostN (ts s) v) (hne : rng (ts s) cl v ≠ []) (hcl : CLok s cl) (hprep : s.prep = none)
    (K : TopCaps κ s) : ∃ D, D ≤ dsBound ∧ DSAgree κ s v D := by
  obtain ⟨hal, hf, hside, hsz, hpt, htb, hpv, hvb, hold, hok, h1, hpsz, htbB, hvbB, htv, hvs, hts, hycl, hhH, hpr⟩ :=
    S.drain_move_hyps hg hne hcl.1
  have hfl : (s.nodes.getX v).first ∈ cl ∧ (s.nodes.getX v).last ∈ cl := by
    obtain ⟨e1, e2⟩ := S.ends v hg.1
    have e1' : (s.nodes.getX v).first = (rng (ts s) cl v).headD NIL := e1
    have e2' : (s.nodes.getX v).last = (rng (ts s) cl v).getLastD NIL := e2
    rw [e1', e2']
    refine ⟨(S.rng_sub v).subset (headD_mem hne NIL), (S.rng_sub v).subset ?_⟩
    rw [List.getLastD_eq_getLast?, List.getLast?_eq_getLast hne]; exact List.getLast_mem hne
  have hfC := ((hcl.2 _).mp hfl.1).2
  have hlC := ((hcl.2 _).mp hfl.2).2
  obtain ⟨hyN, hyP⟩ := CLok.links hcl hycl
  have hnp : ∀ c, notPrep s c := fun c => by simp [notPrep, hprep]
  have hB : ∀ X, (s.nodes.getX X).table.length ≤ 160 ∧ (s.nodes.getX X).side.length ≤ 160 :=
    fun X => tab_le_160 hTL X
  refine ⟨_, ?_, dsAgree_move hal hf hside hsz hpt htb hpv hvb hold hok h1 hpsz htbB hvbB htv hvs hts
    (by have := ((hcl.2 _).mp hycl).2; exact this) (hnp _) (hnp _)
    (by have := K.N; omega) (by have := K.N; omega) (by have := K.rs; omega) (by have := K.rt; omega)
    (by have := K.rt; omega) (by have := K.rt; omega)
    (by have := K.C; omega) (by have := K.C; omega) (by have := K.C; omega) (by have := K.C; omega)
    (by rw [K.pw]; omega)⟩
  have := hB v; have := hB (dsT s v); have := hB ((s.path.getX (dsY s v)).getX ((s.nodes.getX v).height + 1))
  unfold dsBound; omega

/-- **A sweep step that ends the drain agrees.** -/
theorem dsAgree_finishI {κ : Caps} {s : Core} {cl : List Nat} {ord : Nat → List Nat} {dr n0 : Nat → Nat}
    (S : Shape (ts s) cl ord) (hTL : TabLen (ts s) dr n0)
    {v : Nat} (hg : ghostN (ts s) v) (hemp : rng (ts s) cl v = []) (hcl : CLok s cl)
    (K : TopCaps κ s) : ∃ D, D ≤ dsBound ∧ DSAgree κ s v D := by
  obtain ⟨hal, hf, hnd, hT, hv0, hvs, hvo, hTs, ht1, ht2, hE1, hE0⟩ := S.drain_finish_hyps hg hemp
  have hvent : Ent ord (ht (ts s) v) v :=
    (S.ordMem _ (S.htN v hg.1).1 (S.htN v hg.1).2 v).mpr ⟨hg.1, rfl⟩
  have hin : (s.nodes.getX v).inTables.length ≤ 2 := by
    have := S.tabs_len hvent
    unfold tabs at this; rw [if_neg (by have := (S.htN v hg.1).1; omega)] at this; exact this
  have htv : (s.nodes.getX v).table.length ≤ 160 := (tab_le_160 hTL v).1
  refine ⟨_, ?_, dsAgree_finish (B := 160) hal hf hnd hT hv0 hvs hvo
    (by have := K.N; omega) (by have := K.rt; omega) (by have := K.ri; omega)
    (by have := K.N; omega) (by have := K.N; omega)
    (fun e he => ⟨fun h0 => by
        obtain ⟨a, b⟩ := hE0 e he h0
        have := ((hcl.2 e).mp a).2
        exact ⟨by have := K.rcin; omega, by have := K.lcin; omega, by omega⟩,
      fun h0 => by
        obtain ⟨a, b⟩ := hE1 e he h0
        exact ⟨by have := K.ri; omega, by have := K.li; omega, by omega⟩⟩)
    (fun T hT => by
      have := hTs T hT
      obtain ⟨a, b⟩ := tab_le_160 hTL T
      have a' : (s.nodes.getX T).table.length ≤ 160 := a
      have b' : (s.nodes.getX T).side.length ≤ 160 := b
      have := K.lt; have := K.ls
      exact ⟨by have := K.rt; omega, by have := K.rs; omega, by omega, by omega, a', b'⟩)⟩
  unfold dsBound
  have e1 := Nat.mul_le_mul_right (171 + 100 * 160) htv
  have e2 := Nat.mul_le_mul_right (301 + 200 * 160) hin
  omega

/-- **The funding loop's sweep step agrees**: its source is a ghost, so the step moves a chunk or
ends the drain. -/
theorem dsAgree_fund {κ : Caps} {s : Core} {cl : List Nat} {ord : Nat → List Nat} {dr n0 : Nat → Nat}
    {j : Job} {v up src k : Nat} (hcl : CLok s cl) (hprep : s.prep = none)
    (hI : InvJ (ts s) cl ord dr n0 (some { j with pc := .fund v up src k })) (K : TopCaps κ s) :
    ∃ D, D ≤ dsBound ∧ DSAgree κ s src D := by
  have S := hI.shape
  obtain ⟨-, hat⟩ := hI.job _ rfl
  simp only [JobAt] at hat
  obtain ⟨-, -, -, hg, -, -⟩ := hat
  by_cases hne : rng (ts s) cl src = []
  · exact dsAgree_finishI S hI.len hg hne hcl K
  · exact dsAgree_moveI S hI.len hg hne hcl hprep K

theorem SDAgree.mono {κ : Caps} {S : Core} {v D D' : Nat} (h : SDAgree κ S v D) (hD : D ≤ D') :
    SDAgree κ S v D' := fun S' e => by
  obtain ⟨L', c, a, b, d⟩ := h S' e; exact ⟨L', c, a, by omega, d⟩

theorem DSAgree.mono {κ : Caps} {S : Core} {v D D' : Nat} (h : DSAgree κ S v D) (hD : D ≤ D') :
    DSAgree κ S v D' := fun b S' e => by
  obtain ⟨L', c, a, b1, b2, d⟩ := h b S' e; exact ⟨L', c, a, b1, by omega, d⟩

theorem TopCaps.wiC {κ : Caps} {s : Core} (K : TopCaps κ s) (v : Nat) : TopCaps κ (OM.Proof.Top.wiC s v) := by
  have h : (OM.Proof.Top.wiC s v).nodes.size = s.nodes.size := by simp [OM.Proof.Top.wiC]
  obtain ⟨a, b, c, d, e, f, g, i, k, l, m, n, o, p, q⟩ := K
  exact ⟨by rw [h]; exact a, b, c, by rw [h]; exact d, by rw [h]; exact e, by rw [h]; exact f, by rw [h]; exact g,
    by rw [h]; exact i, by rw [h]; exact k, l, m, n, o, p, q⟩

/-- **The walk step's agreements**, at node `v` of the walk: `startDrain` where the walk starts a
drain, and the sweep step of the funding loop where `v` has an overflow source. -/
theorem walkAgree {κ : Caps} {s : Core} {cl : List Nat} {ord : Nat → List Nat} {dr n0 : Nat → Nat}
    {j : Job} {v : Nat} (hpc : j.pc = .walk (some v)) (hTP : TopParams s.P) (hcl : CLok s cl)
    (hprep : s.prep = none) (hI : InvJ (ts s) cl ord dr n0 (some j)) (K : TopCaps κ s) :
    (v ≠ NIL → ((s.nodes.getX v).livePar != NIL && !(s.nodes.getX v).draining &&
      (s.nodes.getX v).overflowOf == NIL &&
      decide ((s.nodes.getX v).weight + 2 > 2 * s.P.a ^ (s.nodes.getX v).height)) = true →
        SDAgree κ (wiC s v) v sdBound) ∧
    (v ≠ NIL → (s.nodes.getX v).overflowOf ≠ NIL → DSAgree κ (wiC s v) (s.nodes.getX v).overflowOf dsBound) := by
  refine ⟨fun hv0 hc => ?_, fun hv0 hov => ?_⟩
  · simp only [Bool.and_eq_true, bne_iff_ne, ne_eq, Bool.not_eq_true', beq_iff_eq, decide_eq_true_eq] at hc
    obtain ⟨⟨⟨h1, h2⟩, h3⟩, h4⟩ := hc
    obtain ⟨side, hside, hlook⟩ := sp_side hpc hv0 hI h1 hTP h3 (by unfold Wd ht; exact h4)
    obtain ⟨D, hD, hA⟩ := sdAgree_walk hpc hv0 hI h1 hTP h3 (by unfold Wd ht; exact h4) hside hlook hcl K
    exact hA.mono hD
  · have hno : ¬ ((nd (ts s) v).livePar ≠ NIL ∧ (nd (ts s) v).draining = false ∧
        (nd (ts s) v).overflowOf = NIL ∧ Wd s.P (ht (ts s) v) < (nd (ts s) v).weight + 2) :=
      fun h => hov h.2.2.1
    have hI' := inv_winc hpc hv0 hI hno
    have hn : walkNext (ts s) j v = { j with pc := .fund v (nd (ts s) v).livePar (srcOf (ts s) v) 0 } := by
      simp only [walkNext]; rw [if_neg (show srcOf (ts s) v ≠ NIL from hov)]
    rw [hn] at hI'
    obtain ⟨D, hD, hA⟩ := dsAgree_fund (hcl.topRel (wiC_topRel s v)) hprep hI' (K.wiC v)
    exact hA.mono hD

/-- A copy step keeps the node count and the path of the chunk copied from. -/
theorem copyS_frame (t : TS) (j : Job) (l : Nat) (hxy : j.x ≠ j.y) (hxz : j.x ≠ j.z) :
    (OM.Proof.Top.copyS t j l).nodes.size = t.nodes.size ∧ (OM.Proof.Top.copyS t j l).path.getX j.x = t.path.getX j.x := by
  unfold OM.Proof.Top.copyS; dsimp only
  split_ifs <;> simp [Array.getX_setX, Ne.symm hxy, Ne.symm hxz, hxy, hxz]

theorem copyRest_frame (j : Job) (H : Nat) (hxy : j.x ≠ j.y) (hxz : j.x ≠ j.z) : ∀ k t l, H + 1 - l = k →
    (copyRest j H t l).nodes.size = t.nodes.size ∧ (copyRest j H t l).path.getX j.x = t.path.getX j.x := by
  intro k
  induction k with
  | zero => intro t l hk; unfold copyRest; rw [if_neg (by omega)]; exact ⟨rfl, rfl⟩
  | succ k ih =>
    intro t l hk; unfold copyRest; rw [if_pos (by omega)]
    obtain ⟨a, b⟩ := ih (OM.Proof.Top.copyS t j l) (l + 1) (by omega)
    obtain ⟨c, d⟩ := copyS_frame t j l hxy hxz
    exact ⟨a.trans c, b.trans d⟩

/-- The running job's chunks: in the chunk list, distinct, not `NIL`. -/
theorem job_chunks {t : TS} {s : Core} {cl : List Nat} {j : Job} (hcl : CLok s cl) (hJ : JobOK t cl j) :
    j.x ∈ cl ∧ j.y ∈ cl ∧ j.z ∈ cl ∧ j.x ≠ j.y ∧ j.x ≠ j.z ∧ j.y ≠ j.z := by
  obtain ⟨A, B, e⟩ := hJ.pos
  have hnd := hcl.1.nodup
  rw [e] at hnd ⊢
  simp only [List.nodup_append, List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false] at hnd
  refine ⟨by simp, by simp, by simp, fun h => ?_, fun h => ?_, fun h => ?_⟩ <;> simp_all

/-- **A copy step agrees.** -/
theorem copyAgree {κ : Caps} {s : Core} {cl : List Nat} {ord : Nat → List Nat} {dr n0 : Nat → Nat}
    {j : Job} {l : Nat} (hpc : j.pc = .copy l) (hres : s.resJob = some j) (hcl : CLok s cl) (hprep : s.prep = none)
    (hI : InvJ (finS (ts s) (some j)) cl ord dr n0 (some j)) (K : TopCaps κ s) : JobAgree κ s j 140 := by
  intro r t1 h
  rw [jobStep_copy hpc] at h
  injection h with hr ht; subst hr; subst ht
  have hJ := hI.job j rfl
  obtain ⟨hx, hy, hz, hxy, hxz, hyz⟩ := job_chunks hcl hJ
  have hat := hJ.at_
  simp only [JobAt, hpc] at hat
  obtain ⟨hl1, hlH, -⟩ := hat
  have hfin : finS (ts s) (some j) = copyRest j s.P.H (ts s) l := by simp only [finS, hpc]; rfl
  have hP : (finS (ts s) (some j)).P = s.P := by rw [hfin]; exact copyRest_P j _ _ _ _ rfl
  rw [hP] at hlH
  obtain ⟨hsz, hpx⟩ := copyRest_frame j s.P.H hxy hxz _ (ts s) l rfl
  have hN := (hI.shape.toShapeT.isN_pp hx hl1 (by rw [hP]; exact hlH)).1.2.1
  unfold pp pth at hN; rw [if_neg (by omega)] at hN
  rw [← hfin] at hsz hpx
  rw [hpx, hsz] at hN
  have hC : ∀ c ∈ cl, c < κ.tbl .C := fun c hc => by have := ((hcl.2 c).mp hc).2; have := K.C; omega
  have hnp : ∀ c, notPrep s c := fun c => by simp [notPrep, hprep]
  obtain ⟨L', c, e, hc⟩ := jobStepS_copy (κ := κ) (L := OM.Machine.State.setLocs (fun _ => 0) [] []) hres hpc
    (fun h => hcl.1.nonil (h ▸ hx)) hyz (hnp _) (hnp _) (hnp _) (hC _ hx) (hC _ hy) (hC _ hz)
    (by rw [K.pw]; omega) (by have := K.N; have hN' : (s.path.getX j.x).getX l < s.nodes.size := hN; omega)
  exact ⟨L', c, e, hc⟩

/-- The cost bound of one job step at Level M. -/
def jobBound : Nat := sdBound + dsBound + 300

/-- **Every job step agrees**, under the top invariant, outside a preparation, with the capacities. -/
theorem jobAgree {κ : Caps} {s : Core} {j : Job} (hT : TopInv s) (hres : s.resJob = some j) (hprep : s.prep = none)
    (hpow : s.P.a = 2 ^ Nat.log2 s.P.a) (K : TopCaps κ s) : JobAgree κ s j jobBound := by
  obtain ⟨hTP, cl, ord, dr, n0, hL, hC, hI⟩ := hT
  rw [hres] at hI
  have hcl : CLok s cl := ⟨hL, hC⟩
  intro r t1 h
  cases hpc : j.pc with
  | copy l =>
    obtain ⟨L', c, e, hc⟩ := copyAgree hpc hres hcl hprep hI K r t1 h
    exact ⟨L', c, e, by unfold jobBound; omega⟩
  | walk ov =>
    have hfin : finS (ts s) (some j) = ts s := by simp only [finS, hpc]
    rw [hfin] at hI
    cases ov with
    | none =>
      obtain ⟨hI', hl, -⟩ := walkNone_inv hpc hI
      obtain ⟨hsd, hds⟩ := walkAgree (j := { j with pc := .walk (some (lpr (ts s) j.y)) }) rfl hTP hcl hprep hI' K
      have hy := (job_chunks hcl (hI.job j rfl)).2.1
      have hyC := ((hcl.2 _).mp hy).2
      have hls : s.lpar.getX j.y < s.nodes.size := hl.1.2.1
      obtain ⟨L', c, e, hc⟩ := jobStepS_walkNone (κ := κ) (L := OM.Machine.State.setLocs (fun _ => 0) [] [])
        hres hpc (by have := K.alp; omega) (fun _ => hls) (fun _ => by have := K.N; omega) hsd hds hpow h
      exact ⟨L', c, e, by unfold jobBound; omega⟩
    | some v =>
      obtain ⟨hsd, hds⟩ := walkAgree hpc hTP hcl hprep hI K
      have hat := (hI.job j rfl).at_
      simp only [JobAt, hpc] at hat
      have hvs : v ≠ 0 → v < s.nodes.size := fun h0 => by
        rcases hat with e | ⟨hl, -⟩
        · exact absurd e h0
        · exact hl.1.2.1
      obtain ⟨L', c, e, hc⟩ := jobStepS_walkSome (κ := κ) (L := OM.Machine.State.setLocs (fun _ => 0) [] [])
        hres hpc hvs (fun h0 => by have := hvs h0; have := K.N; omega) hsd hds hpow h
      exact ⟨L', c, e, by unfold jobBound; omega⟩
  | afterDrain v up =>
    have hfin : finS (ts s) (some j) = ts s := by simp only [finS, hpc]
    rw [hfin] at hI
    have hat := (hI.job j rfl).at_
    simp only [JobAt, hpc] at hat
    obtain ⟨hg, -, -⟩ := hat
    obtain ⟨-, -, -, -, -, -, -, -, hgs, -⟩ := hI.shape.ghost v hg
    have hvs : v < s.nodes.size := hg.1.2.1
    obtain ⟨L', c, e, hc⟩ := jobStepS_after (κ := κ) (L := OM.Machine.State.setLocs (fun _ => 0) [] []) (D := 0)
      hres hpc (by have := K.N; omega) (fun hne => absurd hgs hne) h
    exact ⟨L', c, e, by unfold jobBound; omega⟩
  | fund v up src k =>
    have hfin : finS (ts s) (some j) = ts s := by simp only [finS, hpc]
    rw [hfin] at hI
    rw [job_eta hpc] at hI
    obtain ⟨D, hD, hA⟩ := dsAgree_fund hcl hprep hI K
    obtain ⟨L', c, e, hc⟩ := jobStepS_fund (κ := κ) (L := OM.Machine.State.setLocs (fun _ => 0) [] []) hres hpc hA h
    exact ⟨L', c, e, by unfold jobBound; omega⟩

end OM.Impl
