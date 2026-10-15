import OM.Impl.Job
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
    dsY s v ∈ cl ∧ (s.nodes.getX v).height < s.P.H := by
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
    hh1, S.pathSize y hycl, htbl, hvbl, Ne.symm hvt, hv, htz, hycl, hhH⟩
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
