import OM.Proof.Top.Lists
import OM.Proof.Top.RunDrain

/-!
# M5: a sweep step keeps the invariant

`drainStep src`, in the funding loop of a job (`.fund v up src k`, `k < s`), on a ghost with a
non-empty range: all its lookups succeed, its tag passes the guard, and the invariant holds
afterwards with `k + 1` (`docs/PROOF.md` §4.5.1, `SweepStep`).
-/

namespace OM.Proof.Top

open OM.Model OM.Proof

set_option linter.deprecated false

/-! ### The state after a sweep step -/

section views
variable (s : Core) (v tag : Nat)

theorem dsS_P : (dsS s v tag).P = s.P := by unfold dsS; dsimp only; split_ifs <;> rfl
theorem dsS_cin : (dsS s v tag).cin = s.cin := by unfold dsS; dsimp only; split_ifs <;> rfl
theorem dsS_lpar : (dsS s v tag).lpar = s.lpar := by unfold dsS; dsimp only; split_ifs <;> rfl
theorem dsS_resJob : (dsS s v tag).resJob = s.resJob := by
  unfold dsS; dsimp only; split_ifs <;> rfl
theorem dsS_path : (dsS s v tag).path =
    s.path.setX (dsY s v) ((s.path.getX (dsY s v)).setX (s.nodes.getX v).height (dsT s v)) := by
  unfold dsS; dsimp only; split_ifs <;> rfl
theorem dsS_C : (dsS s v tag).C = s.C.modify (dsY s v) fun C => { C with tag := tag } := by
  unfold dsS; dsimp only; split_ifs <;> rfl
theorem dsS_size : (dsS s v tag).nodes.size = s.nodes.size := by
  unfold dsS; dsimp only; split_ifs <;> simp

/-- New range pointers of the ghost. -/
def dsFirstV : Nat :=
  if (s.nodes.getX v).first == (s.nodes.getX v).last then NIL
  else if goesLeft s v then (s.C.getX (dsY s v)).next else (s.nodes.getX v).first
def dsLastV : Nat :=
  if (s.nodes.getX v).first == (s.nodes.getX v).last then NIL
  else if goesLeft s v then (s.nodes.getX v).last else (s.C.getX (dsY s v)).prev
/-- New range pointers of the target. -/
def dsFirstT : Nat :=
  if goesLeft s v then
    (if (s.nodes.getX (dsT s v)).first == NIL then dsY s v else (s.nodes.getX (dsT s v)).first)
  else dsY s v
def dsLastT : Nat :=
  if goesLeft s v then dsY s v
  else (if (s.nodes.getX (dsT s v)).last == NIL then dsY s v else (s.nodes.getX (dsT s v)).last)

theorem dsS_node (hvt : v ≠ dsT s v) (hv : v < s.nodes.size) (ht : dsT s v < s.nodes.size)
    (u : Nat) : (dsS s v tag).nodes.getX u =
      if u = v then { s.nodes.getX u with first := dsFirstV s v, last := dsLastV s v }
      else if u = dsT s v then { s.nodes.getX u with first := dsFirstT s v, last := dsLastT s v }
      else s.nodes.getX u := by
  unfold dsS dsFirstV dsLastV dsFirstT dsLastT
  dsimp only
  have hvt' := Ne.symm hvt
  by_cases huv : u = v
  · subst huv
    split_ifs <;> simp_all [Array.getX_modify]
  · by_cases hut : u = dsT s v
    · subst hut
      split_ifs <;> simp_all [Array.getX_modify]
    · split_ifs <;> simp [Array.getX_modify, huv, hut, Ne.symm huv, Ne.symm hut]

end views

/-! ### The top structure's part after a sweep step -/

section tsviews
variable {s : Core} {v tag : Nat} (hvt : v ≠ dsT s v) (hv : v < s.nodes.size)
  (ht : dsT s v < s.nodes.size)
include hvt hv ht

theorem dsS_sameTree : SameTree (ts s) (ts (dsS s v tag)) := by
  refine ⟨dsS_P s v tag, dsS_size s v tag, dsS_cin s v tag, dsS_lpar s v tag, fun u => ?_⟩
  show (dsS s v tag).nodes.getX u = { s.nodes.getX u with
    first := ((dsS s v tag).nodes.getX u).first, last := ((dsS s v tag).nodes.getX u).last }
  rw [dsS_node s v tag hvt hv ht u]
  split_ifs <;> rfl

theorem dsS_first (u : Nat) : (nd (ts (dsS s v tag)) u).first =
    if u = v then dsFirstV s v else if u = dsT s v then dsFirstT s v else (nd (ts s) u).first := by
  show ((dsS s v tag).nodes.getX u).first = _
  rw [dsS_node s v tag hvt hv ht u]
  split_ifs <;> rfl

theorem dsS_last (u : Nat) : (nd (ts (dsS s v tag)) u).last =
    if u = v then dsLastV s v else if u = dsT s v then dsLastT s v else (nd (ts s) u).last := by
  show ((dsS s v tag).nodes.getX u).last = _
  rw [dsS_node s v tag hvt hv ht u]
  split_ifs <;> rfl

end tsviews

theorem dsS_pp (s : Core) (v tag : Nat) (h1 : 1 ≤ (s.nodes.getX v).height) (c j : Nat) :
    pp (ts (dsS s v tag)) c j =
      if c = dsY s v ∧ j = (s.nodes.getX v).height then dsT s v else pp (ts s) c j := by
  unfold pp pth
  show (if j = 0 then c else ((dsS s v tag).path.getX c).getX j) = _
  rw [dsS_path, Array.getX_setX]
  by_cases hj : j = 0
  · subst hj; simp only [if_true]; split_ifs <;> first | rfl | omega
  · simp only [if_neg hj]
    by_cases hc : c = dsY s v
    · subst hc; rw [if_pos rfl, Array.getX_setX]
      by_cases hjh : j = (s.nodes.getX v).height
      · simp [hjh]
      · simp [hjh]; rfl
    · simp [hc]; rfl

theorem dsS_tag (s : Core) (v tag : Nat) (hy : dsY s v < s.C.size) (c : Nat) :
    (ts (dsS s v tag)).tag c = if c = dsY s v then tag else (ts s).tag c := by
  show ((dsS s v tag).C.getX c).tag = _
  rw [dsS_C, Array.getX_modify]
  by_cases hc : c = dsY s v
  · subst hc; simp [hy]
  · simp [Ne.symm hc, hc]; rfl

/-! ### What a sweep step finds -/

theorem lab_some_of_mem {s : TS} {X e : Nat} (h : e ∈ order s X) :
    ∃ l, (nd s X).lab? e = some l := by
  obtain ⟨q, hq, hq1⟩ := List.mem_map.mp h
  have : ((nd s X).table.find? (·.1 == e)).isSome := List.find?_isSome.mpr ⟨q, hq, by simp [hq1]⟩
  obtain ⟨q', hq'⟩ := Option.isSome_iff_exists.mp this
  exact ⟨q'.2, by simp [Node.lab?, lookup, hq']⟩

theorem getD_of_mem {s : TS} {X e : Nat} (h : e ∈ order s X) :
    (nd s X).lab? e = some (((nd s X).lab? e).getD 0) := by
  obtain ⟨l, hl⟩ := lab_some_of_mem h; rw [hl]; rfl

theorem lab_lt {s : TS} {cl ord} (S : ShapeT s cl ord) {X e l : Nat} (hX : isN s X)
    (h : (nd s X).lab? e = some l) : l < 2 ^ s.P.beta := by
  unfold Node.lab? lookup at h
  obtain ⟨q, hq, rfl⟩ := Option.map_eq_some_iff.mp h
  exact (S.labs_ok hX).2 _ (List.mem_map.mpr ⟨q, List.mem_of_find?_eq_some hq, rfl⟩)

section facts
variable {s : Core} {cl : List Nat} {ord : Nat → List Nat} (S : Shape (ts s) cl ord)
include S

theorem Shape.ghost_ne_anc {v c j : Nat} (hc : c ∈ cl) (hj1 : 1 ≤ j) (hj : j ≤ (ts s).P.H)
    (hg : ghostN (ts s) v) : anc (ts s) c j ≠ v := by
  intro e
  have := (S.anc_live hc j hj1 hj).1
  rw [e] at this
  exact absurd hg.2 (by rw [this.2]; simp)

/-- A chunk in a ghost's range: its live ancestor is a target, and the entry below has a side. -/
theorem Shape.rng_ghost {v c : Nat} (hg : ghostN (ts s) v) (hc : c ∈ rng (ts s) cl v) :
    c ∈ cl ∧ pp (ts s) c (ht (ts s) v) = v ∧
      (anc (ts s) c (ht (ts s) v) = (nd (ts s) v).t1 ∨ anc (ts s) c (ht (ts s) v) = (nd (ts s) v).t2) ∧
      belowY s v c = pp (ts s) c (ht (ts s) v - 1) ∧
      lookup (nd (ts s) v).side (pp (ts s) c (ht (ts s) v - 1)) =
        some (if anc (ts s) c (ht (ts s) v) = (nd (ts s) v).t1 then .left else .right) := by
  simp only [rng, List.mem_filter, decide_eq_true_eq] at hc
  obtain ⟨hcl, hpp⟩ := hc
  obtain ⟨hh1, hhH⟩ := S.htN v hg.1
  refine ⟨hcl, hpp, ?_, ?_, ?_⟩
  · rcases S.P c hcl _ hh1 hhH with h | ⟨-, h⟩
    · exact absurd (h ▸ hpp) (S.ghost_ne_anc hcl hh1 hhH hg)
    · rw [hpp] at h; exact h
  · unfold belowY pp
    show (if (nd (ts s) v).height == 1 then c else pth (ts s) c ((nd (ts s) v).height - 1)) = _
    by_cases h1 : (nd (ts s) v).height = 1
    · simp [h1, ht]
    · have h2 : (nd (ts s) v).height - 1 ≠ 0 := by simp only [ht] at hh1; omega
      simp [h1, ht, h2]
  · have hw := S.W3 c hcl _ hh1 hhH
    rw [hpp] at hw
    rw [S.side v hg _ hw, S.par_pp hcl hh1 hhH]

theorem Shape.t1_ne_t2 {v : Nat} (hg : ghostN (ts s) v) : (nd (ts s) v).t1 ≠ (nd (ts s) v).t2 := by
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, hinf⟩ := S.ghost v hg
  have := (before_of_infix2 (infix3_left hinf)).trans (before_of_infix2 (infix3_right hinf))
    (S.ordNodup _)
  exact this.ne (S.ordNodup _)

theorem Shape.rng_sub (v : Nat) : (rng (ts s) cl v).Sublist cl := List.filter_sublist

/-- **The sweep step's pick**: the chunk moved is in the range, its live ancestor is the
target, it is the first (moving left) or the last (moving right) of the range. -/
theorem Shape.pick {v : Nat} (hg : ghostN (ts s) v) (hne : rng (ts s) cl v ≠ []) :
    dsY s v ∈ rng (ts s) cl v ∧ anc (ts s) (dsY s v) (ht (ts s) v) = dsT s v ∧
      (goesLeft s v → dsY s v = (rng (ts s) cl v).headD NIL ∧ dsT s v = (nd (ts s) v).t1) ∧
      (¬ goesLeft s v → dsY s v = (rng (ts s) cl v).getLastD NIL ∧ dsT s v = (nd (ts s) v).t2) ∧
      (goesLeft s v ∨
        lookup (s.nodes.getX v).side (belowY s v (s.nodes.getX v).first) = some .right ∧
        lookup (s.nodes.getX v).side (belowY s v (s.nodes.getX v).last) = some .right) := by
  have hcl : (cl).Nodup := S.ord0 ▸ S.ordNodup 0
  obtain ⟨hf, hl⟩ := S.ends v hg.1
  have hfm := headD_mem hne NIL
  have hlm := getLastD_mem hne NIL
  obtain ⟨-, -, hfa, hfb, hfs⟩ := S.rng_ghost hg hfm
  obtain ⟨-, -, hla, hlb, hls⟩ := S.rng_ghost hg hlm
  have h12 := S.t1_ne_t2 hg
  have hfirst : (s.nodes.getX v).first = (rng (ts s) cl v).headD NIL := hf
  have hlast : (s.nodes.getX v).last = (rng (ts s) cl v).getLastD NIL := hl
  have hgl : goesLeft s v ↔ anc (ts s) ((rng (ts s) cl v).headD NIL) (ht (ts s) v) = (nd (ts s) v).t1 := by
    unfold goesLeft; rw [hfirst, hfb]
    show lookup (nd (ts s) v).side _ = _ ↔ _
    rw [hfs]; split <;> simp_all
  by_cases hgo : goesLeft s v
  · have hy : dsY s v = (rng (ts s) cl v).headD NIL := by simp [dsY, hgo, hfirst]
    have ht' : dsT s v = (nd (ts s) v).t1 := by simp [dsT, hgo]; rfl
    refine ⟨by rw [hy]; exact hfm, by rw [hy, ht']; exact hgl.mp hgo, fun _ => ⟨hy, ht'⟩,
      fun h => absurd hgo h, Or.inl hgo⟩
  · have hy : dsY s v = (rng (ts s) cl v).getLastD NIL := by simp [dsY, hgo, hlast]
    have ht' : dsT s v = (nd (ts s) v).t2 := by simp [dsT, hgo]; rfl
    have hf2 : anc (ts s) ((rng (ts s) cl v).headD NIL) (ht (ts s) v) = (nd (ts s) v).t2 :=
      hfa.resolve_left (fun h => hgo (hgl.mpr h))
    have hl2 : anc (ts s) ((rng (ts s) cl v).getLastD NIL) (ht (ts s) v) = (nd (ts s) v).t2 := by
      rcases hla with h | h
      · exfalso
        by_cases he : (rng (ts s) cl v).getLastD NIL = (rng (ts s) cl v).headD NIL
        · rw [he, hf2] at h; exact h12 h.symm
        · have hb := (before_headD hlm he).mono (S.rng_sub v)
          obtain ⟨hh1, hhH⟩ := S.htN v hg.1
          rcases S.anc_mono hb _ hhH with h3 | h3
          · rw [hf2, h] at h3; exact h12 h3.symm
          · rw [hf2, h] at h3
            obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, hinf⟩ := S.ghost v hg
            have h4 := (before_of_infix2 (infix3_left hinf)).trans
              (before_of_infix2 (infix3_right hinf)) (S.ordNodup _)
            exact h3.asymm (S.ordNodup _) h4
      · exact h
    refine ⟨by rw [hy]; exact hlm, by rw [hy, ht']; exact hl2, fun h => absurd h hgo,
      fun _ => ⟨hy, ht'⟩, Or.inr ⟨?_, ?_⟩⟩
    · rw [hfirst, hfb]; show lookup (nd (ts s) v).side _ = _; rw [hfs, if_neg (by rw [hf2]; exact Ne.symm h12)]
    · rw [hlast, hlb]; show lookup (nd (ts s) v).side _ = _; rw [hls, if_neg (by rw [hl2]; exact Ne.symm h12)]

/-! ### The tag part of the invariant after the step -/

variable {v : Nat} (hg : ghostN (ts s) v) (hne : rng (ts s) cl v ≠ [])
include hg hne

theorem Shape.ds_basics :
    v ≠ dsT s v ∧ v < s.nodes.size ∧ dsT s v < s.nodes.size ∧ liveN (ts s) (dsT s v) ∧
      ht (ts s) (dsT s v) = ht (ts s) v ∧ 1 ≤ ht (ts s) v ∧ ht (ts s) v < (ts s).P.H := by
  obtain ⟨hy, hanc, hL, hR, -⟩ := S.pick hg hne
  obtain ⟨hl1, hl2, hh1, hh2, -, -, -, -, -, hlt, -⟩ := S.ghost v hg
  have htt : dsT s v = (nd (ts s) v).t1 ∨ dsT s v = (nd (ts s) v).t2 := by
    by_cases h : goesLeft s v
    · exact Or.inl (hL h).2
    · exact Or.inr (hR h).2
  have hlive : liveN (ts s) (dsT s v) := by rcases htt with h | h <;> rw [h] <;> assumption
  have hht : ht (ts s) (dsT s v) = ht (ts s) v := by rcases htt with h | h <;> rw [h] <;> assumption
  refine ⟨fun e => ?_, hg.1.2.1, hlive.1.2.1, hlive, hht, (S.htN v hg.1).1, hlt⟩
  rw [← e] at hlive; exact absurd hg.2 (by rw [hlive.2]; simp)

theorem Shape.ds_pp (tag c j : Nat) :
    pp (ts (dsS s v tag)) c j = if c = dsY s v ∧ j = ht (ts s) v then dsT s v else pp (ts s) c j :=
  dsS_pp s v tag (S.ds_basics hg hne).2.2.2.2.2.1 c j

theorem Shape.drain_shapeT (tag : Nat) : ShapeT (ts (dsS s v tag)) cl ord := by
  obtain ⟨hvt, hv, htz, hlive, hht, hh1, hhH⟩ := S.ds_basics hg hne
  have T := dsS_sameTree (tag := tag) hvt hv htz
  have hP : (ts (dsS s v tag)).P = (ts s).P := dsS_P s v tag
  obtain ⟨hy, hanc, hL, hR, -⟩ := S.pick hg hne
  have hcl : cl.Nodup := S.ord0 ▸ S.ordNodup 0
  obtain ⟨hycl, hypp, -, -, -⟩ := S.rng_ghost hg hy
  have hpp := S.ds_pp hg hne tag
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, hinf⟩ := S.ghost v hg
  have h1v := before_of_infix2 (infix3_left hinf)
  have hv2 := before_of_infix2 (infix3_right hinf)
  have hon := S.ordNodup (ht (ts s) v)
  have htmem : dsT s v ∈ ord (ht (ts s) v) := by
    rw [← hht]; exact (S.ordMem _ (by omega) (by omega) _).mpr ⟨hlive.1, rfl⟩
  have htt : dsT s v = (nd (ts s) v).t1 ∨ dsT s v = (nd (ts s) v).t2 := by
    by_cases h : goesLeft s v
    · exact Or.inl (hL h).2
    · exact Or.inr (hR h).2
  have inR : ∀ d, d ∈ cl → pp (ts s) d (ht (ts s) v) = v → d ∈ rng (ts s) cl v := fun d hd h => by
    simp only [rng, List.mem_filter, decide_eq_true_eq]; exact ⟨hd, h⟩
  refine ⟨by rw [hP]; exact S.H3, S.ord0, S.ordNodup, fun h h1 h2 u => ?_, fun u hu => ?_,
    ?_, fun c hc j hj => ?_, fun c hc j hj1 hj => ?_, fun j hj c d hcd => ?_, fun X hX => ?_,
    fun X hX => ?_⟩
  · rw [hP] at h2; rw [T.isN, T.ht]; exact S.ordMem h h1 h2 u
  · rw [T.isN] at hu; rw [T.ht, hP]; exact S.htN u hu
  · rw [hP, T.liveN, T.livePar]; exact S.root
  · rw [hP] at hj; rw [hpp]
    split_ifs with h
    · rw [h.2]; exact htmem
    · exact S.pathEnt c hc j hj
  · rw [hP] at hj; rw [T.order, hpp, hpp]
    by_cases hcy : c = dsY s v
    · subst hcy
      by_cases hjh : j = ht (ts s) v
      · subst hjh
        rw [if_pos ⟨rfl, rfl⟩, if_neg (by omega)]
        have := S.Sr _ hycl _ hj1 hj (by rw [hypp]; exact hg)
        rwa [hanc] at this
      · rw [if_neg (fun h => hjh h.2)]
        by_cases hjh1 : j - 1 = ht (ts s) v
        · rw [if_pos ⟨rfl, hjh1⟩]
          have hw := S.W3 _ hycl j hj1 hj
          rw [hjh1, hypp] at hw
          have hX : pp (ts s) (dsY s v) j ∈ tabs (ts s) (ht (ts s) v) v :=
            (S.tabsIff _ v _ ((S.ordMem _ hh1 (by omega) v).mpr ⟨hg.1, rfl⟩)).mpr
              ⟨(S.isN_pp hycl hj1 hj).1, by rw [(S.isN_pp hycl hj1 hj).2]; omega, hw⟩
          have hw1 := (S.W1 v hg _ hX).subset
          rcases htt with e | e <;> rw [e] <;> exact hw1 (by simp)
        · rw [if_neg (fun h => hjh1 h.2)]; exact S.W3 _ hycl j hj1 hj
    · rw [if_neg (fun h => hcy h.1), if_neg (fun h => hcy h.1)]; exact S.W3 c hc j hj1 hj
  · rw [hP] at hj
    rw [hpp, hpp]
    have hc := hcd.mem_left
    have hd := hcd.mem_right
    have hne' : c ≠ d := hcd.ne hcl
    by_cases hjh : j = ht (ts s) v
    · subst hjh
      by_cases hcy : c = dsY s v
      · subst hcy
        rw [if_pos ⟨rfl, rfl⟩, if_neg (fun h => hne' h.1.symm)]
        rcases S.O2 _ hj _ _ hcd with h | h <;> rw [hypp] at h
        · by_cases hgo : goesLeft s v
          · right; rw [(hL hgo).2, ← h]; exact h1v
          · exfalso
            have hdr := inR d hd h.symm
            have := before_getLastD hdr (by rw [← (hR hgo).1]; exact Ne.symm hne')
            rw [← (hR hgo).1] at this
            exact (this.mono (S.rng_sub v)).asymm hcl hcd
        · by_cases hgo : goesLeft s v
          · right; rw [(hL hgo).2]; exact h1v.trans h hon
          · rw [(hR hgo).2]
            rcases before_succ hon (infix3_right hinf) h with e | e
            · left; exact e.symm
            · right; exact e
      · by_cases hdy : d = dsY s v
        · subst hdy
          rw [if_neg (fun h => hcy h.1), if_pos ⟨rfl, rfl⟩]
          rcases S.O2 _ hj _ _ hcd with h | h <;> rw [hypp] at h
          · by_cases hgo : goesLeft s v
            · exfalso
              have hcr := inR c hc h
              have := before_headD hcr (by rw [← (hL hgo).1]; exact hne')
              rw [← (hL hgo).1] at this
              exact (this.mono (S.rng_sub v)).asymm hcl hcd
            · right; rw [h, (hR hgo).2]; exact hv2
          · by_cases hgo : goesLeft s v
            · rw [(hL hgo).2]
              rcases before_pred hon (infix3_left hinf) h with e | e
              · left; exact e
              · right; exact e
            · right; rw [(hR hgo).2]; exact h.trans hv2 hon
        · rw [if_neg (fun h => hcy h.1), if_neg (fun h => hdy h.1)]; exact S.O2 _ hj c d hcd
    · rw [if_neg (fun h => hjh h.2), if_neg (fun h => hjh h.2)]; exact S.O2 j hj c d hcd
  · rw [T.isN] at hX; rw [T.order, T.ht]; exact S.O1 X hX
  · rw [T.isN] at hX; rw [T.labs, hP]; exact S.labsOk X hX

theorem Shape.ds_digit (tag c j : Nat) (hj : j ≠ ht (ts s) v) (hj1 : j ≠ ht (ts s) v + 1 ∨ c ≠ dsY s v) :
    digit (ts (dsS s v tag)) c j = digit (ts s) c j := by
  obtain ⟨hvt, hv, htz, -⟩ := S.ds_basics hg hne
  have T := dsS_sameTree (tag := tag) hvt hv htz
  have hpp := S.ds_pp hg hne tag
  unfold digit
  rw [T.lab?, hpp, hpp, if_neg (fun h => hj h.2)]
  by_cases hc : c = dsY s v
  · rw [if_neg (fun h => by rcases hj1 with h' | h' <;> [exact h' (by omega); exact h' h.1])]
  · rw [if_neg (fun h => hc h.1)]

theorem Shape.ds_tagF_other (tag c : Nat) (hc : c ≠ dsY s v) :
    tagF (ts (dsS s v tag)) c = tagF (ts s) c := by
  unfold tagF
  rw [show (ts (dsS s v tag)).P = (ts s).P from dsS_P s v tag]
  apply tagUp_congr (by rw [show (ts (dsS s v tag)).P = (ts s).P from dsS_P s v tag])
  intro i _ _
  obtain ⟨hvt, hv, htz, -⟩ := S.ds_basics hg hne
  have T := dsS_sameTree (tag := tag) hvt hv htz
  have hpp := S.ds_pp hg hne tag
  unfold digit
  rw [T.lab?, hpp, hpp, if_neg (fun h => hc h.1), if_neg (fun h => hc h.1)]

/-- The table entries a sweep step reads. -/
theorem Shape.ds_mem :
    let y := dsY s v
    let h := ht (ts s) v
    dsT s v ∈ order (ts s) (pp (ts s) y (h + 1)) ∧ pp (ts s) y (h - 1) ∈ order (ts s) (dsT s v) ∧
      v ∈ order (ts s) (pp (ts s) y (h + 1)) ∧ pp (ts s) y (h - 1) ∈ order (ts s) v := by
  intro y h
  obtain ⟨hvt, hv, htz, hlive, hht, hh1, hhH⟩ := S.ds_basics hg hne
  obtain ⟨hy, hanc, hL, hR, -⟩ := S.pick hg hne
  obtain ⟨hycl, hypp, -, -, -⟩ := S.rng_ghost hg hy
  have hw := S.W3 _ hycl (h + 1) (by omega) (by omega)
  simp only [Nat.add_sub_cancel] at hw
  rw [hypp] at hw
  have hw0 := S.W3 _ hycl h hh1 (by omega)
  rw [hypp] at hw0
  have hX : pp (ts s) y (h + 1) ∈ tabs (ts s) h v :=
    (S.tabsIff _ v _ ((S.ordMem _ hh1 (by omega) v).mpr ⟨hg.1, rfl⟩)).mpr
      ⟨(S.isN_pp hycl (by omega) (show h + 1 ≤ _ by omega)).1,
        by rw [(S.isN_pp hycl (by omega) (show h + 1 ≤ _ by omega)).2], hw⟩
  have hw1 := (S.W1 v hg _ hX).subset
  have htt : dsT s v = (nd (ts s) v).t1 ∨ dsT s v = (nd (ts s) v).t2 := by
    by_cases h' : goesLeft s v
    · exact Or.inl (hL h').2
    · exact Or.inr (hR h').2
  refine ⟨by rcases htt with e | e <;> rw [e] <;> exact hw1 (by simp), ?_, hw, hw0⟩
  have := S.Sr _ hycl h hh1 (by omega) (by rw [hypp]; exact hg)
  rwa [hanc] at this

/-- **The sweep step runs**, and the tag it writes is the tag of the new path. -/
theorem Shape.drain_run (hL : LList (cN s) (cP s) s.firstChunk cl) :
    let y := dsY s v
    let h := ht (ts s) v
    let pv := digit (ts s) y (h + 1)
    let vb := digit (ts s) y h
    let pt := ((nd (ts s) (pp (ts s) y (h + 1))).lab? (dsT s v)).getD 0
    let tb := ((nd (ts s) (dsT s v)).lab? (pp (ts s) y (h - 1))).getD 0
    (drainStep v).run s = .ok true (dsS s v (dsTag s v pt tb pv vb)) ∧
      dsTag s v pt tb pv vb = tagF (ts (dsS s v (dsTag s v pt tb pv vb))) y := by
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
  refine ⟨drainStep_move hg.1.2.2 ?_ hside ?_ (getD_of_mem m1) ?_ (by rw [hpv]; exact getD_of_mem m3)
    ?_ ?_ ?_, hnew⟩
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

end facts

end OM.Proof.Top
