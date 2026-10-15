import OM.Proof.Top.StartShape

/-!
# M5: weights, drain timing and label room after a drain starts
-/

namespace OM.Proof.Top

open OM.Model OM.Proof

set_option linter.deprecated false

theorem foldr_sum (l : List Nat) (f : Nat → Nat) : l.foldr (fun e acc => acc + f e) 0 = (l.map f).sum := by
  induction l with
  | nil => rfl
  | cons a t ih => simp [ih]; omega

/-- The job after the walk starts a drain at `v` (`up` its live parent). -/
def drainJob (j : Job) (v up : Nat) : Job := { j with pc := .afterDrain v up }

namespace SDCtx

variable {s : Core} {cl : List Nat} {ord : Nat → List Nat} {dr n0 : Nat → Nat} {j : Job} {v : Nat}
  {side : List (Nat × Side)} (C : SDCtx s cl ord dr n0 j v side)
include C

local notation "S'" => ts (sdS (wiC s v) v side)
local notation "O'" => ordSD ord (Top.ht (ts s) v) v s.nodes.size

/-- **The weight of a new node**: its part's children's, stored as its true weight. -/
theorem tw_new (w : Nat) (hw : w = s.nodes.size ∨ w = s.nodes.size + 1) :
    tw S' cl w = (nd S' w).weight ∧
      tw S' cl w = if Top.ht (ts s) v = 1 then (nd S' w).children.length
        else ((nd S' w).children.map (tw (ts s) cl)).sum := by
  have SH := C.shape
  have hvlt := C.H.hv
  have hwl : Top.liveN S' w := (C.liveN w).mpr (Or.inr hw)
  obtain ⟨-, -, hkk⟩ := C.S.kids v C.vl
  have hch : ∀ e ∈ (nd S' w).children, e ∈ (nd (ts s) v).children := by
    intro e he
    rw [C.children, if_neg (by omega)] at he
    rcases hw with rfl | rfl
    · rw [if_pos rfl] at he; exact List.mem_of_mem_take he
    · rw [if_neg (by omega), if_pos rfl] at he; exact List.mem_of_mem_drop he
  have hwt : (nd S' w).weight = ((nd S' w).children.map (sWt (wiC s v) v)).sum := by
    rw [C.H.weight]
    rcases hw with rfl | rfl
    · rw [if_pos rfl, C.children, if_neg (by omega), if_pos rfl, C.ch.1]
    · rw [if_neg (by omega), if_pos rfl, C.children, if_neg (by omega), if_neg (by omega), if_pos rfl, C.ch.2]
  have hwh : Top.ht S' w = Top.ht (ts s) v := by rw [C.ht w, if_pos hw]
  by_cases h1 : Top.ht (ts s) v = 1
  · rw [if_pos h1, SH.tw_one hwl (by rw [hwh, h1]), hwt]
    have : ((nd S' w).children.map (sWt (wiC s v) v)) = List.replicate (nd S' w).children.length 1 := by
      rw [List.eq_replicate_iff]; simp only [List.length_map, true_and]
      intro x hx; obtain ⟨e, -, rfl⟩ := List.mem_map.mp hx
      unfold sWt drainWt; rw [sd_h_eq, h1]; rfl
    rw [this]; simp
  · have h2 : 2 ≤ Top.ht (ts s) v := by have := C.h1; omega
    have hsum : ((nd S' w).children.map (tw S' cl)) = ((nd S' w).children.map (tw (ts s) cl)) := by
      apply List.map_congr_left; intro e he
      have hek := hch e he
      have hel := (hkk e hek).2 h2
      have hev : e ≠ v := by
        intro e'; have := ((C.S.mem_children C.vl).mp hek).1; rw [if_neg h1, e'] at this; omega
      exact C.tw_old hel.1 hev
    have hws : ((nd S' w).children.map (sWt (wiC s v) v)) = ((nd S' w).children.map (tw (ts s) cl)) := by
      apply List.map_congr_left; intro e he
      have hek := hch e he
      have hev : e ≠ v := by
        intro e'; have := ((C.S.mem_children C.vl).mp hek).1; rw [if_neg h1, e'] at this; omega
      unfold sWt drainWt
      rw [sd_h_eq, if_neg (by simp; omega), ← sd_kid_weight C.pc C.v0 C.I C.lp hek h2]
      show ((s.nodes.modify v _).getX e).weight = _
      rw [Array.getX_modify, if_neg (fun h' => hev h'.1.symm)]; rfl
    rw [if_neg h1, SH.tw_kids hwl (by rw [hwh]; exact h2), hsum, hwt, hws]
    exact ⟨rfl, rfl⟩

/-- The drained node served what its two targets now serve. -/
theorem ew_v : ew S' cl v = tw (ts s) cl v := by
  have hvlt := C.H.hv
  have SH := C.shape
  obtain ⟨hknd, -, hkk⟩ := C.S.kids v C.vl
  have hd : (nd S' v).draining = true := by rw [C.draining', if_pos rfl]
  have ht1 : (nd S' v).t1 = s.nodes.size := by rw [C.H.t1, if_pos rfl]
  have ht2 : (nd S' v).t2 = s.nodes.size + 1 := by rw [C.H.t2, if_pos rfl]
  unfold ew
  rw [if_pos hd, ht1, ht2]
  obtain ⟨-, a1⟩ := C.tw_new _ (Or.inl rfl)
  obtain ⟨-, a2⟩ := C.tw_new _ (Or.inr rfl)
  rw [a1, a2, C.children s.nodes.size, if_neg (show ¬(s.nodes.size = v) by omega), if_pos rfl,
    C.children (s.nodes.size + 1), if_neg (show ¬(s.nodes.size + 1 = v) by omega),
    if_neg (show ¬(s.nodes.size + 1 = s.nodes.size) by omega), if_pos rfl]
  by_cases h1 : Top.ht (ts s) v = 1
  · rw [if_pos h1, if_pos h1, List.length_take, List.length_drop, C.S.tw_one C.vl h1]
    have := C.k; omega
  · rw [if_neg h1, if_neg h1, C.S.tw_kids C.vl (by have := C.h1; omega), ← List.sum_append, ← List.map_append,
      List.take_append_drop]

/-- An old node serves as before. -/
theorem ew_old {X : Nat} (hX : Top.isN (ts s) X) : ew S' cl X = ew (ts s) cl X := by
  have hvlt := C.H.hv
  by_cases hXv : X = v
  · rw [hXv, C.ew_v]; unfold ew; rw [if_neg (by rw [C.vl.2]; simp)]
  · have hXn := C.nN X hX
    have hnn : ¬(X = s.nodes.size ∨ X = s.nodes.size + 1) := fun h => h.elim hXn.1 hXn.2
    unfold ew
    rw [C.draining', if_neg hXv, if_neg hnn]
    split
    · next hd =>
      obtain ⟨g1, g2, -, -, h5, h6, -⟩ := C.S.ghost X ⟨hX, hd⟩
      have ht1v : (nd (ts s) X).t1 ≠ v := fun e => by rw [e] at h5; rw [show Top.srcOf (ts s) v = NIL from C.of] at h5; exact hX.1 h5.symm
      have ht2v : (nd (ts s) X).t2 ≠ v := fun e => by rw [e] at h6; rw [show Top.srcOf (ts s) v = NIL from C.of] at h6; exact hX.1 h6.symm
      rw [C.H.t1, C.H.t2, if_neg hXv, if_neg hXv, if_neg hnn, if_neg hnn, C.tw_old g1.1 ht1v, C.tw_old g2.1 ht2v]
    · exact C.tw_old hX hXv

/-- Live nodes above `v` keep their live parents. -/
theorem livePar_high {x : Nat} (hx : Top.liveN (ts s) x) (hh : Top.ht (ts s) v + 1 ≤ Top.ht (ts s) x) :
    (nd S' x).livePar = (nd (ts s) x).livePar :=
  C.livePar_old hx.1 (fun e => by rw [e] at hh; omega) (fun h1 hk => by
    have := ((C.S.mem_children C.vl).mp hk).1; rw [if_neg h1] at this; omega)

theorem upChain_high : ∀ f x, (x = NIL ∨ (Top.liveN (ts s) x ∧ Top.ht (ts s) v + 1 ≤ Top.ht (ts s) x)) →
    upChain S' f x = upChain (ts s) f x
  | 0, _, _ => rfl
  | f + 1, x, hx => by
    simp only [upChain]
    split
    · rfl
    · next hx0 =>
      rcases hx with h | ⟨hl, hh⟩
      · exact absurd h hx0
      rw [C.livePar_high hl hh]
      congr 1
      apply upChain_high
      by_cases hH : Top.ht (ts s) x < s.P.H
      · obtain ⟨h1, h2, -⟩ := C.S.up x hl hH
        exact Or.inr ⟨h1, by omega⟩
      · left
        have hc := C.Ti.chain
        have hroot : x = s.P.H := by
          have h' : Top.ht (ts s) x ≤ s.P.H := (C.S.htN x hl.1).2
          have hm := (C.S.ordMem (ts s).P.H (by have := C.S.H3; omega) le_rfl x).mpr ⟨hl.1, by
            show Top.ht (ts s) x = s.P.H; omega⟩
          rw [C.S.root.1] at hm
          have : x = (ts s).P.H := by simpa using hm
          exact this
        rw [hroot]; exact C.S.root.2.2

/-- **The lagging nodes after the drain starts**: `v` has caught up. -/
theorem pend_mem {x : Nat} : x ∈ pend S' (some { j with pc := .afterDrain v (nd (ts s) v).livePar }) ↔
    x ∈ pend (ts s) (some j) ∧ x ≠ v := by
  obtain ⟨hl, hlh, -⟩ := C.up
  have hpold := sd_pend C.pc C.v0 C.I C.lp
  rw [hpold]
  unfold pend wStart
  simp only
  rw [C.H.P, C.upChain_high _ _ (Or.inr ⟨hl, by omega⟩)]
  have e : (ts s).P.H = s.P.H := rfl
  rw [e]
  have hvn : v ∉ upChain (ts s) (s.P.H + 1) (nd (ts s) v).livePar := by
    intro hm
    have := (C.S.upChain_mem _ _ v hl hm).2; omega
  constructor
  · intro h; exact ⟨List.mem_cons_of_mem _ h, fun e => hvn (e ▸ h)⟩
  · rintro ⟨h, hxv⟩
    rcases List.mem_cons.mp h with h | h
    · exact absurd h hxv
    · exact h


theorem y_mem : j.y ∈ cl := by
  obtain ⟨⟨A, B, hAB⟩, -⟩ := C.I.job j rfl
  rw [hAB]; simp

theorem rng_old {g : Nat} (hg : Top.isN (ts s) g) : rng S' cl g = rng (ts s) cl g := by
  have hn := C.nN g hg
  unfold rng; rw [C.ht g, if_neg (fun h => h.elim hn.1 hn.2)]; congr 1; funext c; rw [C.pp]

theorem funded_old {g : Nat} (hg : Top.ghostN (ts s) g) :
    funded S' (some (drainJob j v (nd (ts s) v).livePar)) g ↔ funded (ts s) (some j) g := by
  have hvlt := C.H.hv
  have hgv : g ≠ v := fun e => by rw [e] at hg; exact absurd hg.2 (by rw [C.vl.2]; simp)
  have hgn := C.nN g hg.1
  have hgnn : ¬(g = s.nodes.size ∨ g = s.nodes.size + 1) := fun h => h.elim hgn.1 hgn.2
  obtain ⟨g1, g2, -, -, h5, h6, -⟩ := C.S.ghost g hg
  have ht1v : (nd (ts s) g).t1 ≠ v := fun e => by rw [e] at h5; rw [show Top.srcOf (ts s) v = NIL from C.of] at h5; exact hg.1.1 h5.symm
  have ht2v : (nd (ts s) g).t2 ≠ v := fun e => by rw [e] at h6; rw [show Top.srcOf (ts s) v = NIL from C.of] at h6; exact hg.1.1 h6.symm
  have h1n := C.nN _ g1.1
  have h2n := C.nN _ g2.1
  show Top.anc S' j.y (Top.ht S' g) = (nd S' g).t1 ∨ Top.anc S' j.y (Top.ht S' g) = (nd S' g).t2 ↔
    Top.anc (ts s) j.y (Top.ht (ts s) g) = (nd (ts s) g).t1 ∨ Top.anc (ts s) j.y (Top.ht (ts s) g) = (nd (ts s) g).t2
  rw [C.ht g, if_neg hgnn, C.H.t1, C.H.t2, if_neg hgv, if_neg hgv, if_neg hgnn, if_neg hgnn,
    C.anc C.y_mem _ (C.S.htN g hg.1).2]
  split
  · next hb =>
    rw [hb.1, hb.2]
    constructor
    · rintro (h | h) <;> split at h <;> omega
    · rintro (h | h)
      · exact absurd h.symm ht1v
      · exact absurd h.symm ht2v
  · rfl

theorem slack_old {g : Nat} (hg : Top.ghostN (ts s) g) : slack S' (some (drainJob j v (nd (ts s) v).livePar)) g = slack (ts s) (some j) g := by
  have hvlt := C.H.hv
  have hgn := C.nN g hg.1
  have hgnn : ¬(g = s.nodes.size ∨ g = s.nodes.size + 1) := fun h => h.elim hgn.1 hgn.2
  have hf := C.funded_old hg
  have hcur : curH (ts s) j = Top.ht (ts s) v := by unfold curH; rw [C.pc]; simp [C.v0]
  have hcur' : curH S' (drainJob j v (nd (ts s) v).livePar) = Top.ht (ts s) v + 1 := by
    show Top.ht S' v + 1 = _
    have hvn := C.nN v C.vl.1
    rw [C.ht v, if_neg (fun h => h.elim hvn.1 hvn.2)]
  -- funded ghosts are not at `v`'s height
  have hfh : funded (ts s) (some j) g → Top.ht (ts s) g ≠ Top.ht (ts s) v := by
    intro hfd e
    obtain ⟨-, -, -, -, h5, h6, -⟩ := C.S.ghost g hg
    have hvy := C.vy
    change Top.anc (ts s) j.y (Top.ht (ts s) g) = (nd (ts s) g).t1 ∨
      Top.anc (ts s) j.y (Top.ht (ts s) g) = (nd (ts s) g).t2 at hfd
    rw [e, ← hvy] at hfd
    rcases hfd with h | h
    · rw [← h, show Top.srcOf (ts s) v = NIL from C.of] at h5; exact hg.1.1 h5.symm
    · rw [← h, show Top.srcOf (ts s) v = NIL from C.of] at h6; exact hg.1.1 h6.symm
  have hpc := C.pc
  unfold slack
  simp only
  by_cases hfd : funded (ts s) (some j) g
  · have hfd' : funded S' (some (drainJob j v (nd (ts s) v).livePar)) g := hf.mpr hfd
    have hne := hfh hfd
    rw [if_pos (show Top.anc S' (drainJob j v (nd (ts s) v).livePar).y (Top.ht S' g) = (nd S' g).t1 ∨
        Top.anc S' (drainJob j v (nd (ts s) v).livePar).y (Top.ht S' g) = (nd S' g).t2 from hfd'),
      if_pos (show Top.anc (ts s) j.y (Top.ht (ts s) g) = (nd (ts s) g).t1 ∨
        Top.anc (ts s) j.y (Top.ht (ts s) g) = (nd (ts s) g).t2 from hfd)]
    rw [hcur, hcur', C.H.P, C.ht g, if_neg hgnn]
    by_cases hle : Top.ht (ts s) v ≤ Top.ht (ts s) g
    · rw [if_pos (by omega), if_pos hle]; rfl
    · rw [if_neg (by omega), if_neg hle, hpc]; rfl
  · rw [if_neg (show ¬(Top.anc S' (drainJob j v (nd (ts s) v).livePar).y (Top.ht S' g) = (nd S' g).t1 ∨
        Top.anc S' (drainJob j v (nd (ts s) v).livePar).y (Top.ht S' g) = (nd S' g).t2) from fun h => hfd (hf.mp h)),
      if_neg (show ¬(Top.anc (ts s) j.y (Top.ht (ts s) g) = (nd (ts s) g).t1 ∨
        Top.anc (ts s) j.y (Top.ht (ts s) g) = (nd (ts s) g).t2) from hfd)]

theorem slack_v : slack S' (some (drainJob j v (nd (ts s) v).livePar)) v = 0 := by
  have hvlt := C.H.hv
  have hvn := C.nN v C.vl.1
  have hcur' : curH S' (drainJob j v (nd (ts s) v).livePar) = Top.ht (ts s) v + 1 := by
    show Top.ht S' v + 1 = _
    rw [C.ht v, if_neg (fun h => h.elim hvn.1 hvn.2)]
  unfold slack
  simp only
  rw [hcur', C.ht v, if_neg (show ¬(v = s.nodes.size ∨ v = s.nodes.size + 1) from fun h => h.elim hvn.1 hvn.2)]
  split
  · rw [if_neg (by omega)]; rfl
  · rfl

/-- **The new nodes weigh between `λ_h` and `τ_h`** (Lemma T0). -/
theorem tw_new_range (w : Nat) (hw : w = s.nodes.size ∨ w = s.nodes.size + 1) :
    lamd s.P (Top.ht (ts s) v) ≤ tw S' cl w ∧ tw S' cl w ≤ taud s.P (Top.ht (ts s) v) := by
  have hvlt := C.H.hv
  obtain ⟨-, htw⟩ := C.tw_new w hw
  rw [htw]
  have hc : (nd S' w).children = if w = s.nodes.size then (nd (ts s) v).children.take (sK (wiC s v) v)
      else (nd (ts s) v).children.drop (sK (wiC s v) v) := by
    rcases hw with rfl | rfl
    · rw [C.children, if_neg (show ¬(s.nodes.size = v) by omega), if_pos rfl, if_pos rfl]
    · rw [C.children, if_neg (show ¬(s.nodes.size + 1 = v) by omega),
        if_neg (show ¬(s.nodes.size + 1 = s.nodes.size) by omega), if_pos rfl,
        if_neg (show ¬(s.nodes.size + 1 = s.nodes.size) by omega)]
  rw [hc]
  by_cases h1 : Top.ht (ts s) v = 1
  · obtain ⟨-, -, -, a1, a2, a3, a4⟩ := sd_cut1 C.pc C.v0 C.I C.lp h1 C.of C.W
    rw [if_pos h1]; rw [h1]
    split
    · exact ⟨a1, a2⟩
    · exact ⟨a3, a4⟩
  · obtain ⟨-, -, -, -, a1, a2, a3, a4⟩ := sd_cut2 C.pc C.v0 C.I C.lp C.TP (by have := C.h1; omega) C.of C.W
    rw [if_neg h1]
    split
    · exact ⟨a1, a2⟩
    · exact ⟨a3, a4⟩

theorem pend_new {w : Nat} (hw : w = s.nodes.size ∨ w = s.nodes.size + 1) :
    w ∉ pend S' (some (drainJob j v (nd (ts s) v).livePar)) := by
  intro h
  rw [show drainJob j v (nd (ts s) v).livePar = { j with pc := .afterDrain v (nd (ts s) v).livePar } from rfl,
    C.pend_mem] at h
  obtain ⟨hl, -, -⟩ := C.up
  have hp := sd_pend C.pc C.v0 C.I C.lp
  rw [hp] at h
  rcases List.mem_cons.mp h.1 with e | e
  · exact h.2 e
  · have := (C.S.upChain_mem _ _ w hl e).1
    have h' : w < s.nodes.size := this.1.2.1
    omega

theorem rng_v_le : (rng (ts s) cl v).length ≤ tw (ts s) cl v := by
  unfold rng tw
  have e : cl.filter (fun c => decide (Top.pp (ts s) c (Top.ht (ts s) v) = v)) =
      (cl.filter (fun c => decide (Top.anc (ts s) c (Top.ht (ts s) v) = v))).filter
        (fun c => decide (Top.pp (ts s) c (Top.ht (ts s) v) = v)) := by
    rw [List.filter_filter]
    apply List.filter_congr
    intro c hc
    by_cases hp : Top.pp (ts s) c (Top.ht (ts s) v) = v
    · have : Top.anc (ts s) c (Top.ht (ts s) v) = v := by
        rcases C.S.P c hc _ C.h1 (by have := C.hHt; omega) with h | ⟨hg, -⟩
        · rw [← h, hp]
        · rw [hp] at hg; exact absurd hg.2 (by rw [C.vl.2]; simp)
      simp [hp, this]
    · simp [hp]
  rw [e]
  exact (List.filter_sublist).length_le

/-- **The drain timing after a drain starts.** -/
theorem time : Timing S' cl (some (drainJob j v (nd (ts s) v).livePar)) := by
  have Ti := C.Ti
  have hvlt := C.H.hv
  have hNH := C.NH
  have hP' := C.H.P
  have hpm : ∀ x, x ∈ pend S' (some (drainJob j v (nd (ts s) v).livePar)) ↔ x ∈ pend (ts s) (some j) ∧ x ≠ v :=
    fun x => C.pend_mem
  have hwv : (nd (ts s) v).weight ≤ Wd s.P (Top.ht (ts s) v) := Ti.wA v C.vl C.lp C.of
  have htv := sd_tw C.pc C.v0 C.I C.lp
  have hW := C.W
  refine ⟨fun u hu => ?_, fun u hu hp hs => ?_, fun g hg => ?_, fun g hg => ?_, fun g hg => ?_,
    fun g hg => ?_, fun u hu hH => ?_, fun t ht hs => ?_, fun u hu hH => ?_, fun u hu => ?_⟩
  · -- wts
    rw [C.liveN] at hu
    rcases hu with ⟨hul, huv⟩ | hw | hw
    · have hun := C.nN u hul.1
      rw [C.H.weight, if_neg hun.1, if_neg hun.2, if_neg huv, C.tw_old hul.1 huv, ← Ti.wts u hul]
      by_cases hp : u ∈ pend (ts s) (some j)
      · rw [if_pos ((hpm u).mpr ⟨hp, huv⟩), if_pos hp]
      · rw [if_neg (fun h => hp ((hpm u).mp h).1), if_neg hp]
    all_goals
      rw [if_neg (C.pend_new (by omega)), Nat.add_zero]
      exact (C.tw_new _ (by omega)).1.symm
  · -- wA
    rw [C.liveN] at hu
    rw [C.srcOf] at hs
    rcases hu with ⟨hul, huv⟩ | hw | hw
    · have hun := C.nN u hul.1
      have hnn : ¬(u = s.nodes.size ∨ u = s.nodes.size + 1) := fun h => h.elim hun.1 hun.2
      rw [if_neg hnn] at hs
      rw [C.H.weight, if_neg hun.1, if_neg hun.2, if_neg huv, C.ht u, if_neg hnn, hP']
      apply Ti.wA u hul _ hs
      by_cases hk : Top.ht (ts s) v ≠ 1 ∧ u ∈ (nd (ts s) v).children
      · have := ((C.S.mem_children C.vl).mp hk.2).2
        rw [par_live (Or.inr hul), if_neg (by have := C.h1; omega)] at this
        rw [this]; exact C.v0
      · rwa [C.livePar_old hul.1 huv (fun h1 h => hk ⟨h1, h⟩)] at hp
    all_goals rw [if_pos (by omega)] at hs; exact absurd hs C.v0
  · -- wB
    rw [C.ghostN] at hg
    rcases hg with hg | hgv
    · have hgv : g ≠ v := fun e => by rw [e] at hg; exact absurd hg.2 (by rw [C.vl.2]; simp)
      have hgn := C.nN g hg.1
      rw [C.H.weight, if_neg hgn.1, if_neg hgn.2, if_neg hgv, C.ht g, if_neg (fun h => h.elim hgn.1 hgn.2), hP']
      exact Ti.wB g hg
    · rw [hgv, C.H.weight, if_neg (by omega), if_neg (by omega), if_pos rfl, C.ht v,
        if_neg (show ¬(v = s.nodes.size ∨ v = s.nodes.size + 1) by omega), hP']
      constructor <;> omega
  · -- wF
    rw [C.ghostN] at hg
    rcases hg with hg | hgv
    · have hgv : g ≠ v := fun e => by rw [e] at hg; exact absurd hg.2 (by rw [C.vl.2]; simp)
      have hgn := C.nN g hg.1
      rw [C.H.weight, if_neg hgn.1, if_neg hgn.2, if_neg hgv, C.ew_old hg.1]
      exact Ti.wF g hg
    · rw [hgv, C.H.weight, if_neg (by omega), if_neg (by omega), if_pos rfl, C.ew_v, htv]
      simp
  · -- wC
    rw [C.ghostN] at hg
    rcases hg with hg | hgv
    · have hgv : g ≠ v := fun e => by rw [e] at hg; exact absurd hg.2 (by rw [C.vl.2]; simp)
      have hgn := C.nN g hg.1
      have hw : (nd S' g).weight = (nd (ts s) g).weight := by
        rw [C.H.weight, if_neg hgn.1, if_neg hgn.2, if_neg hgv]
      have hf : fundOf S' cl g = fundOf (ts s) cl g := by unfold fundOf; rw [C.ew_old hg.1, hw]
      rw [C.rng_old hg.1, hf, hw, C.slack_old hg, hP']
      exact Ti.wC g hg
    · rw [hgv]
      have hw : (nd S' v).weight = (nd (ts s) v).weight + 2 := by
        rw [C.H.weight, if_neg (by omega), if_neg (by omega), if_pos rfl]
      have hf : fundOf S' cl v = 0 := by unfold fundOf; rw [C.ew_v, hw, htv]; simp
      rw [C.rng_old C.vl.1, hf, hw, C.slack_v]
      have := C.rng_v_le
      omega
  · -- wC'
    rw [C.ghostN] at hg
    rcases hg with hg | hgv
    · have hgv : g ≠ v := fun e => by rw [e] at hg; exact absurd hg.2 (by rw [C.vl.2]; simp)
      have hgn := C.nN g hg.1
      have hw : (nd S' g).weight = (nd (ts s) g).weight := by
        rw [C.H.weight, if_neg hgn.1, if_neg hgn.2, if_neg hgv]
      have hf : fundOf S' cl g = fundOf (ts s) cl g := by unfold fundOf; rw [C.ew_old hg.1, hw]
      have := Ti.wC' g hg
      rw [hf, hw, hP']
      by_cases hfd : funded (ts s) (some j) g
      · rw [if_pos ((C.funded_old hg).mpr hfd)]; rw [if_pos hfd] at this; exact this
      · rw [if_neg (fun h => hfd ((C.funded_old hg).mp h))]; rw [if_neg hfd] at this; exact this
    · rw [hgv]
      have hw : (nd S' v).weight = (nd (ts s) v).weight + 2 := by
        rw [C.H.weight, if_neg (by omega), if_neg (by omega), if_pos rfl]
      have hf : fundOf S' cl v = 0 := by unfold fundOf; rw [C.ew_v, hw, htv]; simp
      rw [hf]; simp
  · -- wD
    rw [C.liveN] at hu
    rw [hP'] at hH
    rcases hu with ⟨hul, huv⟩ | hw | hw
    · have hun := C.nN u hul.1
      rw [C.ht u, if_neg (fun h => h.elim hun.1 hun.2), C.tw_old hul.1 huv, hP']
      exact Ti.wD u hul hH
    · subst hw; rw [C.ht _, if_pos (Or.inl rfl), hP']; exact (C.tw_new_range _ (Or.inl rfl)).1
    · subst hw; rw [C.ht _, if_pos (Or.inr rfl), hP']; exact (C.tw_new_range _ (Or.inr rfl)).1
  · -- big
    rw [C.liveN] at ht
    rw [C.srcOf] at hs
    rw [hP']
    rcases ht with ⟨htl, -⟩ | hw | hw
    · have htn := C.nN t htl.1
      rw [if_neg (fun h => h.elim htn.1 htn.2)] at hs
      exact Ti.big t htl hs
    all_goals omega
  · -- chain
    rw [C.isN] at hu
    rw [hP'] at hH
    rcases hu with hu | hw | hw
    · have hun := C.nN u hu
      rw [C.ht u, if_neg (fun h => h.elim hun.1 hun.2)]
      exact Ti.chain u hu hH
    all_goals omega
  · -- tw1
    rw [C.liveN] at hu
    rcases hu with ⟨hul, huv⟩ | hw | hw
    · rw [C.tw_old hul.1 huv]; exact Ti.tw1 u hul
    all_goals
      have := (C.tw_new_range u (by omega)).1
      have hl := C.TP.lamK (Top.ht (ts s) v) C.h1
      omega

/-- **The potential of a table that held `v`.** -/
theorem growth_tab {X : Nat} (hT : X ∈ (nd (ts s) v).inTables) :
    growth S' cl X + (if X < v then tw (ts s) cl v - taud s.P (Top.ht (ts s) v) else 0) = growth (ts s) cl X ∧
    oldLive S' X + (if v < X then 1 else 0) = oldLive (ts s) X := by
  have hvlt := C.H.hv
  obtain ⟨hX, hXh, hvX⟩ := C.inTab X hT
  have hXn := C.nN X hX
  have hXnn : ¬(X = s.nodes.size ∨ X = s.nodes.size + 1) := fun h => h.elim hXn.1 hXn.2
  have hXv : X ≠ v := fun e => by rw [e] at hXh; omega
  obtain ⟨P, Q, hPQ⟩ := List.mem_iff_append.mp hvX
  have hnd : (Top.order (ts s) X).Nodup := (C.S.ordNodup _).sublist (C.S.O1 X hX)
  have hord' : Top.order S' X = P ++ s.nodes.size :: v :: (s.nodes.size + 1) :: Q := by
    rw [C.order, if_neg hXn.1, if_neg hXn.2, if_pos hT, hPQ]
    rw [hPQ] at hnd
    have hP : v ∉ P := fun h => (List.nodup_append.mp hnd).2.2 v h v (by simp) rfl
    rw [replace1_split _ hP]; simp
  rw [hPQ] at hnd
  have hPQv : ∀ e ∈ P ++ Q, e ≠ v ∧ Top.isN (ts s) e ∧ Top.ht (ts s) e = Top.ht (ts s) v := by
    intro e he
    have hvP : v ∉ P := fun h => (List.nodup_append.mp hnd).2.2 v h v (by simp) rfl
    have hvQ : v ∉ Q := (List.nodup_cons.mp (List.nodup_append.mp hnd).2.1).1
    have hem : e ∈ Top.order (ts s) X := by
      rw [hPQ]
      rcases List.mem_append.mp he with h | h
      · exact List.mem_append_left _ h
      · exact List.mem_append_right _ (List.mem_cons_of_mem _ h)
    have hent := C.S.tabEnt X hX e hem
    rw [hXh, Nat.add_sub_cancel] at hent
    obtain ⟨hn, hh⟩ := (C.S.ordMem _ C.h1 (by have := C.hHt; omega) e).mp hent
    refine ⟨fun h => ?_, hn, hh⟩
    subst h
    simp only [List.mem_append] at he
    rcases he with h | h
    · exact hvP h
    · exact hvQ h
  have hl : ∀ e ∈ P ++ Q, (Top.liveN S' e ↔ Top.liveN (ts s) e) ∧ tw S' cl e = tw (ts s) cl e := by
    intro e he
    obtain ⟨hev, hn, -⟩ := hPQv e he
    refine ⟨?_, C.tw_old hn hev⟩
    rw [C.liveN]
    have := C.nN e hn
    constructor
    · rintro (⟨h, -⟩ | h | h)
      · exact h
      · exact absurd h this.1
      · exact absurd h this.2
    · intro h; exact Or.inl ⟨h, hev⟩
  have hNl : Top.liveN S' s.nodes.size := (C.liveN _).mpr (Or.inr (Or.inl rfl))
  have hN1l : Top.liveN S' (s.nodes.size + 1) := (C.liveN _).mpr (Or.inr (Or.inr rfl))
  have hvl' : ¬Top.liveN S' v := fun h => by
    rcases (C.liveN v).mp h with ⟨-, h⟩ | h | h
    · exact h rfl
    · omega
    · omega
  have hXN : X < s.nodes.size := hX.2.1
  have hτN := (C.tw_new_range _ (Or.inl rfl)).2
  have hτN1 := (C.tw_new_range _ (Or.inr rfl)).2
  have hht : Top.ht S' X - 1 = Top.ht (ts s) v := by rw [C.ht X, if_neg hXnn, hXh, Nat.add_sub_cancel]
  have hht' : Top.ht (ts s) X - 1 = Top.ht (ts s) v := by rw [hXh, Nat.add_sub_cancel]
  constructor
  · unfold growth
    rw [hord', hPQ, foldr_sum, foldr_sum, hht, hht', C.H.P, show (ts s).P = s.P from rfl]
    have eP : (P.filter fun e => decide (Top.liveN S' e) && decide (X < e)) =
        P.filter fun e => decide (Top.liveN (ts s) e) && decide (X < e) :=
      List.filter_congr (fun e he => by rw [show (decide (Top.liveN S' e) = decide (Top.liveN (ts s) e)) from
        decide_eq_decide.mpr (hl e (by simp [he])).1])
    have eQ : (Q.filter fun e => decide (Top.liveN S' e) && decide (X < e)) =
        Q.filter fun e => decide (Top.liveN (ts s) e) && decide (X < e) :=
      List.filter_congr (fun e he => by rw [show (decide (Top.liveN S' e) = decide (Top.liveN (ts s) e)) from
        decide_eq_decide.mpr (hl e (by simp [he])).1])
    rw [List.filter_append, List.filter_append, eP, List.filter_cons, List.filter_cons, List.filter_cons,
      List.filter_cons, eQ]
    simp only [decide_eq_true hNl, decide_eq_true hN1l, decide_eq_false hvl', decide_eq_true C.vl,
      decide_eq_true hXN, decide_eq_true (show X < s.nodes.size + 1 by omega), Bool.true_and, Bool.false_and,
      if_true, Bool.false_eq_true, if_false]
    have mP : ((P.filter fun e => decide (Top.liveN (ts s) e) && decide (X < e)).map
        fun e => tw S' cl e - taud s.P (Top.ht (ts s) v)) =
        (P.filter fun e => decide (Top.liveN (ts s) e) && decide (X < e)).map
        fun e => tw (ts s) cl e - taud s.P (Top.ht (ts s) v) :=
      List.map_congr_left (fun e he => by rw [(hl e (by simp [(List.mem_filter.mp he).1])).2])
    have mQ : ((Q.filter fun e => decide (Top.liveN (ts s) e) && decide (X < e)).map
        fun e => tw S' cl e - taud s.P (Top.ht (ts s) v)) =
        (Q.filter fun e => decide (Top.liveN (ts s) e) && decide (X < e)).map
        fun e => tw (ts s) cl e - taud s.P (Top.ht (ts s) v) :=
      List.map_congr_left (fun e he => by rw [(hl e (by simp [(List.mem_filter.mp he).1])).2])
    simp only [List.map_append, List.map_cons, List.sum_append, List.sum_cons, mP, mQ]
    by_cases hXv' : X < v
    · simp only [decide_eq_true hXv', if_true, List.map_cons, List.sum_cons]; rw [if_pos hXv']; omega
    · simp only [decide_eq_false hXv', Bool.false_eq_true, if_false]; rw [if_neg hXv']; omega
  · unfold oldLive
    rw [hord', hPQ]
    have eP : (P.filter fun e => decide (Top.liveN S' e) && decide (e < X)) =
        P.filter fun e => decide (Top.liveN (ts s) e) && decide (e < X) :=
      List.filter_congr (fun e he => by rw [show (decide (Top.liveN S' e) = decide (Top.liveN (ts s) e)) from
        decide_eq_decide.mpr (hl e (by simp [he])).1])
    have eQ : (Q.filter fun e => decide (Top.liveN S' e) && decide (e < X)) =
        Q.filter fun e => decide (Top.liveN (ts s) e) && decide (e < X) :=
      List.filter_congr (fun e he => by rw [show (decide (Top.liveN S' e) = decide (Top.liveN (ts s) e)) from
        decide_eq_decide.mpr (hl e (by simp [he])).1])
    rw [List.filter_append, List.filter_append, eP, List.filter_cons, List.filter_cons, List.filter_cons,
      List.filter_cons, eQ]
    simp only [decide_eq_false hvl', decide_eq_true C.vl, decide_eq_false (show ¬(s.nodes.size < X) by omega),
      decide_eq_false (show ¬(s.nodes.size + 1 < X) by omega), Bool.and_false, Bool.true_and, Bool.false_and,
      Bool.false_eq_true, if_false]
    by_cases hvX : v < X
    · simp only [decide_eq_true hvX, if_true, List.length_append, List.length_cons]; rw [if_pos hvX]; omega
    · simp only [decide_eq_false hvX, Bool.false_eq_true, if_false, List.length_append]; rw [if_neg hvX]; omega

theorem growth_same {X : Nat} (hX : Top.isN (ts s) X) (h2 : 2 ≤ Top.ht (ts s) X)
    (hT : X ∉ (nd (ts s) v).inTables) :
    growth S' cl X = growth (ts s) cl X ∧ oldLive S' X = oldLive (ts s) X := by
  have hvlt := C.H.hv
  have hXn := C.nN X hX
  have hXnn : ¬(X = s.nodes.size ∨ X = s.nodes.size + 1) := fun h => h.elim hXn.1 hXn.2
  obtain ⟨h1X, hHX⟩ := C.S.htN X hX
  have hord : Top.order S' X = Top.order (ts s) X := by rw [C.order, if_neg hXn.1, if_neg hXn.2, if_neg hT]
  have hent : ∀ e ∈ Top.order (ts s) X, Top.isN (ts s) e ∧ Top.ht (ts s) e = Top.ht (ts s) X - 1 :=
    fun e he => (C.S.ordMem _ (by omega) (by omega) e).mp (C.S.tabEnt X hX e he)
  have hvX : v ∉ Top.order (ts s) X := by
    intro h
    have hentv : Ent ord (Top.ht (ts s) v) v := (C.S.ordMem _ C.h1 (C.S.htN v C.vl.1).2 v).mpr ⟨C.vl.1, rfl⟩
    have hh : Top.ht (ts s) X = Top.ht (ts s) v + 1 := by have := (hent v h).2; omega
    apply hT
    have : X ∈ tabs (ts s) (Top.ht (ts s) v) v := (C.S.tabsIff _ v X hentv).mpr ⟨hX, hh, h⟩
    unfold tabs at this; rwa [if_neg (by have := C.h1; omega)] at this
  have hl : ∀ e ∈ Top.order (ts s) X, (Top.liveN S' e ↔ Top.liveN (ts s) e) ∧ tw S' cl e = tw (ts s) cl e := by
    intro e he
    have hev : e ≠ v := fun h => hvX (h ▸ he)
    have hn := (hent e he).1
    have hen := C.nN e hn
    refine ⟨?_, C.tw_old hn hev⟩
    rw [C.liveN]
    constructor
    · rintro (⟨h, -⟩ | h | h)
      · exact h
      · exact absurd h hen.1
      · exact absurd h hen.2
    · intro h; exact Or.inl ⟨h, hev⟩
  have hht : Top.ht S' X = Top.ht (ts s) X := by rw [C.ht X, if_neg hXnn]
  constructor
  · unfold growth
    rw [hord, hht, C.H.P, show (ts s).P = s.P from rfl, foldr_sum, foldr_sum]
    have ef : ((Top.order (ts s) X).filter fun e => decide (Top.liveN S' e) && decide (X < e)) =
        (Top.order (ts s) X).filter fun e => decide (Top.liveN (ts s) e) && decide (X < e) :=
      List.filter_congr (fun e he => by rw [show (decide (Top.liveN S' e) = decide (Top.liveN (ts s) e)) from
        decide_eq_decide.mpr (hl e he).1])
    rw [ef]
    have em : (((Top.order (ts s) X).filter fun e => decide (Top.liveN (ts s) e) && decide (X < e)).map
        fun e => tw S' cl e - taud s.P (Top.ht (ts s) X - 1)) =
        ((Top.order (ts s) X).filter fun e => decide (Top.liveN (ts s) e) && decide (X < e)).map
        fun e => tw (ts s) cl e - taud s.P (Top.ht (ts s) X - 1) :=
      List.map_congr_left (fun e he => by rw [(hl e (List.mem_of_mem_filter he)).2])
    rw [em]
  · unfold oldLive
    rw [hord]
    have ef : ((Top.order (ts s) X).filter fun e => decide (Top.liveN S' e) && decide (e < X)) =
        (Top.order (ts s) X).filter fun e => decide (Top.liveN (ts s) e) && decide (e < X) :=
      List.filter_congr (fun e he => by rw [show (decide (Top.liveN S' e) = decide (Top.liveN (ts s) e)) from
        decide_eq_decide.mpr (hl e he).1])
    rw [ef]

end SDCtx

end OM.Proof.Top
