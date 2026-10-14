import OM.Proof.Cost.LMove

/-!
# Lemma C3 at the reservation pop

Popping chunk `x` starts its split: two empty chunks `y = |C|`, `z = |C| + 1` are allocated as its
siblings, and `x` turns from quiet to splitting. The ghost state of the new chunks starts at 0, and
`s₀ x` becomes the size of `x`.
-/

namespace OM.Proof

open OM.Model

set_option linter.deprecated false

/-! ### Fields read from the groups only -/

section GsFrame

variable {s s' : Core} (h : s'.Gs = s.Gs)
include h

theorem liveG_of_Gs (g : Nat) : LiveG s' g ↔ LiveG s g := by simp only [LiveG, gA, h]

theorem GrpsC_of_Gs (c : Nat) : GrpsC s' c = GrpsC s c := by
  ext g; simp only [mem_GrpsC, LiveG, gA, gC, h]

theorem units_of_Gs (c : Nat) : units s' c = units s c :=
  units_congr fun g => by unfold UnitG; simp only [LiveG, gA, gC, gSt, h]

theorem pending_of_Gs (lg : LGh) (c : Nat) : pending s' lg c = pending s lg c := by
  unfold pending; rw [GrpsC_of_Gs h]; simp only [gSt, h]

theorem charge_of_Gs (hP : s'.P = s.P) (lg : LGh) (c : Nat) : charge s' lg c = charge s lg c := by
  unfold charge; rw [GrpsC_of_Gs h]; simp only [gSt, gLl, gRr, gSz, famT, h, hP]

end GsFrame

/-! ### The pop -/

/-- What starting the split of `x` changes for the label invariant. -/
structure ResSpec (s s' : Core) (x : Nat) : Prop where
  Gs : s'.Gs = s.Gs
  P : s'.P = s.P
  Csize : s'.C.size = s.C.size + 2
  old : ∀ c, c < s.C.size → c ≠ x →
    cSz s' c = cSz s c ∧ cLs s' c = cLs s c ∧ cSt s' c = cSt s c ∧ cSrc s' c = cSrc s c ∧
      cLl s' c = cLl s c ∧ cRr s' c = cRr s c
  xs : cSz s' x = cSz s x ∧ cLs s' x = cLs s x ∧ cSt s' x = .splitting ∧
    cLl s' x = s.C.size ∧ cRr s' x = s.C.size + 1
  new : ∀ c, c = s.C.size ∨ c = s.C.size + 1 →
    cSz s' c = 0 ∧ cLs s' c = NIL ∧ cSt s' c = .overflow ∧ cSrc s' c = x

/-- Fresh ghost counters for the chunks `y` and `z`. -/
def LGh.fresh (lg : LGh) (y z : Nat) : LGh :=
  let f := fun (h : Nat → Nat) (c : Nat) => if c = y ∨ c = z then 0 else h c
  { child := lg.child, hv := f lg.hv, cs := f lg.cs, rs := f lg.rs, ins := f lg.ins, pb := f lg.pb,
    pf := f lg.pf, arB := f lg.arB, arF := f lg.arF, e0 := lg.e0 }

/-- **Lemma C3 at the reservation pop.** -/
theorem linv_pop {s s' : Core} {A : Abs} {lg : LGh} {s₀ : Nat → Nat} {x : Nat}
    (R : ResSpec s s' x) (hC : CInv s A.elist (fun _ => 0) (fun _ => 0) s₀)
    (hL : LInv s lg s₀ (fun _ => 0) (fun _ => 0)) (hxL : LiveC s x) (hxq : cSt s x = .quiet)
    (hun : units s x ≤ unitsOf s.P (cSz s x)) :
    LInv s' (lg.fresh s.C.size (s.C.size + 1)) (Function.update s₀ x (cSz s x))
      (fun _ => 0) (fun _ => 0) := by
  have hnew : ∀ c, c = s.C.size ∨ c = s.C.size + 1 → ¬ c < s.C.size := by
    rintro c (rfl | rfl) <;> omega
  have hLv := liveG_of_Gs R.Gs
  have hg : ∀ g, s'.Gs.getX g = s.Gs.getX g := fun g => by rw [R.Gs]
  have hcg : ∀ g, LiveG s g → gC s g < s.C.size := fun g hg => (hC.gchk g hg).1.2
  have hcgx : ∀ g, LiveG s g → ¬ (gC s g = s.C.size ∨ gC s g = s.C.size + 1) := by
    intro g hg' h; exact hnew _ h (hcg g hg')
  -- an old chunk's fields
  have hold : ∀ c, c < s.C.size → (c = s.C.size ∨ c = s.C.size + 1) = False := by
    intro c hc; apply propext; constructor
    · intro h; exact hnew c h hc
    · intro h; exact h.elim
  have hLC : ∀ c, LiveC s' c ↔ LiveC s c ∨ c = s.C.size ∨ c = s.C.size + 1 := by
    intro c; simp only [LiveC, R.Csize]; constructor
    · rintro ⟨h1, h2⟩
      by_cases h3 : c < s.C.size
      · exact Or.inl ⟨h1, h3⟩
      · right; have : c = s.C.size ∨ c = s.C.size + 1 := by omega
        exact this
    · rintro (⟨h1, h2⟩ | h | h)
      · exact ⟨h1, by omega⟩
      · subst h; exact ⟨hxL.1.trans (Nat.le_of_lt hxL.2), by omega⟩
      · subst h; exact ⟨by omega, by omega⟩
  -- the family of an old splitting chunk is old and avoids `x`
  have hfamOld : ∀ x', LiveC s x' → cSt s x' = .splitting →
      x' ≠ x ∧ cLl s x' ≠ x ∧ cRr s x' ≠ x ∧ cLl s x' < s.C.size ∧ cRr s x' < s.C.size := by
    intro x' hx' hs'
    have F := hC.cfam x' hx' hs'
    refine ⟨?_, ?_, ?_, F.lLive.2, F.rLive.2⟩
    · rintro rfl; rw [hxq] at hs'; cases hs'
    · intro e; have := F.lSt; rw [e, hxq] at this; cases this
    · intro e; have := F.rSt; rw [e, hxq] at this; cases this
  have hfamC : ∀ x', LiveC s x' → cSt s x' = .splitting → famC s' x' = famC s x' := by
    intro x' hx' hs'
    obtain ⟨h1, h2, h3, h4, h5⟩ := hfamOld x' hx' hs'
    have o1 := R.old _ h4 h2
    have o2 := R.old _ hx'.2 h1
    have o3 := R.old _ h5 h3
    unfold famC; rw [o2.2.2.2.2.1, o2.2.2.2.2.2, o1.1, o2.1, o3.1]
  have hgrE : ∀ c, c = s.C.size ∨ c = s.C.size + 1 → GrpsC s' c = ∅ := by
    intro c hc
    rw [GrpsC_of_Gs R.Gs]
    ext g; simp only [mem_GrpsC, Finset.notMem_empty, iff_false, not_and]
    intro hg' e; exact hcgx g hg' (e ▸ hc)
  have hfr : ∀ (h : Nat → Nat) c, c < s.C.size →
      (if c = s.C.size ∨ c = s.C.size + 1 then 0 else h c) = h c := by
    intro h c hc; rw [if_neg (hnew c · hc)]
  have hfr0 : ∀ (h : Nat → Nat) c, c = s.C.size ∨ c = s.C.size + 1 →
      (if c = s.C.size ∨ c = s.C.size + 1 then 0 else h c) = 0 := by
    intro h c hc; rw [if_pos hc]
  have eL : ∀ g, gL s' g = gL s g := fun g => by simp only [gL, hg]
  have eN : ∀ g, gN s' g = gN s g := fun g => by simp only [gN, hg]
  have eC : ∀ g, gC s' g = gC s g := fun g => by simp only [gC, hg]
  have eSt : ∀ g, gSt s' g = gSt s g := fun g => by simp only [gSt, hg]
  have eLl : ∀ g, gLl s' g = gLl s g := fun g => by simp only [gLl, hg]
  have eRr : ∀ g, gRr s' g = gRr s g := fun g => by simp only [gRr, hg]
  have hfx : famC s' x = cSz s x := by
    unfold famC
    rw [R.xs.2.2.2.1, R.xs.2.2.2.2, (R.new _ (Or.inl rfl)).1, R.xs.1, (R.new _ (Or.inr rfl)).1]
    omega
  have hstN : ∀ c, c = s.C.size ∨ c = s.C.size + 1 → cSt s' c = .overflow := fun c h => (R.new c h).2.2.1
  refine
    { gaps := ?_, range := ?_, hv := ?_, pb := ?_, pf := ?_, roots := ?_, claim2 := ?_,
      insQ := ?_, insO := ?_, insS := ?_, arrS := ?_, arrN := ?_, e0 := ?_, famChild := ?_ }
  · intro g hg' hl
    rw [hLv] at hg'
    have hgc := hcg g hg'
    show gL s' g + s'.P.D_g / 2 ^ (if gC s' g = s.C.size ∨ gC s' g = s.C.size + 1 then 0
      else lg.hv (gC s' g)) ≤ gL s' (gN s' g)
    rw [eC] at hl ⊢
    rw [eL, eL, eN, R.P, hfr _ _ hgc]
    have hls : cLs s' (gC s g) = cLs s (gC s g) := by
      by_cases hx : gC s g = x
      · rw [hx]; exact R.xs.2.1
      · exact (R.old _ hgc hx).2.1
    rw [hls] at hl
    exact hL.gaps g hg' hl
  · intro g hg'
    rw [hLv] at hg'
    have hgc := hcg g hg'
    show cG s'.P ≤ gL s' g + (if gC s' g = s.C.size ∨ gC s' g = s.C.size + 1 then 0
      else lg.pf (gC s' g)) * s'.P.D_g ∧ gL s' g ≤ cG s'.P +
        (if gC s' g = s.C.size ∨ gC s' g = s.C.size + 1 then 0 else lg.pb (gC s' g)) * s'.P.D_g
    rw [eL, eC, R.P, hfr _ _ hgc, hfr _ _ hgc]
    exact hL.range g hg'
  · intro c
    show (if c = s.C.size ∨ c = s.C.size + 1 then 0 else lg.hv c) ≤
      2 * ((if c = s.C.size ∨ c = s.C.size + 1 then 0 else lg.cs c) +
        (if c = s.C.size ∨ c = s.C.size + 1 then 0 else lg.rs c))
    by_cases hc : c = s.C.size ∨ c = s.C.size + 1
    · simp only [if_pos hc]; omega
    · simp only [if_neg hc]; exact hL.hv c
  · intro c
    show (if c = s.C.size ∨ c = s.C.size + 1 then 0 else lg.pb c) ≤
      (if c = s.C.size ∨ c = s.C.size + 1 then 0 else lg.arB c) +
        (if c = s.C.size ∨ c = s.C.size + 1 then 0 else lg.rs c) +
        (if c = s.C.size ∨ c = s.C.size + 1 then 0 else lg.cs c)
    by_cases hc : c = s.C.size ∨ c = s.C.size + 1
    · simp only [if_pos hc]; omega
    · simp only [if_neg hc]; exact hL.pb c
  · intro c
    show (if c = s.C.size ∨ c = s.C.size + 1 then 0 else lg.pf c) ≤
      (if c = s.C.size ∨ c = s.C.size + 1 then 0 else lg.arF c) +
        (if c = s.C.size ∨ c = s.C.size + 1 then 0 else lg.rs c) +
        (if c = s.C.size ∨ c = s.C.size + 1 then 0 else lg.cs c)
    by_cases hc : c = s.C.size ∨ c = s.C.size + 1
    · simp only [if_pos hc]; omega
    · simp only [if_neg hc]; exact hL.pf c
  · intro d hd
    show (if d = s.C.size ∨ d = s.C.size + 1 then 0 else lg.rs d) + pending s' lg d ≤
      (if d = s.C.size ∨ d = s.C.size + 1 then 0 else lg.arB d) +
        (if d = s.C.size ∨ d = s.C.size + 1 then 0 else lg.arF d) + 1
    rcases (hLC d).mp hd with hd | hdn
    · rw [hfr _ _ hd.2, hfr _ _ hd.2, hfr _ _ hd.2, pending_of_Gs R.Gs]; exact hL.roots d hd
    · rw [hfr0 _ _ hdn, hfr0 _ _ hdn, hfr0 _ _ hdn]
      unfold pending; rw [hgrE d hdn]; simp
  · intro d hd
    show (if d = s.C.size ∨ d = s.C.size + 1 then 0 else lg.cs d) * gmin s'.P + charge s' lg d ≤
      (if d = s.C.size ∨ d = s.C.size + 1 then 0 else lg.ins d)
    rcases (hLC d).mp hd with hd | hdn
    · rw [hfr _ _ hd.2, hfr _ _ hd.2, charge_of_Gs R.Gs R.P, R.P]; exact hL.claim2 d hd
    · rw [hfr0 _ _ hdn, hfr0 _ _ hdn, charge_eq, hgrE d hdn]; simp
  · intro d hd hds
    show (if d = s.C.size ∨ d = s.C.size + 1 then 0 else lg.ins d) + lg.e0 d ≤
      cSz s' d + kC s'.P s'.P.T
    rcases (hLC d).mp hd with hd | hdn
    · have hdx : d ≠ x := by intro e; rw [e, R.xs.2.2.1] at hds; cases hds
      have o := R.old d hd.2 hdx
      rw [o.2.2.1] at hds
      rw [hfr _ _ hd.2, o.1, R.P]; exact hL.insQ d hd hds
    · rw [hstN d hdn] at hds; cases hds
  · intro d hd hds
    show (if d = s.C.size ∨ d = s.C.size + 1 then 0 else lg.ins d) +
      Function.update s₀ x (cSz s x) (cSrc s' d) ≤ famC s' (cSrc s' d)
    rcases (hLC d).mp hd with hd | hdn
    · have hdx : d ≠ x := by intro e; rw [e, R.xs.2.2.1] at hds; cases hds
      have o := R.old d hd.2 hdx
      rw [o.2.2.1] at hds
      obtain ⟨p1, p2, -⟩ := hC.covf d hd hds
      have hsx := (hfamOld _ p1 p2).1
      rw [hfr _ _ hd.2, o.2.2.2.1, Function.update_of_ne hsx, hfamC _ p1 p2]
      exact hL.insO d hd hds
    · rw [hfr0 _ _ hdn, (R.new d hdn).2.2.2, Function.update_self, hfx]; omega
  · intro d hd hds
    show (if d = s.C.size ∨ d = s.C.size + 1 then 0 else lg.ins d) ≤ famC s' d + kC s'.P s'.P.T
    rcases (hLC d).mp hd with hd | hdn
    · rw [hfr _ _ hd.2, R.P]
      by_cases hdx : d = x
      · rw [hdx, hfx]; have := hL.insQ x hxL hxq; omega
      · have o := R.old d hd.2 hdx
        rw [o.2.2.1] at hds
        rw [hfamC d hd hds]; exact hL.insS d hd hds
    · rw [hstN d hdn] at hds; cases hds
  · intro x' hx' hxs'
    rcases (hLC x').mp hx' with hx' | hdn
    · by_cases hdx : x' = x
      · subst hdx
        show (if cLl s' x' = s.C.size ∨ cLl s' x' = s.C.size + 1 then 0 else lg.arB (cLl s' x')) +
            (if cLl s' x' = s.C.size ∨ cLl s' x' = s.C.size + 1 then 0 else lg.arF (cLl s' x')) +
            (if cRr s' x' = s.C.size ∨ cRr s' x' = s.C.size + 1 then 0 else lg.arB (cRr s' x')) +
            (if cRr s' x' = s.C.size ∨ cRr s' x' = s.C.size + 1 then 0 else lg.arF (cRr s' x')) +
            3 * units s' x' + 3 * (0 + 0 + 0) + 3 * Function.update s₀ x' (cSz s x') x' ≤
          3 * (unitsOf s'.P (Function.update s₀ x' (cSz s x') x') + famC s' x') + 3 * 0
        rw [R.xs.2.2.2.1, R.xs.2.2.2.2, hfr0 _ _ (Or.inl rfl), hfr0 _ _ (Or.inl rfl),
          hfr0 _ _ (Or.inr rfl), hfr0 _ _ (Or.inr rfl), units_of_Gs R.Gs, Function.update_self, hfx,
          R.P]
        omega
      · have o := R.old x' hx'.2 hdx
        rw [o.2.2.1] at hxs'
        obtain ⟨-, -, -, h4, h5⟩ := hfamOld x' hx' hxs'
        have h := hL.arrS x' hx' hxs'
        show (if cLl s' x' = s.C.size ∨ cLl s' x' = s.C.size + 1 then 0 else lg.arB (cLl s' x')) +
            (if cLl s' x' = s.C.size ∨ cLl s' x' = s.C.size + 1 then 0 else lg.arF (cLl s' x')) +
            (if cRr s' x' = s.C.size ∨ cRr s' x' = s.C.size + 1 then 0 else lg.arB (cRr s' x')) +
            (if cRr s' x' = s.C.size ∨ cRr s' x' = s.C.size + 1 then 0 else lg.arF (cRr s' x')) +
            3 * units s' x' + 3 * (0 + 0 + 0) + 3 * Function.update s₀ x (cSz s x) x' ≤
          3 * (unitsOf s'.P (Function.update s₀ x (cSz s x) x') + famC s' x') + 3 * 0
        rw [o.2.2.2.2.1, o.2.2.2.2.2, hfr _ _ h4, hfr _ _ h4, hfr _ _ h5, hfr _ _ h5,
          units_of_Gs R.Gs, Function.update_of_ne hdx, hfamC x' hx' hxs', R.P]
        exact h
    · rw [hstN x' hdn] at hxs'; cases hxs'
  · intro d hd hds
    show (if d = s.C.size ∨ d = s.C.size + 1 then 0 else lg.arB d) +
      (if d = s.C.size ∨ d = s.C.size + 1 then 0 else lg.arF d) ≤ 3 * Mu s'.P
    rcases (hLC d).mp hd with hd | hdn
    · rw [hfr _ _ hd.2, hfr _ _ hd.2, R.P]
      by_cases hdx : d = x
      · rw [hdx]; exact hL.arrN x hxL (by rw [hxq]; simp)
      · have o := R.old d hd.2 hdx
        rw [o.2.2.1] at hds
        exact hL.arrN d hd hds
    · exact absurd (hstN d hdn) hds
  · intro d hd hds
    show lg.e0 d ≤ cSz s' d
    rcases (hLC d).mp hd with hd | hdn
    · have hdx : d ≠ x := by intro e; rw [e, R.xs.2.2.1] at hds; cases hds
      have o := R.old d hd.2 hdx
      rw [o.2.2.1] at hds
      rw [o.1]; exact hL.e0 d hd hds
    · rw [hstN d hdn] at hds; cases hds
  · intro p hp hps
    rw [hLv] at hp; rw [eSt] at hps
    show lg.child (gLl s' p) = lg.child (gRr s' p)
    rw [eLl, eRr]; exact hL.famChild p hp hps

end OM.Proof
