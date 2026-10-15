import OM.Proof.Top.InsShape

/-!
# M5: weights, drain timing and label room after a chunk split

After the split, `y` and `z` sit below `x`'s live ancestors, so those weigh 2 more while their
stored weights lag: they are the job's pending nodes. A ghost one of whose targets is above `x`
is funded by the job.
-/

namespace OM.Proof.Top

open OM.Model OM.Proof

set_option linter.deprecated false

/-! ### The live ancestors as an up-chain -/

theorem Shape.upChain_anc {s : TS} {cl : List Nat} {ord : Nat → List Nat} (S : Shape s cl ord)
    {c : Nat} (hc : c ∈ cl) :
    ∀ n j, 1 ≤ j → j + n = s.P.H → ∀ v, v ∈ upChain s (n + 2) (anc s c j) ↔
      ∃ k, j ≤ k ∧ k ≤ s.P.H ∧ v = anc s c k
  | 0, j, hj, hn, v => by
    have hj' : j = s.P.H := by omega
    subst hj'
    have hne : anc s c s.P.H ≠ NIL := (S.anc_live hc _ hj le_rfl).1.1.1
    have hup : (nd s (anc s c s.P.H)).livePar = NIL := by rw [S.anc_root hc]; exact S.root.2.2
    simp only [upChain, if_neg hne, hup, if_true, ↓reduceIte, List.mem_singleton]
    constructor
    · intro h; exact ⟨s.P.H, le_rfl, le_rfl, h⟩
    · rintro ⟨k, h1, h2, h3⟩; rw [h3, show k = s.P.H by omega]
  | n + 1, j, hj, hn, v => by
    have hne : anc s c j ≠ NIL := (S.anc_live hc j hj (by omega)).1.1.1
    have e : upChain s (n + 1 + 2) (anc s c j) = anc s c j :: upChain s (n + 2) (anc s c (j + 1)) := by
      rw [anc_succ c j hj]; simp only [upChain, if_neg hne]
    rw [e, List.mem_cons, S.upChain_anc hc n (j + 1) (by omega) (by omega) v]
    constructor
    · rintro (h | ⟨k, h1, h2, h3⟩)
      · exact ⟨j, le_rfl, by omega, h⟩
      · exact ⟨k, by omega, h2, h3⟩
    · rintro ⟨k, h1, h2, h3⟩
      rcases Nat.eq_or_lt_of_le h1 with e | e
      · left; rw [h3, e]
      · right; exact ⟨k, by omega, h2, h3⟩

/-- A live node is on the up-chain from chunk `c`'s parent iff it is an ancestor of `c`. -/
theorem Shape.upChain_lpr {s : TS} {cl : List Nat} {ord : Nat → List Nat} (S : Shape s cl ord)
    {c : Nat} (hc : c ∈ cl) {v : Nat} (hv : liveN s v) :
    v ∈ upChain s (s.P.H + 1) (lpr s c) ↔ anc s c (ht s v) = v := by
  have h3 := S.H3
  have e : s.P.H + 1 = (s.P.H - 1) + 2 := by omega
  rw [e, show lpr s c = anc s c 1 from rfl, S.upChain_anc hc (s.P.H - 1) 1 le_rfl (by omega) v]
  obtain ⟨h1, h2⟩ := S.htN v hv.1
  constructor
  · rintro ⟨k, hk1, hk2, rfl⟩
    rw [(S.anc_live hc k hk1 hk2).2]
  · intro h; exact ⟨ht s v, h1, h2, h.symm⟩

/-! ### Sums over entries -/

/-- Raising one entry's term by at most 2 raises a sum over distinct entries by at most 2. -/
theorem foldr_bump {l : List Nat} (hl : l.Nodup) (f g : Nat → Nat) (e0 : Nat)
    (hfg : ∀ e ∈ l, e ≠ e0 → g e ≤ f e) (h0 : g e0 ≤ f e0 + 2) :
    l.foldr (fun e acc => acc + g e) 0 ≤ l.foldr (fun e acc => acc + f e) 0 + (if e0 ∈ l then 2 else 0) := by
  induction l with
  | nil => simp
  | cons a r ih =>
    have hn := List.nodup_cons.mp hl
    have ih' := ih hn.2 (fun e he hne => hfg e (by simp [he]) hne)
    simp only [List.foldr_cons, List.mem_cons]
    by_cases ha : a = e0
    · subst ha
      have : a ∉ r := hn.1
      simp only [true_or, if_true]
      rw [if_neg this] at ih'
      omega
    · have := hfg a (by simp) ha
      by_cases hr : e0 ∈ r
      · simp only [hr, or_true, if_true]; rw [if_pos hr] at ih'; omega
      · simp only [Ne.symm ha, hr, or_self, if_false, false_or]; rw [if_neg hr] at ih'; omega

/-! ### Weights after the split -/

section weights
variable {s : Core} {cl : List Nat} {ord : Nat → List Nat} {dr n0 : Nat → Nat}
  (hI : InvJ (ts s) cl ord dr n0 none)
  (hcs : ∀ c, c ∈ cl ↔ 1 ≤ c ∧ c < s.C.size) {x : Nat} (hx : x ∈ cl)
  {f1x i1 : Nat} {t : TS} (F : InsFrame s x f1x i1 t)
include hI hcs hx F

/-- Filtering the chunk list after the split, for a predicate on the chunk each one stands for. -/
theorem ins_filter_len (p : Nat → Nat → Prop) [∀ a b, Decidable (p a b)] (u : Nat) :
    ((clIns cl x s.C.size (s.C.size + 1)).filter fun c =>
        decide (p (if c = s.C.size ∨ c = s.C.size + 1 then x else c) u)).length =
      (cl.filter fun c => decide (p c u)).length + (if p x u then 2 else 0) := by
  obtain ⟨A, B, hcl, hA, hB, hcl'⟩ := ins_cl hI hcs hx
  obtain ⟨hy, hz⟩ := ins_fresh hI hcs hx
  have hxs := (hcs x).mp hx
  have hfr : ∀ c, c ∈ A ∨ c ∈ B → ¬(c = s.C.size ∨ c = s.C.size + 1) := fun c hc => by
    have : c ∈ cl := by rw [hcl]; simp only [List.mem_append, List.mem_cons]; tauto
    rintro (rfl | rfl)
    · exact hy this
    · exact hz this
  have eA : (A.filter fun c => decide (p (if c = s.C.size ∨ c = s.C.size + 1 then x else c) u)) =
      A.filter fun c => decide (p c u) :=
    List.filter_congr (fun c hc => by rw [if_neg (hfr c (Or.inl hc))])
  have eB : (B.filter fun c => decide (p (if c = s.C.size ∨ c = s.C.size + 1 then x else c) u)) =
      B.filter fun c => decide (p c u) :=
    List.filter_congr (fun c hc => by rw [if_neg (hfr c (Or.inr hc))])
  rw [hcl', hcl, List.filter_append, List.filter_append, eA]
  simp only [List.filter_cons, true_or, or_true, if_true,
    if_neg (show ¬(x = s.C.size ∨ x = s.C.size + 1) by omega)]
  rw [eB]
  by_cases hp : p x u
  · simp only [hp, decide_true, if_true, List.length_append, List.length_cons]; omega
  · simp only [hp, decide_false, Bool.false_eq_true, if_false, Nat.add_zero]

theorem ins_tw {u : Nat} (hu : 1 ≤ ht (ts s) u) :
    tw t (clIns cl x s.C.size (s.C.size + 1)) u =
      tw (ts s) cl u + (if anc (ts s) x (ht (ts s) u) = u then 2 else 0) := by
  have h := ins_filter_len hI hcs hx F (fun c u => anc (ts s) c (ht (ts s) u) = u) u
  unfold tw; rw [F.ht, ← h]
  congr 1
  apply List.filter_congr
  intro c _
  by_cases hc : c = s.C.size ∨ c = s.C.size + 1
  · rw [if_pos hc, F.anc_new c hc _ hu]
  · rw [if_neg hc]; push Not at hc; rw [F.anc_old c hc.1 hc.2]

theorem ins_rng_len {u : Nat} (hu : 1 ≤ ht (ts s) u) (hH : ht (ts s) u ≤ s.P.H) :
    (rng t (clIns cl x s.C.size (s.C.size + 1)) u).length =
      (rng (ts s) cl u).length + (if pp (ts s) x (ht (ts s) u) = u then 2 else 0) := by
  have h := ins_filter_len hI hcs hx F (fun c u => pp (ts s) c (ht (ts s) u) = u) u
  unfold rng; rw [F.ht, ← h]
  congr 1
  apply List.filter_congr
  intro c _
  by_cases hc : c = s.C.size ∨ c = s.C.size + 1
  · rw [if_pos hc, F.pp_new c hc _ hu hH]
  · rw [if_neg hc]; push Not at hc; rw [F.pp_old c hc.1 hc.2]

theorem ins_ew_live {u : Nat} (hu : liveN (ts s) u) :
    ew t (clIns cl x s.C.size (s.C.size + 1)) u =
      ew (ts s) cl u + (if anc (ts s) x (ht (ts s) u) = u then 2 else 0) := by
  have h1 := (hI.shape.htN u hu.1).1
  unfold ew; rw [F.draining, if_neg (by rw [hu.2]; simp), if_neg (by rw [hu.2]; simp)]
  exact ins_tw hI hcs hx F h1

theorem ins_ew_ghost {u : Nat} (hu : ghostN (ts s) u) :
    ew t (clIns cl x s.C.size (s.C.size + 1)) u =
      ew (ts s) cl u + (if anc (ts s) x (ht (ts s) u) = (nd (ts s) u).t1 ∨
        anc (ts s) x (ht (ts s) u) = (nd (ts s) u).t2 then 2 else 0) := by
  have S := hI.shape
  obtain ⟨g1, g2, g3, g4, -, -, -, -, -, -, -, -, g13⟩ := S.ghost u hu
  have hne : (nd (ts s) u).t1 ≠ (nd (ts s) u).t2 := by
    have hnd := (S.ordNodup (ht (ts s) u)).sublist g13.sublist
    simp at hnd; exact hnd.1.2
  unfold ew; rw [F.draining, if_pos hu.2, if_pos hu.2, F.t1, F.t2]
  have e1 := ins_tw hI hcs hx F (u := (nd (ts s) u).t1) (by rw [g3]; exact (S.htN u hu.1).1)
  have e2 := ins_tw hI hcs hx F (u := (nd (ts s) u).t2) (by rw [g4]; exact (S.htN u hu.1).1)
  rw [g3] at e1; rw [g4] at e2
  rw [e1, e2]
  by_cases h1 : anc (ts s) x (ht (ts s) u) = (nd (ts s) u).t1
  · have h2 : anc (ts s) x (ht (ts s) u) ≠ (nd (ts s) u).t2 := fun e => hne (h1.symm.trans e)
    rw [if_pos h1, if_neg h2, if_pos (Or.inl h1)]; omega
  · by_cases h2 : anc (ts s) x (ht (ts s) u) = (nd (ts s) u).t2
    · rw [if_neg h1, if_pos h2, if_pos (Or.inr h2)]; omega
    · rw [if_neg h1, if_neg h2, if_neg (by tauto)]; omega

end weights

end OM.Proof.Top
