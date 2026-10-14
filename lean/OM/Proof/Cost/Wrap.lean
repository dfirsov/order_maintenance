import OM.Proof.Cost.Params

/-!
# The wrapper: cost and Lemma W

Every core the wrapper runs satisfies the cost invariant whenever an operation reaches it, and
its element count stays within its capacity (Lemma W). So no core operation ever takes FALLBACK.
-/

namespace OM.Proof

open OM.Model

set_option linter.deprecated false

/-- A list linked forward from `hd`. -/
structure NList (nxt : Nat → Nat) (hd : Nat) (l : List Nat) : Prop where
  nodup : l.Nodup
  nonil : NIL ∉ l
  head : hd = l.headD NIL
  next : ∀ x ∈ l, nxt x = succOf l x

theorem LList.nlist {nxt prv : Nat → Nat} {hd : Nat} {l : List Nat} (h : LList nxt prv hd l) :
    NList nxt hd l := ⟨h.nodup, h.nonil, h.head, h.next⟩

theorem succOf_cons_ne {a x : Nat} {t : List Nat} (h : a ≠ x) : succOf (a :: t) x = succOf t x := by
  cases t with
  | nil => rfl
  | cons b t => simp only [succOf, if_neg h]

theorem succOf_cons_self {a : Nat} {t : List Nat} : succOf (a :: t) a = t.headD NIL := by
  cases t with
  | nil => rfl
  | cons b t => simp [succOf]

/-- **A forward-linked list is determined by its head.** -/
theorem NList.unique {nxt : Nat → Nat} : ∀ {hd : Nat} {l l' : List Nat},
    NList nxt hd l → NList nxt hd l' → l = l'
  | hd, [], l', h, h' => by
    cases l' with
    | nil => rfl
    | cons a t => exfalso; have := h.head; have := h'.head; simp at *; exact h'.nonil (by simp_all)
  | hd, a :: t, l', h, h' => by
    cases l' with
    | nil => exfalso; have := h.head; have := h'.head; simp at *; exact h.nonil (by simp_all)
    | cons a' t' =>
      have ha : a = a' := by have e1 := h.head; have e2 := h'.head; simp at e1 e2; rw [← e1, ← e2]
      subst ha
      have hat : a ∉ t := (List.nodup_cons.mp h.nodup).1
      have hat' : a ∉ t' := (List.nodup_cons.mp h'.nodup).1
      have tl : NList nxt (nxt a) t := ⟨(List.nodup_cons.mp h.nodup).2,
        fun hn => h.nonil (List.mem_cons_of_mem _ hn),
        by rw [h.next a (by simp), succOf_cons_self],
        fun x hx => by
          rw [h.next x (List.mem_cons_of_mem _ hx),
            succOf_cons_ne (fun (e : a = x) => hat (by rw [e]; exact hx))]⟩
      have tl' : NList nxt (nxt a) t' := ⟨(List.nodup_cons.mp h'.nodup).2,
        fun hn => h'.nonil (List.mem_cons_of_mem _ hn),
        by rw [h'.next a (by simp), succOf_cons_self],
        fun x hx => by
          rw [h'.next x (List.mem_cons_of_mem _ hx),
            succOf_cons_ne (fun (e : a = x) => hat' (by rw [e]; exact hx))]⟩
      rw [NList.unique tl tl']

theorem INV.elist_unique {s : Core} {A A' : Abs} (h : INV s A) (h' : INV s A') :
    A.elist = A'.elist := h.eList.nlist.unique h'.eList.nlist

end OM.Proof

namespace OM.Proof

open OM.Model

set_option linter.deprecated false

/-! ### The split at the cursor -/

/-- The elements before the cursor. -/
def preOf (l : List Nat) (c : Nat) : List Nat := l.takeWhile (· ≠ c)

/-- The elements from the cursor on. -/
def postOf (l : List Nat) (c : Nat) : List Nat := l.dropWhile (· ≠ c)

/-- A split whose second part starts at `c` is the split at `c`. -/
theorem split_unique {pre post : List Nat} {c : Nat} (hnd : (pre ++ post).Nodup)
    (hnil : NIL ∉ pre ++ post) (hc : c = post.headD NIL) :
    preOf (pre ++ post) c = pre ∧ postOf (pre ++ post) c = post := by
  induction pre with
  | nil =>
    cases post with
    | nil => simp [preOf, postOf]
    | cons a t => subst hc; simp [preOf, postOf]
  | cons a pre ih =>
    have hnd' : (pre ++ post).Nodup := (List.nodup_cons.mp hnd).2
    have hnil' : NIL ∉ pre ++ post := fun h => hnil (List.mem_cons_of_mem _ h)
    obtain ⟨ih1, ih2⟩ := ih hnd' hnil'
    have hac : a ≠ c := by
      intro e
      cases post with
      | nil => exact hnil (by rw [List.cons_append]; simp [e, hc])
      | cons b t =>
        simp at hc
        have : a ∈ pre ++ b :: t := by rw [e, hc]; simp
        exact (List.nodup_cons.mp hnd).1 this
    simp only [preOf, postOf, List.cons_append, List.takeWhile_cons, List.dropWhile_cons,
      decide_eq_true_eq, hac, ne_eq, not_false_eq_true, if_true] at ih1 ih2 ⊢
    exact ⟨by rw [ih1], ih2⟩

/-- The element count of a core equals its list's length (an extra invariant the wrapper uses). -/
def CntEq (c : Core) (A : Abs) : Prop := c.count = A.elist.length

end OM.Proof

namespace OM.Proof

open OM.Model OM.Zeroing

set_option linter.deprecated false

/-- **What the wrapper's cost proof assumes**: the top structure's contracts (M5), the parameter
conditions, and Lemma R's I5 (M5 fixes `J` and `H`). -/
structure CostSetup (mk : Nat → Params) (TI PI : Core → Prop) (μ : Job → Nat) (ν : Core → Nat)
    (Jf capf nf Rf : Params → Nat) : Prop where
  top : ∀ N, TopContract TI μ (Jf (mk N)) (capf (mk N))
  prep : PrepContract TI PI ν
  core : ∀ N, CoreP (mk N)
  gp : ∀ N, GParams (mk N)
  cp : ∀ N, CParams (mk N)
  lp : ∀ N, LParams (mk N)
  kR : ∀ N, 1 ≤ (mk N).K_R
  R : ∀ N, Jf (mk N) / (mk N).K_R + 1 ≤ Rf (mk N)
  n1 : ∀ N, 1 ≤ nf (mk N)
  I5 : ∀ N, ((mk N).theta : ℝ) + Rf (mk N) * (Hn (nf (mk N) - 1) + 1) ≤ (mk N).T
  size : ∀ N, 2 + 2 * (N / ((mk N).theta + 1 - cmax (mk N))) ≤ nf (mk N) + 1
  capc : ∀ N, 2 + 2 * (N / ((mk N).theta + 1 - cmax (mk N))) ≤ capf (mk N)
  PN : ∀ N, (mk N).N = N
  prepB : ∀ N N', N' ≤ 4 * N → (mk N').H + 1 ≤ (mk N).L + 2
  small : ∀ N, 64 ≤ N → (mk N).L + 6 ≤ N / 2

variable {mk : Nat → Params} {TI PI : Core → Prop} {μ : Job → Nat} {ν : Core → Nat}
  {Jf capf nf Rf : Params → Nat}

/-- A core in service: the cost invariant for its element list, which it counts. -/
structure CoreOK (mk : Nat → Params) (TI : Core → Prop) (μ : Job → Nat)
    (Jf nf Rf : Params → Nat) (c : Core) (L : List Nat) : Prop where
  cost : CostInv TI μ (Jf c.P) (nf c.P) (Rf c.P) L c
  cnt : c.count = L.length
  pmk : c.P = mk c.P.N

theorem CoreOK.inv {c : Core} {L : List Nat} (h : CoreOK mk TI μ Jf nf Rf c L) :
    ∃ A, INV c A ∧ A.elist = L := h.cost.low.inv

/-- **Insertion into a core in service**: no FALLBACK while its count stays within capacity. -/
theorem CoreOK.insert {c : Core} {L : List Nat} (S : CostSetup mk TI PI μ ν Jf capf nf Rf)
    (h : CoreOK mk TI μ Jf nf Rf c L) {x : Nat} (hx : x ∈ L) (hcap : c.count + 1 ≤ c.P.N)
    (hh : Nat) :
    ∃ c', (insertAfter x hh).run c = .ok c.E.size c' ∧
      (do let y ← insertElem x hh; background y; pure y).run c = .ok c.E.size c' ∧
      CoreOK mk TI μ Jf nf Rf c' (OM.Spec.insertAfterL x c.E.size L) ∧
      c'.count = c.count + 1 ∧ c'.P = c.P := by
  have hmk := h.pmk
  generalize hN : c.P.N = N at hmk hcap
  have hdiv : (c.count + 1) / (c.P.theta + 1 - cmax c.P) ≤ N / (c.P.theta + 1 - cmax c.P) :=
    Nat.div_le_div_right hcap
  have hs := S.size N
  have hc := S.capc N
  rw [← hmk] at hs hc
  have hTC : TopContract TI μ (Jf c.P) (capf c.P) := by rw [hmk]; exact S.top N
  obtain ⟨c', hr, hnf, hC', hcnt, hP⟩ := insertAfter_cost hTC
    h.cost hx (by rw [hmk]; exact S.kR N) (by rw [hmk]; exact S.R N) (by rw [hmk]; exact S.n1 N)
    (by omega) (by omega) (by rw [hmk]; exact S.I5 N) hh
  refine ⟨c', hr, hnf, ⟨by rw [hP]; exact hC', ?_, by rw [hP, hN]; exact hmk⟩, hcnt, hP⟩
  obtain ⟨A, hI, hel⟩ := h.inv
  rw [hcnt, h.cnt, length_insertAfterL hx]

/-- **Deletion in a core in service.** -/
theorem CoreOK.markDead {c : Core} {L : List Nat} (S : CostSetup mk TI PI μ ν Jf capf nf Rf)
    (h : CoreOK mk TI μ Jf nf Rf c L) (x : Nat) :
    ∃ c', (OM.Model.markDead x).run c = .ok () c' ∧ CoreOK mk TI μ Jf nf Rf c' L ∧
      c'.count = c.count ∧ c'.P = c.P := by
  have hmk := h.pmk
  have hTC : TopContract TI μ (Jf c.P) (capf c.P) := by rw [hmk]; exact S.top c.P.N
  obtain ⟨c', hr, hC'⟩ := markDead_cost hTC h.cost x
  have he : c' = { c with E := c.E.modify x fun e => { e with live := false } } := by
    rw [markDead_run] at hr; cases hr; rfl
  subst he
  exact ⟨_, hr, ⟨hC', h.cnt, hmk⟩, rfl, rfl⟩

end OM.Proof

namespace OM.Proof

open OM.Model OM.Zeroing

set_option linter.deprecated false

variable {mk : Nat → Params} {TI PI : Core → Prop} {μ : Job → Nat} {ν : Core → Nat}
  {Jf capf nf Rf : Params → Nat}

/-- A core whose top structure is being built: it holds the sentinel alone. -/
structure PrepOK (mk : Nat → Params) (PI : Core → Prop) (n : Core) : Prop where
  pi : PI n
  low : LowInv n initAbs.elist
  inv : INV n initAbs
  cnt : n.count = 1
  pmk : n.P = mk n.P.N

theorem newCore_run {P : Params} {lazy : Bool} :
    ∃ n, newCore P lazy = .ok n ∧ (initCore lazy).run { P := P } = .ok () n := by
  obtain ⟨n, hr, -, -⟩ := initCore_run lazy { P := P }
  exact ⟨n, by unfold newCore; rw [runCore_ok hr]; rfl, hr⟩

theorem initCore_fields {s n : Core} {lazy : Bool} (h : (initCore lazy).run s = .ok () n) :
    n.count = 1 ∧ n.P = s.P := by
  obtain ⟨n', hr, -, -⟩ := initCore_run lazy s
  rw [hr] at h; cases h
  have hR : LowRel (initState s.P) n := by
    unfold initCore at hr
    simp only [run_getP_bind] at hr
    rw [run_bind, run_set] at hr
    dsimp only at hr
    have := low_initTop lazy (initState s.P)
    rw [hr] at this; exact this
  exact ⟨hR.1.count, hR.1.P⟩

/-- **A lazily built fresh core.** -/
theorem newCore_lazy (S : CostSetup mk TI PI μ ν Jf capf nf Rf) (N : Nat) :
    ∃ n, newCore (mk N) true = .ok n ∧ PrepOK mk PI n ∧ ν n ≤ (mk N).H + 1 := by
  obtain ⟨n, hnew, hr⟩ := newCore_run (P := mk N) (lazy := true)
  obtain ⟨hcnt, hP⟩ := initCore_fields hr
  obtain ⟨hL, hI⟩ := lowinv_initCore (S.gp N) (S.cp N) (S.lp N) hr
  obtain ⟨hPI, hν⟩ := S.prep.lazy _ _ hr
  exact ⟨n, hnew, ⟨hPI, hL, hI, hcnt, by rw [hP]; show mk N = mk (mk N).N; rw [S.PN]⟩, hν⟩

/-- **An eagerly built fresh core** is in service. -/
theorem newCore_eager (S : CostSetup mk TI PI μ ν Jf capf nf Rf) (N : Nat) :
    ∃ n, newCore (mk N) false = .ok n ∧ CoreOK mk TI μ Jf nf Rf n initAbs.elist ∧ n.count = 1 ∧
      n.P = mk N := by
  obtain ⟨n, hnew, hr⟩ := newCore_run (P := mk N) (lazy := false)
  obtain ⟨hcnt, hP⟩ := initCore_fields hr
  obtain ⟨hL, hI⟩ := lowinv_initCore (S.gp N) (S.cp N) (S.lp N) hr
  obtain ⟨hTI, hres⟩ := S.prep.eager _ _ hr
  refine ⟨n, hnew, ⟨costInv_fresh hL hTI hres (by rw [hP]; exact S.n1 N) (gval_fresh hL hI),
    by rw [hcnt, initAbs_elist]; rfl, by rw [hP]; show mk N = mk (mk N).N; rw [S.PN]⟩, hcnt, hP⟩

/-- **A preparation step** of a core being built: it finishes (the core is in service) or it
decreases `ν`. -/
theorem PrepOK.step (S : CostSetup mk TI PI μ ν Jf capf nf Rf) {n : Core}
    (h : PrepOK mk PI n) :
    ∃ b n', runCore n prepareStep = .ok (b, n') ∧ n'.count = n.count ∧ n'.P = n.P ∧
      INV n' initAbs ∧
      (b = true → CoreOK mk TI μ Jf nf Rf n' initAbs.elist) ∧
      (b = false → PrepOK mk PI n' ∧ ν n' < ν n) := by
  obtain ⟨b, n', hr, hL', hI', hR⟩ := prepareStep_low h.low h.inv
  obtain ⟨b2, n2, hr2, hT, hF⟩ := S.prep.step n h.pi
  rw [hr] at hr2; cases hr2
  have hP : n'.P = n.P := hR.1.P
  refine ⟨b, n', by rw [runCore_ok hr], hR.1.count, hP, hI', fun hb => ?_, fun hb => ?_⟩
  · obtain ⟨hTI, hres⟩ := hT hb
    have hpm := h.pmk
    have hn1 : 1 ≤ nf n'.P := by rw [hP, hpm]; exact S.n1 _
    have hc1 : n'.count = initAbs.elist.length := by rw [hR.1.count, h.cnt, initAbs_elist]; rfl
    have hpm' : n'.P = mk n'.P.N := by rw [hP]; exact hpm
    exact ⟨costInv_fresh hL' hTI hres hn1 (gval_fresh hL' hI'), hc1, hpm'⟩
  · obtain ⟨hPI, hν⟩ := hF hb
    have hc1 : n'.count = 1 := by rw [hR.1.count, h.cnt]
    have hpm' : n'.P = mk n'.P.N := by rw [hP]; exact h.pmk
    exact ⟨⟨hPI, hL', hI', hc1, hpm'⟩, hν⟩

end OM.Proof
