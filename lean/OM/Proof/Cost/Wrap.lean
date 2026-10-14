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

namespace OM.Proof

open OM.Model OM.Zeroing

set_option linter.deprecated false

variable {mk : Nat → Params} {TI PI : Core → Prop} {μ : Job → Nat} {ν : Core → Nat}
  {Jf capf nf Rf : Params → Nat}

/-- **Lemma W's record of a rebuild in progress**: `c₀` elements and `live₀` live ones at the
trigger, `I` insertions and `D` deletions since. The work left (preparation steps, then the
elements not yet scanned) shrinks by `K_B − 1` per insertion's worth of operations. -/
structure RebuildW (mk : Nat → Params) (TI PI : Core → Prop) (μ : Job → Nat) (ν : Core → Nat)
    (Jf nf Rf : Params → Nat) (om : OM) (n : Core) (c₀ live₀ I D : Nat) : Prop where
  c0 : c₀ ≤ om.cur.P.N / 2
  nP : n.P = mk (4 * max (live₀ + (c₀ + (om.cur.P.L + 2)) / (om.KB - 1) + 1) 16)
  ccnt : om.cur.count ≤ c₀ + I
  live : om.live + D = live₀ + I
  l0 : live₀ ≤ c₀
  prep : om.cursorSet = false → PrepOK mk PI n ∧
    ν n + om.cur.count + (om.KB - 1) * I ≤ om.cur.P.L + 2 + c₀
  serve : om.cursorSet = true →
    (∀ B, INV n B → CoreOK mk TI μ Jf nf Rf n B.elist ∧
      n.count ≤ 1 + (liveH n B.elist).length + D) ∧
    ∀ A, INV om.cur A → (postOf A.elist om.cursor).length + (om.KB - 1) * I ≤
      om.cur.P.L + 2 + c₀

/-- **The wrapper's cost invariant**: Invariant R, both cores' cost invariants, and Lemma W. -/
structure WC (mk : Nat → Params) (TI PI : Core → Prop) (μ : Job → Nat) (ν : Core → Nat)
    (Jf nf Rf : Params → Nat) (om : OM) (Sp : OM.Spec.State) : Prop where
  w : WInv om Sp
  live : om.live = Sp.list.length
  kb : 4 ≤ om.KB
  big : 64 ≤ om.cur.P.N
  cur : ∀ A, INV om.cur A → CoreOK mk TI μ Jf nf Rf om.cur A.elist
  idle : om.nxt = none → om.cur.count < om.cur.P.N / 2
  busy : ∀ n, om.nxt = some n → ∃ c₀ live₀ I D, RebuildW mk TI PI μ ν Jf nf Rf om n c₀ live₀ I D

/-- The work left bounds the insertions of a rebuild. -/
theorem RebuildW.ins_le {om : OM} {n : Core} {c₀ live₀ I D : Nat}
    (h : RebuildW mk TI PI μ ν Jf nf Rf om n c₀ live₀ I D) (hkb : 4 ≤ om.KB)
    (hA : ∃ A, INV om.cur A) :
    3 * I ≤ om.cur.P.L + 2 + c₀ := by
  have h3 : 3 * I ≤ (om.KB - 1) * I := Nat.mul_le_mul_right I (by omega)
  cases hs : om.cursorSet
  · have := (h.prep hs).2; omega
  · obtain ⟨A, hI⟩ := hA
    have := (h.serve hs).2 A hI; omega

/-- **Lemma W (1)**: `cur` has room for an insertion. -/
theorem WC.cur_room {om : OM} {Sp : OM.Spec.State} (S : CostSetup mk TI PI μ ν Jf capf nf Rf)
    (h : WC mk TI PI μ ν Jf nf Rf om Sp) : om.cur.count + 1 ≤ om.cur.P.N := by
  have hsm := S.small _ h.big
  have hmk : om.cur.P = mk om.cur.P.N := by
    obtain ⟨A, hR, -⟩ := h.w.core; exact (h.cur A hR.inv).pmk
  have hL : (mk om.cur.P.N).L = om.cur.P.L := by rw [← hmk]
  rw [hL] at hsm
  cases hn : om.nxt with
  | none => have := h.idle hn; omega
  | some n =>
    obtain ⟨c₀, live₀, I, D, hW⟩ := h.busy n hn
    have hI3 := hW.ins_le h.kb (by obtain ⟨A, hR, -⟩ := h.w.core; exact ⟨A, hR.inv⟩)
    have := hW.ccnt
    have := hW.c0
    omega

end OM.Proof

namespace OM.Proof

open OM.Model OM.Zeroing

set_option linter.deprecated false

variable {mk : Nat → Params} {TI PI : Core → Prop} {μ : Job → Nat} {ν : Core → Nat}
  {Jf capf nf Rf : Params → Nat}

/-- The copies in `nxt` are live elements of `cur`, so at most the live count. -/
theorem WC.nxt_live_le {om : OM} {Sp : OM.Spec.State} (h : WC mk TI PI μ ν Jf nf Rf om Sp)
    {n : Core} (hn : om.nxt = some n) (hset : om.cursorSet = true) {B : Abs} (hB : INV n B) :
    (liveH n B.elist).length ≤ om.live := by
  obtain ⟨-, -, A, hR, hL, -, hN⟩ := h.w
  unfold NxtR at hN; rw [hn] at hN
  obtain ⟨B', hRB', -, -, hcs⟩ := hN
  rw [if_pos hset] at hcs
  obtain ⟨pre, post, hsplit, -, -, hLB⟩ := hcs
  rw [INV.elist_unique hB hRB'.inv, hLB, h.live, ← hL, hsplit, liveH_append, List.length_append]
  omega

/-- **Lemma W (2)**: `nxt` has room for an insertion. -/
theorem WC.nxt_room {om : OM} {Sp : OM.Spec.State} (S : CostSetup mk TI PI μ ν Jf capf nf Rf)
    (h : WC mk TI PI μ ν Jf nf Rf om Sp) {n : Core} (hn : om.nxt = some n)
    (hset : om.cursorSet = true) : n.count + 1 ≤ n.P.N := by
  obtain ⟨c₀, live₀, I, D, hW⟩ := h.busy n hn
  obtain ⟨A, hR, -, -, hN⟩ := h.w.core
  obtain ⟨hserve, hpost⟩ := hW.serve hset
  have hB : ∃ B, INV n B := by
    unfold NxtR at hN; rw [hn] at hN
    obtain ⟨B, hRB, -⟩ := hN
    exact ⟨B, hRB.inv⟩
  obtain ⟨B, hB⟩ := hB
  have hc := (hserve B hB).2
  have hl := h.nxt_live_le hn hset hB
  have hlive := hW.live
  have hp := hpost A hR.inv
  have hkb := h.kb
  have hIq : I ≤ (c₀ + (om.cur.P.L + 2)) / (om.KB - 1) := by
    rw [Nat.le_div_iff_mul_le (by omega), Nat.mul_comm]; omega
  rw [hW.nP, S.PN]
  generalize (c₀ + (om.cur.P.L + 2)) / (om.KB - 1) = q at hIq ⊢
  have : live₀ + q + 1 ≤ max (live₀ + q + 1) 16 := le_max_left _ _
  omega

end OM.Proof

namespace OM.Proof

open OM.Model

set_option linter.deprecated false

theorem length_insertAfterL_le (x y : Nat) (l : List Nat) :
    (OM.Spec.insertAfterL x y l).length ≤ l.length + 1 := by
  induction l with
  | nil => simp [OM.Spec.insertAfterL]
  | cons a t ih =>
    simp only [OM.Spec.insertAfterL]
    split <;> simp <;> omega

/-- An insertion adds at most one element to the part from the cursor on. -/
theorem postOf_insertAfterL_le {a b c : Nat} (hbc : b ≠ c) (l : List Nat) :
    (postOf (OM.Spec.insertAfterL a b l) c).length ≤ (postOf l c).length + 1 := by
  induction l with
  | nil => simp [OM.Spec.insertAfterL, postOf]
  | cons x t ih =>
    simp only [OM.Spec.insertAfterL]
    by_cases hxa : x = a
    · rw [if_pos hxa]
      by_cases hxc : x = c
      · simp [postOf, hxc]
      · simp only [postOf, List.dropWhile_cons, ne_eq, decide_not, hxc, not_false_eq_true,
          decide_true, Bool.not_true, Bool.false_eq_true, if_false, hbc] at ih ⊢
        simp
    · rw [if_neg hxa]
      by_cases hxc : x = c
      · simp only [postOf, List.dropWhile_cons, hxc, ne_eq, not_true_eq_false, decide_false,
          Bool.not_false, if_true, List.length_cons]
        subst hxc
        have := length_insertAfterL_le a b t
        simp [hxa]; omega
      · simp only [postOf, List.dropWhile_cons, ne_eq, decide_not, hxc, not_false_eq_true,
          decide_true, Bool.not_true, Bool.false_eq_true, if_false] at ih ⊢
        exact ih

/-- Advancing the cursor drops one element. -/
theorem postOf_succOf {l : List Nat} (hnd : l.Nodup) (hnil : NIL ∉ l) {c : Nat} (hc : c ∈ l) :
    postOf l (succOf l c) = (postOf l c).tail := by
  induction l with
  | nil => simp at hc
  | cons x t ih =>
    have hxt : x ∉ t := (List.nodup_cons.mp hnd).1
    have hx0 : x ≠ NIL := fun e => hnil (by rw [← e]; simp)
    by_cases hxc : x = c
    · subst hxc
      rw [succOf_cons_self]
      cases t with
      | nil => simp [postOf]; exact hx0
      | cons y t' =>
        have hxy : x ≠ y := fun e => hxt (by rw [e]; simp)
        simp [postOf, hxy]
    · have hct : c ∈ t := by simp at hc; rcases hc with h | h; exact absurd h.symm hxc; exact h
      rw [succOf_cons_ne hxc]
      have hxs : x ≠ succOf t c := by
        intro e
        by_cases h : succOf t c = NIL
        · exact hx0 (e.trans h)
        · have : succOf t c ∈ t := by
            obtain ⟨l1, l2, e2⟩ := succOf_split (rfl : succOf t c = succOf t c) h
            have hm : succOf t c ∈ l1 ++ c :: succOf t c :: l2 := by simp
            rwa [← e2] at hm
          exact hxt (e ▸ this)
      simp only [postOf, List.dropWhile_cons, ne_eq, decide_not, hxs, hxc, not_false_eq_true,
        decide_true, Bool.not_true, Bool.false_eq_true, if_false]
      exact ih (List.nodup_cons.mp hnd).2 (fun h => hnil (List.mem_cons_of_mem _ h)) hct

theorem postOf_headD {l : List Nat} (hne : l ≠ []) : postOf l (l.headD NIL) = l := by
  cases l with
  | nil => exact absurd rfl hne
  | cons a t => simp [postOf]

end OM.Proof

namespace OM.Proof

open OM.Model OM.Zeroing

set_option linter.deprecated false

variable {mk : Nat → Params} {TI PI : Core → Prop} {μ : Job → Nat} {ν : Core → Nat}
  {Jf capf nf Rf : Params → Nat}

/-- **A copy step** keeps the nxt core in service and its fill bound, and advances the cursor. -/
theorem copy_cost (S : CostSetup mk TI PI μ ν Jf capf nf Rf) {om : OM} {n : Core} {A B : Abs}
    {D : Nat} (hR : CoreR om.cur A) (hRB : CoreR n B) (hset : om.cursorSet = true)
    (hcur : om.cursor ≠ NIL) (hcurA : om.cursor ∈ A.elist)
    (hok : CoreOK mk TI μ Jf nf Rf n B.elist) (hfill : n.count ≤ 1 + (liveH n B.elist).length + D)
    (hroom : n.count + 1 ≤ n.P.N) :
    ∃ om' n' B', copyAtCursor om n = .ok (om', n') ∧ om'.cursor = eN om.cur om.cursor ∧
      CoreR n' B' ∧ CoreOK mk TI μ Jf nf Rf n' B'.elist ∧
      n'.count ≤ 1 + (liveH n' B'.elist).length + D ∧ n'.P = n.P := by
  unfold copyAtCursor
  by_cases hl : live om.cur om.cursor = true
  · have hl' : (om.cur.E.getX om.cursor).live = true := hl
    simp only [hl', if_true]
    have htail : n.tail ∈ B.elist := by
      rw [hRB.inv.tail]
      obtain ⟨b, bt, hb⟩ := List.exists_cons_of_ne_nil hRB.ne
      rw [hb]; exact getLastD_cons_mem _ _ _
    obtain ⟨n', B', hr', hRB', hB', hrecB, hlyB, hhyB, hyB, _, _, hP'⟩ :=
      core_insert hRB htail (hdl om.cur om.cursor)
    obtain ⟨n2, hr2, -, hok2, hcnt2, hP2⟩ := hok.insert S htail hroom (hdl om.cur om.cursor)
    rw [hr'] at hr2; cases hr2
    simp only [bind, Except.bind]
    rw [show (om.cur.E.getX om.cursor).h = hdl om.cur om.cursor from rfl, runCore_ok hr']
    have hB'e : B'.elist = B.elist ++ [n.E.size] := by
      rw [hB', hRB.inv.tail]; exact insertAfterL_getLastD hRB.inv.eList.nodup hRB.ne _
    have hLn : liveH n' B'.elist = liveH n B.elist ++ [hdl om.cur om.cursor] := by
      rw [hB'e, liveH_append, liveH_frame hrecB]
      simp [FM_cons, hlyB, hhyB]
    refine ⟨_, n', B', rfl, rfl, hRB', by rw [hB']; exact hok2, ?_, hP2⟩
    rw [hLn, List.length_append, hcnt2]; simp; omega
  · have hl' : (om.cur.E.getX om.cursor).live = false := by simpa [live] using hl
    simp only [hl', Bool.false_eq_true, if_false]
    exact ⟨_, n, B, rfl, rfl, hRB, hok, hfill, rfl⟩

end OM.Proof

namespace OM.Proof

open OM.Model OM.Zeroing

set_option linter.deprecated false

variable {mk : Nat → Params} {TI PI : Core → Prop} {μ : Job → Nat} {ν : Core → Nat}
  {Jf capf nf Rf : Params → Nat}

/-- The rebuild loop's cost invariant, with `budget` steps left, within the entry potential `Φe`. -/
structure LoopC (mk : Nat → Params) (TI PI : Core → Prop) (μ : Job → Nat) (ν : Core → Nat)
    (Jf nf Rf : Params → Nat) (om : OM) (n : Core) (A : Abs) (budget Φe live₀ I D N' : Nat) :
    Prop where
  curok : CoreOK mk TI μ Jf nf Rf om.cur A.elist
  nP : n.P = mk N'
  prep : om.cursorSet = false → PrepOK mk PI n ∧ ν n + om.cur.count + (om.KB - budget) ≤ Φe
  serve : om.cursorSet = true →
    (∀ B, INV n B → CoreOK mk TI μ Jf nf Rf n B.elist ∧
      n.count ≤ 1 + (liveH n B.elist).length + D) ∧
    (postOf A.elist om.cursor).length + (om.KB - budget) ≤ Φe
  room : 1 + live₀ + I + 1 ≤ N'
  live : om.live + D = live₀ + I
  bud : budget ≤ om.KB

/-- What the rebuild loop leaves: the rebuild goes on, having spent the whole budget, or `nxt`
replaced `cur`. -/
def LoopOut (mk : Nat → Params) (TI PI : Core → Prop) (μ : Job → Nat) (ν : Core → Nat)
    (Jf nf Rf : Params → Nat) (om om' : OM) (A : Abs) (Φe live₀ I D N' : Nat) : Prop :=
  (∃ n', om'.nxt = some n' ∧ om'.cur = om.cur ∧ om'.KB = om.KB ∧
      LoopC mk TI PI μ ν Jf nf Rf om' n' A 0 Φe live₀ I D N') ∨
    (om'.nxt = none ∧ om'.cur.P = mk N' ∧ om'.KB = om.KB ∧ om'.live = om.live ∧
      (∀ B, INV om'.cur B → CoreOK mk TI μ Jf nf Rf om'.cur B.elist) ∧
      om'.cur.count ≤ 1 + live₀ + I)

end OM.Proof

namespace OM.Proof

open OM.Model OM.Zeroing

set_option linter.deprecated false

variable {mk : Nat → Params} {TI PI : Core → Prop} {μ : Job → Nat} {ν : Core → Nat}
  {Jf capf nf Rf : Params → Nat}

theorem LoopC.congr {om om' : OM} {n : Core} {A : Abs} {budget Φe live₀ I D N' : Nat}
    (h : LoopC mk TI PI μ ν Jf nf Rf om n A budget Φe live₀ I D N') (hc : om'.cur = om.cur)
    (hs : om'.cursorSet = om.cursorSet) (hu : om'.cursor = om.cursor) (hk : om'.KB = om.KB)
    (hl : om'.live = om.live) : LoopC mk TI PI μ ν Jf nf Rf om' n A budget Φe live₀ I D N' := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7⟩ := h
  refine ⟨by rw [hc]; exact h1, h2, fun h => ?_, fun h => ?_, h5, by rw [hl]; exact h6,
    by rw [hk]; exact h7⟩
  · rw [hs] at h; rw [hc, hk]; exact h3 h
  · rw [hs] at h; rw [hu, hk]; exact h4 h

theorem LoopOut.mono {om om1 om' : OM} {A : Abs} {Φe live₀ I D N' : Nat}
    (h : LoopOut mk TI PI μ ν Jf nf Rf om1 om' A Φe live₀ I D N') (hc : om1.cur = om.cur)
    (hk : om1.KB = om.KB) (hl : om1.live = om.live) :
    LoopOut mk TI PI μ ν Jf nf Rf om om' A Φe live₀ I D N' := by
  rcases h with ⟨n', h1, h2, h3, h4⟩ | ⟨h1, h2, h3, h4, h5, h6⟩
  · exact Or.inl ⟨n', h1, h2.trans hc, h3.trans hk, h4⟩
  · exact Or.inr ⟨h1, h2, h3.trans hk, h4.trans hl, h5, h6⟩

/-- The live copies are at most the live count, inside the loop. -/
theorem nxtR'_live_le {c : Core} {A : Abs} {om : OM} {n : Core} {Sp : OM.Spec.State}
    (hN : NxtR' c A om n) (hL : liveH c A.elist = Sp.list) (hset : om.cursorSet = true)
    {B : Abs} (hB : INV n B) : (liveH n B.elist).length ≤ Sp.list.length := by
  obtain ⟨B', hRB', -, -, hcs⟩ := hN
  rw [if_pos hset] at hcs
  obtain ⟨pre, post, hsplit, -, -, hLB⟩ := hcs
  rw [INV.elist_unique hB hRB'.inv, hLB, ← hL, hsplit, liveH_append, List.length_append]
  omega

end OM.Proof

namespace OM.Proof

open OM.Model OM.Zeroing

set_option linter.deprecated false

variable {mk : Nat → Params} {TI PI : Core → Prop} {μ : Job → Nat} {ν : Core → Nat}
  {Jf capf nf Rf : Params → Nat}

/-- **The rebuild loop** (Lemma W's length argument): every budgeted step shrinks the work left by
one; the loop ends with the budget spent or with the swap. -/
theorem rebuildLoop_cost (S : CostSetup mk TI PI μ ν Jf capf nf Rf) {Sp : OM.Spec.State}
    (hS : OM.Spec.Inv Sp) {Φe live₀ I D N' : Nat} :
    ∀ fuel budget (om : OM) (n : Core) (A : Abs), CoreR om.cur A →
      liveH om.cur A.elist = Sp.list → IdxOK om.cur A om.curIdx Sp.list → NxtR' om.cur A om n →
      om.nextHandle = Sp.fresh → om.live = Sp.list.length →
      LoopC mk TI PI μ ν Jf nf Rf om n A budget Φe live₀ I D N' →
      budget + (if om.cursorSet then 0 else 1) ≤ fuel →
      ∃ om', rebuildLoop om n fuel budget = .ok om' ∧ WInv om' Sp ∧ om'.live = om.live ∧
        LoopOut mk TI PI μ ν Jf nf Rf om om' A Φe live₀ I D N' := by
  intro fuel
  induction fuel with
  | zero =>
    intro budget om n A hR hL hI hN hf hlv hC hfu
    have hb : budget = 0 := by split at hfu <;> omega
    subst hb
    exact ⟨_, rfl, ⟨hS, hf, A, hR, hL, hI, hN⟩, rfl, Or.inl ⟨n, rfl, rfl, rfl,
      hC.congr rfl rfl rfl rfl rfl⟩⟩
  | succ fuel ih =>
    intro budget om n A hR hL hI hN hf hlv hC hfu
    have hnd : (liveH om.cur A.elist).Nodup := hL ▸ hS.1
    unfold rebuildLoop
    by_cases hb : budget = 0
    · rw [if_pos hb]; subst hb
      exact ⟨_, rfl, ⟨hS, hf, A, hR, hL, hI, hN⟩, rfl, Or.inl ⟨n, rfl, rfl, rfl,
        hC.congr rfl rfl rfl rfl rfl⟩⟩
    rw [if_neg hb]
    by_cases hset : om.cursorSet = true
    · rw [if_neg (by simp [hset])]
      obtain ⟨hserve, hpost⟩ := hC.serve hset
      have hN0 := hN
      obtain ⟨B, hRB, hIB, hzB, hcs⟩ := hN0
      rw [if_pos hset] at hcs
      obtain ⟨pre, post, hsplit, hcpost, hpre, hLB⟩ := hcs
      have hlB := nxtR'_live_le hN hL hset hRB.inv
      have hfill := (hserve B hRB.inv).2
      have hlive := hC.live
      by_cases hc : om.cursor = NIL
      · rw [if_pos hc]
        refine ⟨_, rfl, swap_ok hN hR hL hset hc hS hf, rfl, Or.inr ⟨rfl, hC.nP, rfl, rfl,
          fun B' hB' => (hserve B' hB').1, ?_⟩⟩
        show n.count ≤ 1 + live₀ + I
        omega
      rw [if_neg hc]
      obtain ⟨om', n', hcp, e1, e2, e3, e4, e5, e6, e7, hN'⟩ := copy_ok hN hR hnd hset hc
      have hcurA : om.cursor ∈ A.elist := by
        rw [hsplit, hcpost]
        cases post with
        | nil => exact absurd hcpost hc
        | cons a t => simp
      have hroom : n.count + 1 ≤ n.P.N := by
        rw [hC.nP, S.PN]; have := hC.room; omega
      obtain ⟨om2, n2, B2, hcp2, hcur2, hRB2, hok2, hfill2, hP2⟩ :=
        copy_cost S hR hRB hset hc hcurA (hserve B hRB.inv).1 hfill hroom
      rw [hcp] at hcp2
      injection hcp2 with hcp2
      injection hcp2 with h1 h2
      subst h1; subst h2
      simp only [bind, Except.bind, hcp]
      -- the work left after the copy
      have hpo : postOf A.elist om.cursor = post := by
        rw [hsplit]
        exact (split_unique (hsplit ▸ hR.inv.eList.nodup) (hsplit ▸ hR.inv.eList.nonil) hcpost).2
      have hpne : post ≠ [] := by intro h; rw [h] at hcpost; exact hc hcpost
      have hpost' : (postOf A.elist om'.cursor).length + 1 = (postOf A.elist om.cursor).length := by
        rw [hcur2, hR.inv.eList.next _ hcurA, postOf_succOf hR.inv.eList.nodup hR.inv.eList.nonil hcurA,
          hpo, List.length_tail]
        have := List.length_pos_of_ne_nil hpne; omega
      have hC' : LoopC mk TI PI μ ν Jf nf Rf om' n' A (budget - 1) Φe live₀ I D N' := by
        refine ⟨by rw [e1]; exact hC.curok, by rw [hP2]; exact hC.nP, fun h => absurd (e4 ▸ h)
          (by simp [hset]), fun _ => ⟨fun B' hB' => ?_, ?_⟩, hC.room, by rw [e6]; exact hlive,
          by rw [e7]; have := hC.bud; omega⟩
        · rw [INV.elist_unique hB' hRB2.inv]; exact ⟨hok2, hfill2⟩
        · rw [e7]; have := hC.bud; omega
      by_cases hc' : om'.cursor = NIL
      · rw [if_pos hc']
        have hN'' := e1 ▸ hN'
        obtain ⟨Bx, hRBx, -, -, hcsx⟩ := hN''
        refine ⟨_, rfl, swap_ok (om := om') (e1 ▸ hN') (e1 ▸ hR) (e1 ▸ hL) (e4 ▸ hset) hc' hS
          (e5 ▸ hf), e6, Or.inr ⟨rfl, hC'.nP, e7, e6, fun B' hB' => ((hC'.serve (e4 ▸ hset)).1 B' hB').1,
          ?_⟩⟩
        show n'.count ≤ 1 + live₀ + I
        have := nxtR'_live_le (e1 ▸ hN') (e1 ▸ hL) (e4 ▸ hset) hRB2.inv
        omega
      · rw [if_neg hc']
        obtain ⟨om'', h1, h2, h3, h4⟩ := ih (budget - 1) om' n' A (e1 ▸ hR) (e1 ▸ hL)
          (e1 ▸ e2 ▸ hI) (e1 ▸ hN') (e5 ▸ hf) (by rw [e6]; exact hlv) hC'
          (by rw [e4, if_pos hset]; rw [if_pos hset] at hfu; omega)
        exact ⟨om'', h1, h2, h3.trans e6, h4.mono e1 e7 e6⟩
    · have hf' : om.cursorSet = false := by simpa using hset
      rw [if_pos (by simp [hf'])]
      obtain ⟨hprep, hφ⟩ := hC.prep hf'
      obtain ⟨ready, n', hr, hN1, hN2⟩ := prepare_ok hN hR hf'
      obtain ⟨b, n2, hr2, hcnt2, hP2, hI2, hT2, hF2⟩ := hprep.step S
      rw [hr] at hr2
      injection hr2 with hr2
      injection hr2 with h1 h2
      subst h1; subst h2
      simp only [bind, Except.bind, hr]
      cases ready with
      | true =>
        rw [if_pos rfl]
        have hok := hT2 rfl
        set om1 : OM := { om with cursor := (om.cur.E.getX om.cur.head).next, cursorSet := true }
          with hom1
        have hcnt : om.cur.count = A.elist.length := by
          have := hC.curok.cnt; exact this
        have hpost1 : (postOf A.elist om1.cursor).length + 1 = A.elist.length := by
          show (postOf A.elist (eN om.cur om.cur.head)).length + 1 = _
          rw [hR.inv.eList.next _ hR.head, hR.inv.eList.head,
            postOf_succOf hR.inv.eList.nodup hR.inv.eList.nonil
              (by rw [← hR.inv.eList.head]; exact hR.head), postOf_headD hR.ne, List.length_tail]
          have := List.length_pos_of_ne_nil hR.ne; omega
        have hC1 : LoopC mk TI PI μ ν Jf nf Rf om1 n' A budget Φe live₀ I D N' := by
          refine ⟨hC.curok, by rw [hP2]; exact hC.nP, fun h => by simp [hom1] at h, fun _ =>
            ⟨fun B' hB' => ?_, ?_⟩, hC.room, hC.live, hC.bud⟩
          · rw [INV.elist_unique hB' hI2]
            refine ⟨hok, ?_⟩
            rw [hcnt2, hprep.cnt]; omega
          · show (postOf A.elist om1.cursor).length + (om.KB - budget) ≤ Φe
            omega
        obtain ⟨om'', h1, h2, h3, h4⟩ := ih budget om1 n' A hR hL hI (hN2 rfl) hf hlv hC1
          (by simp [hom1]; rw [if_neg (by simp [hf'])] at hfu; omega)
        exact ⟨om'', h1, h2, h3, h4.mono rfl rfl rfl⟩
      | false =>
        simp only [Bool.false_eq_true, if_false]
        obtain ⟨hprep', hν⟩ := hF2 rfl
        have hC1 : LoopC mk TI PI μ ν Jf nf Rf om n' A (budget - 1) Φe live₀ I D N' := by
          refine ⟨hC.curok, by rw [hP2]; exact hC.nP, fun _ => ⟨hprep', ?_⟩,
            fun h => absurd h (by simp [hf']), hC.room, hC.live, by have := hC.bud; omega⟩
          have := hC.bud; omega
        obtain ⟨om'', h1, h2, h3, h4⟩ := ih (budget - 1) om n' A hR hL hI hN1 hf hlv hC1
          (by rw [if_neg (by simp [hf'])] at hfu ⊢; omega)
        exact ⟨om'', h1, h2, h3, h4⟩

end OM.Proof
