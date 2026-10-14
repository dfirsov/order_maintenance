import OM.Proof.Cost.LHooks

/-!
# Scheduling: the priority queue and the zeroing game

The queue holds exactly the quiet chunks above `θ`, keyed by their sizes (`PQC`). So `pqPopMax`
returns a chunk of largest game value, and `pqEmpty` says that every value is 0. Every step but
the insertion's size update and the pop leaves the queue, and the quiet sizes it reads, alone.
-/

namespace OM.Proof

open OM.Model

set_option linter.deprecated false

/-- The chunks the queue must hold: live, quiet, above `θ`. -/
def inQC (s : Core) (c : Nat) : Bool := decide (LiveC s c ∧ cSt s c = .quiet ∧ s.P.theta < cSz s c)

/-- **The queue invariant.** -/
def PQC (s : Core) : Prop := QInv s (cSz s) (inQC s)

/-- The queue's own fields. -/
structure PQSame (s s' : Core) : Prop where
  where_ : s'.pqWhere = s.pqWhere
  next : s'.pqNext = s.pqNext
  prev : s'.pqPrev = s.pqPrev
  head : s'.pqHead = s.pqHead
  nbn : s'.nbNext = s.nbNext
  nbp : s'.nbPrev = s.nbPrev
  lo : s'.pqLo = s.pqLo
  hi : s'.pqHi = s.pqHi
  theta : s'.P.theta = s.P.theta

theorem QRep.congr {s s' : Core} {k k' : Nat → Nat} {inQ inQ' : Nat → Bool} {bl : Nat → List Nat}
    {nb : List Nat} (hQ : QRep s k inQ bl nb) (S : PQSame s s') (hin : ∀ c, inQ' c = inQ c)
    (hk : ∀ c, inQ c = true → k' c = k c) : QRep s' k' inQ' bl nb where
  where_ c := by
    rw [S.where_, hQ.where_, hin]
    by_cases h : inQ c = true
    · rw [if_pos h, if_pos h, hk c h]
    · rw [if_neg h, if_neg h]
  pos c h := by rw [hin] at h; rw [S.theta, hk c h]; exact hQ.pos c h
  bucket b := by rw [S.next, S.prev, S.head]; exact hQ.bucket b
  bmem b c := by
    rw [hQ.bmem, hin]
    constructor
    · rintro ⟨h1, h2⟩; exact ⟨h1, by rw [hk c h1]; exact h2⟩
    · rintro ⟨h1, h2⟩; exact ⟨h1, by rw [← hk c h1]; exact h2⟩
  nbl := by rw [S.nbn, S.nbp, S.lo]; exact hQ.nbl
  nbmem := hQ.nbmem
  sorted := hQ.sorted
  hi := by rw [S.hi]; exact hQ.hi

theorem QInv.congr {s s' : Core} {k k' : Nat → Nat} {inQ inQ' : Nat → Bool}
    (hQ : QInv s k inQ) (S : PQSame s s') (hin : ∀ c, inQ' c = inQ c)
    (hk : ∀ c, inQ c = true → k' c = k c) : QInv s' k' inQ' := by
  obtain ⟨bl, nb, h⟩ := hQ; exact ⟨bl, nb, h.congr S hin hk⟩

theorem PQSame.refl (s : Core) : PQSame s s := ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

theorem PQSame.trans {a b c : Core} (h1 : PQSame a b) (h2 : PQSame b c) : PQSame a c :=
  ⟨h2.where_.trans h1.where_, h2.next.trans h1.next, h2.prev.trans h1.prev, h2.head.trans h1.head,
    h2.nbn.trans h1.nbn, h2.nbp.trans h1.nbp, h2.lo.trans h1.lo, h2.hi.trans h1.hi,
    h2.theta.trans h1.theta⟩

/-- **A frame for the queue invariant**: the queue's fields are unchanged, and so are the queued
chunks and their sizes. -/
theorem PQC.frame {s s' : Core} (h : PQC s) (S : PQSame s s')
    (hin : ∀ c, inQC s' c = inQC s c) (hk : ∀ c, inQC s c = true → cSz s' c = cSz s c) :
    PQC s' := QInv.congr h S hin hk

/-- What `PQC` and the game read of the chunks. -/
structure QSame (s s' : Core) : Prop where
  Csize : s'.C.size = s.C.size
  P : s'.P = s.P
  q : ∀ c, LiveC s c → (cSt s' c = .quiet ↔ cSt s c = .quiet)
  sz : ∀ c, LiveC s c → cSt s c = .quiet → cSz s' c = cSz s c

theorem QSame.inQC {s s' : Core} (h : QSame s s') (c : Nat) : inQC s' c = inQC s c := by
  unfold OM.Proof.inQC
  have hL : LiveC s' c ↔ LiveC s c := by simp only [LiveC, h.Csize]
  by_cases hc : LiveC s c
  · by_cases hq : cSt s c = .quiet
    · rw [h.sz c hc hq, h.P]; simp [hc, hq, hL.mpr hc, (h.q c hc).mpr hq]
    · have : ¬ cSt s' c = .quiet := fun e => hq ((h.q c hc).mp e)
      simp [hq, this]
  · have : ¬ LiveC s' c := fun e => hc (hL.mp e)
    simp [hc, this]

theorem PQC.qsame {s s' : Core} (h : PQC s) (S : PQSame s s') (Q : QSame s s') : PQC s' :=
  h.frame S Q.inQC (fun c hc => by
    unfold OM.Proof.inQC at hc; simp only [decide_eq_true_eq] at hc
    exact Q.sz c hc.1 hc.2.1)

/-- The game values agree when the quiet sizes do. -/
theorem QSame.gval {s s' : Core} (h : QSame s s') (c : Nat) : gval s' c = gval s c := by
  unfold OM.Proof.gval
  have hL : LiveC s' c ↔ LiveC s c := by simp only [LiveC, h.Csize]
  by_cases hc : LiveC s c
  · by_cases hq : cSt s c = .quiet
    · rw [h.sz c hc hq, h.P]; simp [hc, hq, hL.mpr hc, (h.q c hc).mpr hq]
    · have : ¬ cSt s' c = .quiet := fun e => hq ((h.q c hc).mp e)
      simp [hq, this]
  · have : ¬ LiveC s' c := fun e => hc (hL.mp e)
    simp [hc, this]

theorem QSame.gvec {s s' : Core} (h : QSame s s') (n : Nat) : gvec n s' = gvec n s := by
  funext i; unfold OM.Proof.gvec; rw [h.gval]

theorem QSame.refl (s : Core) : QSame s s := ⟨rfl, rfl, fun _ _ => Iff.rfl, fun _ _ _ => rfl⟩

theorem QSame.trans {a b c : Core} (h1 : QSame a b) (h2 : QSame b c) : QSame a c := by
  have hL : ∀ d, LiveC a d → LiveC b d := fun d hd => by simp only [LiveC, h1.Csize]; exact hd
  refine ⟨h2.Csize.trans h1.Csize, h2.P.trans h1.P, fun d hd => (h2.q d (hL d hd)).trans (h1.q d hd),
    fun d hd hq => ?_⟩
  rw [h2.sz d (hL d hd) ((h1.q d hd).mpr hq), h1.sz d hd hq]

end OM.Proof

namespace OM.Proof

open OM.Model

set_option linter.deprecated false

/-! ### What the group phase leaves alone -/

/-- Chunk fields other than `first`/`last`, the queue and the top structure are unchanged. -/
structure CFrame (s s' : Core) : Prop where
  C : ∀ c, cSz s' c = cSz s c ∧ cSt s' c = cSt s c ∧ cSrc s' c = cSrc s c ∧ cLl s' c = cLl s c ∧
    cRr s' c = cRr s c ∧ cN s' c = cN s c ∧ cP s' c = cP s c ∧ cT s' c = cT s c
  Csize : s'.C.size = s.C.size
  P : s'.P = s.P
  pq : PQSame s s'
  top : s'.nodes = s.nodes ∧ s'.path = s.path ∧ s'.cin = s.cin ∧ s'.lpar = s.lpar ∧
    s'.resJob = s.resJob ∧ s'.prep = s.prep ∧ s'.ready = s.ready ∧ s'.firstChunk = s.firstChunk

theorem CFrame.refl (s : Core) : CFrame s s :=
  ⟨fun _ => ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩, rfl, rfl, PQSame.refl s,
    ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩⟩

theorem CFrame.trans {a b c : Core} (h1 : CFrame a b) (h2 : CFrame b c) : CFrame a c := by
  obtain ⟨C1, s1, P1, q1, ⟨t1, t2, t3, t4, t5, t6, t7, t8⟩⟩ := h1
  obtain ⟨C2, s2, P2, q2, ⟨u1, u2, u3, u4, u5, u6, u7, u8⟩⟩ := h2
  refine ⟨fun d => ?_, s2.trans s1, P2.trans P1, q1.trans q2,
    ⟨u1.trans t1, u2.trans t2, u3.trans t3, u4.trans t4, u5.trans t5, u6.trans t6, u7.trans t7,
      u8.trans t8⟩⟩
  obtain ⟨a1, a2, a3, a4, a5, a6, a7, a8⟩ := C1 d
  obtain ⟨b1, b2, b3, b4, b5, b6, b7, b8⟩ := C2 d
  exact ⟨b1.trans a1, b2.trans a2, b3.trans a3, b4.trans a4, b5.trans a5, b6.trans a6, b7.trans a7,
    b8.trans a8⟩

theorem CFrame.qsame {s s' : Core} (h : CFrame s s') : QSame s s' :=
  ⟨h.Csize, h.P, fun c _ => by rw [(h.C c).2.1], fun c _ _ => (h.C c).1⟩

/-- A frame from equal chunk arrays. -/
theorem CFrame.of_C {s s' : Core} (hC : s'.C = s.C) (hP : s'.P = s.P) (hq : PQSame s s')
    (ht : s'.nodes = s.nodes ∧ s'.path = s.path ∧ s'.cin = s.cin ∧ s'.lpar = s.lpar ∧
      s'.resJob = s.resJob ∧ s'.prep = s.prep ∧ s'.ready = s.ready ∧
      s'.firstChunk = s.firstChunk) : CFrame s s' :=
  ⟨fun c => by simp only [cSz, cSt, cSrc, cLl, cRr, cN, cP, cT, hC, and_self], by rw [hC], hP, hq,
    ht⟩

theorem unlinkGroup_cfields (s : Core) (g z : Nat) :
    cSz (unlinkGroup s g) z = cSz s z ∧ cSt (unlinkGroup s g) z = cSt s z ∧
      cSrc (unlinkGroup s g) z = cSrc s z ∧ cLl (unlinkGroup s g) z = cLl s z ∧
      cRr (unlinkGroup s g) z = cRr s z ∧ cN (unlinkGroup s g) z = cN s z ∧
      cP (unlinkGroup s g) z = cP s z ∧ cT (unlinkGroup s g) z = cT s z := by
  simp only [cSz, cSt, cSrc, cLl, cRr, cN, cP, cT, unlinkGroup]
  split_ifs <;> simp only [Array.getX_modify] <;> (try split) <;> simp

theorem cframe_remove (s : Core) (p : Nat) : CFrame s (removeState s p) := by
  have hC : (removeState s p).C = (unlinkGroup s p).C := rfl
  have hu := unlinkGroup_cfields s p
  have hfc : (removeState s p).firstChunk = (unlinkGroup s p).firstChunk := rfl
  have hfc' : (unlinkGroup s p).firstChunk = s.firstChunk :=
    (unlinkGroup_rest (s := s) (g := p)).2.2.2.2.2.1
  have hpq : PQSame s (removeState s p) := by
    unfold removeState unlinkGroup; exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
  have htop : (removeState s p).nodes = s.nodes ∧ (removeState s p).path = s.path ∧
      (removeState s p).cin = s.cin ∧ (removeState s p).lpar = s.lpar ∧
      (removeState s p).resJob = s.resJob ∧ (removeState s p).prep = s.prep ∧
      (removeState s p).ready = s.ready := by
    unfold removeState unlinkGroup; exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
  refine ⟨fun c => ?_, by rw [hC]; exact (unlinkGroup_rest (s := s) (g := p)).2.1, rfl, hpq,
    ⟨htop.1, htop.2.1, htop.2.2.1, htop.2.2.2.1, htop.2.2.2.2.1, htop.2.2.2.2.2.1,
      htop.2.2.2.2.2.2, hfc.trans hfc'⟩⟩
  simp only [cSz, cSt, cSrc, cLl, cRr, cN, cP, cT, hC]
  exact hu c

theorem cframe_moveL (s : Core) (p : Nat) : CFrame s (moveLState s p) :=
  CFrame.of_C rfl rfl ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
    ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

theorem cframe_moveR (s : Core) (p : Nat) : CFrame s (moveRState s p) :=
  CFrame.of_C rfl rfl ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
    ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

theorem allocGroup_frame (s : Core) (c : Nat) :
    PQSame s (allocGroup s c).2 ∧ (allocGroup s c).2.nodes = s.nodes ∧
      (allocGroup s c).2.path = s.path ∧ (allocGroup s c).2.cin = s.cin ∧
      (allocGroup s c).2.lpar = s.lpar ∧ (allocGroup s c).2.resJob = s.resJob ∧
      (allocGroup s c).2.prep = s.prep ∧ (allocGroup s c).2.ready = s.ready ∧
      (allocGroup s c).2.firstChunk = s.firstChunk := by
  unfold allocGroup
  split <;> exact ⟨⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩, rfl, rfl, rfl, rfl, rfl, rfl, rfl,
    rfl⟩

theorem linkGroupPair_frame (t : Core) (g gl gr labL labR : Nat) :
    PQSame t (linkGroupPair t g gl gr labL labR) ∧ (linkGroupPair t g gl gr labL labR).nodes = t.nodes ∧
      (linkGroupPair t g gl gr labL labR).path = t.path ∧
      (linkGroupPair t g gl gr labL labR).cin = t.cin ∧
      (linkGroupPair t g gl gr labL labR).lpar = t.lpar ∧
      (linkGroupPair t g gl gr labL labR).resJob = t.resJob ∧
      (linkGroupPair t g gl gr labL labR).prep = t.prep ∧
      (linkGroupPair t g gl gr labL labR).ready = t.ready ∧
      (linkGroupPair t g gl gr labL labR).firstChunk = t.firstChunk := by
  unfold linkGroupPair
  exact ⟨⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

theorem cframe_split {s : Core} {A : Abs} {g labL labR : Nat} (hI : INV s A) (hg : LiveG s g) :
    CFrame s (splitState s g labL labR) := by
  have S := splitSpec hI (hI.mem_glist_iff.mpr hg) labL labR
  obtain ⟨q1, n1, p1, c1, l1, r1, pr1, rd1, f1⟩ := allocGroup_frame s (gC s g)
  obtain ⟨q2, n2, p2, c2, l2, r2, pr2, rd2, f2⟩ :=
    allocGroup_frame (allocGroup s (gC s g)).2 (gC s g)
  obtain ⟨q3, n3, p3, c3, l3, r3, pr3, rd3, f3⟩ := linkGroupPair_frame
    (allocGroup (allocGroup s (gC s g)).2 (gC s g)).2 g (splitL s g) (splitR s g) labL labR
  refine ⟨fun c => ?_, S.Csize, S.P, q1.trans (q2.trans q3), ⟨(n3.trans n2).trans n1,
    (p3.trans p2).trans p1, (c3.trans c2).trans c1, (l3.trans l2).trans l1, (r3.trans r2).trans r1,
    (pr3.trans pr2).trans pr1, (rd3.trans rd2).trans rd1, (f3.trans f2).trans f1⟩⟩
  simp only [cSz, cSt, cSrc, cLl, cRr, cN, cP, cT, S.C]
  split <;> simp

/-- **The group phase leaves the chunk fields, the queue and the top structure alone.** -/
theorem xgroup_frame {L : List Nat} {c : Nat} (s₀ : Core) :
    XGroup (CFrame s₀) (CFrame s₀) L c := by
  refine ⟨fun δ p => ⟨?_, ?_, ?_⟩, ?_⟩
  · intro t _ _ _ _ _ _ _ hX; exact hX.trans (cframe_moveL t p)
  · intro t _ _ _ _ _ _ _ hX; exact hX.trans (cframe_moveR t p)
  · intro t _ _ _ _ _ _ _ _ _ _ _ _ _ hX; exact hX.trans (cframe_remove t p)
  · intro t A _ g labL labR hI _ _ hg _ _ _ _ hX; exact hX.trans (cframe_split hI hg)

end OM.Proof
