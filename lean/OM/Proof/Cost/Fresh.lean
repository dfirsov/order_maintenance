import OM.Proof.Cost.CoreCost

/-!
# Fresh cores

A fresh core holds the sentinel alone, in one group of one chunk. It satisfies the lower
invariants, and the deferred construction of its top structure (`prepareStep`) touches only the
top structure, the chunk tags and the `ready` flag.
-/

namespace OM.Proof

open OM.Model

set_option linter.deprecated false

/-- `TopRel`, but the `ready` flag may change too. -/
def TopRelR (s s' : Core) : Prop := TopRel s { s' with ready := s.ready }

theorem TopRel.topRelR {s s' : Core} (h : TopRel s s') : TopRelR s s' := by
  unfold TopRelR
  have hr : s'.ready = s.ready := h.rest.2.2.2.2.2.2.2.2
  have : ({ s' with ready := s.ready } : Core) = s' := by rw [← hr]
  rw [this]; exact h

theorem TopRelR.lowSame {s s' : Core} (h : TopRelR s s') : LowSame s s' :=
  ⟨h.E, h.Gs, h.Csize, h.C, h.rest.1, h.rest.2.1, h.rest.2.2.1⟩

theorem TopRelR.pqsame {s s' : Core} (h : TopRelR s s') : PQSame s s' := by
  obtain ⟨p1, p2, p3, p4, p5, p6, p7, p8, -⟩ := h.pq
  exact ⟨p4, p2, p3, p1, p5, p6, p8, p7, by rw [← h.rest.1]⟩

theorem TopRelR.trans {a b c : Core} (h1 : TopRelR a b) (h2 : TopRelR b c) : TopRelR a c := by
  unfold TopRelR at *
  have h1' : TopRel a { b with ready := a.ready } := h1
  have hr : b.ready = b.ready := rfl
  obtain ⟨e2, g2, s2, c2, ⟨q1, q2, q3, q4, q5, q6, q7, q8, q9⟩, ⟨r1, r2, r3, r4, r5, r6, r7, r8, -⟩⟩ := h2
  obtain ⟨e1, g1, s1, c1, ⟨p1, p2, p3, p4, p5, p6, p7, p8, p9⟩, ⟨t1, t2, t3, t4, t5, t6, t7, t8, -⟩⟩ := h1'
  have c1' : ∀ x, b.C.getX x = { a.C.getX x with tag := (b.C.getX x).tag } := c1
  have c2' : ∀ x, c.C.getX x = { b.C.getX x with tag := (c.C.getX x).tag } := c2
  exact ⟨e2.trans e1, g2.trans g1, s2.trans s1, fun x => by
    show c.C.getX x = { a.C.getX x with tag := (c.C.getX x).tag }
    rw [c2' x, c1' x],
    ⟨q1.trans p1, q2.trans p2, q3.trans p3, q4.trans p4, q5.trans p5, q6.trans p6, q7.trans p7,
      q8.trans p8, q9.trans p9⟩, ⟨r1.trans t1, r2.trans t2, r3.trans t3, r4.trans t4, r5.trans t5,
      r6.trans t6, r7.trans t7, r8.trans t8, rfl⟩⟩

theorem top_resetTop : Pres TopRel resetTop := by
  unfold resetTop; pres; intro s; exact TopRel.of_top s _ _ _ _

theorem top_initStep : Pres TopRel initStep := by
  unfold initStep
  pres [pres_getP, top_resetTop, top_setInTables _ _ _, top_newNode _, top_modN _ _,
    top_setLpar _ _, top_setPath _ _]
  all_goals first
    | (intro s; exact TopRel.of_tag s _ _)
    | (intro s; exact ⟨rfl, rfl, rfl, fun _ => rfl, ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩,
        ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩⟩)

end OM.Proof

namespace OM.Proof

open OM.Model

set_option linter.deprecated false

/-- What the deferred construction keeps: everything below the top structure, and the queue. -/
def LowRel (s s' : Core) : Prop := LowSame s s' ∧ PQSame s s'

instance : IsPre LowRel where
  refl s := ⟨⟨rfl, rfl, rfl, fun _ => rfl, rfl, rfl, rfl⟩, PQSame.refl s⟩
  trans _ _ _ h1 h2 := ⟨⟨h2.1.E.trans h1.1.E, h2.1.Gs.trans h1.1.Gs, h2.1.Csize.trans h1.1.Csize,
    fun c => by rw [h2.1.C c, h1.1.C c], h2.1.P.trans h1.1.P, h2.1.count.trans h1.1.count,
    h2.1.head.trans h1.1.head⟩, h1.2.trans h2.2⟩

theorem TopRel.lowRel {s s' : Core} (h : TopRel s s') : LowRel s s' := ⟨h.lowSame, h.pqsame⟩

theorem low_initStep : Pres LowRel initStep := top_initStep.mono fun _ _ h => h.lowRel

theorem low_prepareStep : Pres LowRel prepareStep := by
  unfold prepareStep
  pres [low_initStep]
  intro s; exact ⟨⟨rfl, rfl, rfl, fun _ => rfl, rfl, rfl, rfl⟩, ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩⟩

theorem low_initTop (lazy : Bool) : Pres LowRel (initTop lazy) := by
  unfold initTop
  pres [pres_getP, low_initStep]
  all_goals (intro s; exact ⟨⟨rfl, rfl, rfl, fun _ => rfl, rfl, rfl, rfl⟩,
    ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩⟩)

/-- The lower invariants survive steps that keep `LowRel`, given INV-S. -/
theorem LowInv.lowRel {s s' : Core} {L : List Nat} (h : LowInv s L) (hR : LowRel s s')
    (hI : ∃ A, INV s' A ∧ A.elist = L) : LowInv s' L :=
  h.transfer hR.1 hI (h.pq.qsame hR.2 hR.1.qsame)

/-- **The deferred construction** of a core holding the sentinel alone never fails, and keeps the
lower invariants. -/
theorem prepareStep_low {s : Core} (h : LowInv s initAbs.elist) (hI : INV s initAbs) :
    ∃ b s', prepareStep.run s = .ok b s' ∧ LowInv s' initAbs.elist ∧ INV s' initAbs ∧
      LowRel s s' := by
  obtain ⟨b, s', hr⟩ := noerr_prepareStep s
  have hR : LowRel s s' := by have := low_prepareStep s; rw [hr] at this; exact this
  have hS : SameLinks s s' := by have := pres_prepareStep s; rw [hr] at this; exact this
  have hI' : INV s' initAbs := hI.of_sameLinks' hS (by simp [initAbs])
  exact ⟨b, s', hr, h.lowRel hR ⟨initAbs, hI', rfl⟩, hI', hR⟩

end OM.Proof
