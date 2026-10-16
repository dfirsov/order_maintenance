import OM.Impl.GlueCore

/-!
# M6: the capacities (step 4 of the glue)

The Level M side conditions (`TopCaps`, `GCaps`, `InsCaps`, `PQCaps`, ...) bound the record
counts of a core. Level F bounds the element and chunk counts already (`E.size = count + 1`,
`CountInv.chunks`). Here are the bounds Level F lacks:
* nodes: a potential `nodes.size + topMu ≤ nb0 + topJ · C.size`. A drain start adds 2 nodes and
  lowers the job measure by `s ≥ 3`; no other step adds nodes; a split start adds 2 chunks and a
  job of measure at most `topJ`.
-/

namespace OM.Proof

open OM.Model

set_option linter.deprecated false

/-! ### Steps that keep the node count -/

/-- The node count is unchanged. -/
def NS (s s' : Core) : Prop := s'.nodes.size = s.nodes.size

instance : IsPre NS := ⟨fun _ => rfl, fun _ _ _ h1 h2 => h2.trans h1⟩

theorem ns_modN (i : Nat) (f : Node → Node) : Pres NS (modN i f) := by
  unfold modN; pres; intro s; simp [NS]
theorem ns_setPath (c : Nat) (p : Array Nat) : Pres NS (setPath c p) := by
  unfold setPath; pres; intro s; rfl
theorem ns_setPathAt (c j v : Nat) : Pres NS (setPathAt c j v) := by
  unfold setPathAt; pres; intro s; rfl
theorem ns_setLpar (c v : Nat) : Pres NS (setLpar c v) := by
  unfold setLpar; pres; intro s; rfl
theorem ns_inTablesOf (e h : Nat) : Pres NS (inTablesOf e h) := by
  unfold inTablesOf; pres [pres_getN _]
theorem ns_setInTables (e h : Nat) (l : List Nat) : Pres NS (setInTables e h l) := by
  unfold setInTables; pres [ns_modN _ _]; intro s; rfl
theorem ns_guardTag (c t : Nat) : Pres NS (guardTag c t) := by
  unfold guardTag; pres [pres_getC _]
theorem ns_guardedSetTag (c t : Nat) : Pres NS (guardedSetTag c t) := by
  unfold guardedSetTag modC; pres [ns_guardTag _ _]; intro s; rfl
theorem ns_dropTable (h v e : Nat) : Pres NS (dropTable h v e) := by
  unfold dropTable; pres [ns_inTablesOf _ _, ns_setInTables _ _ _]
theorem ns_dropEntry (v T : Nat) : Pres NS (dropEntry v T) := by
  unfold dropEntry; pres [pres_getN _, ns_modN _ _]
theorem ns_release (v t : Nat) : Pres NS (release v t) := by
  unfold release; pres [pres_getN _, ns_modN _ _]
theorem ns_finishDrain (v : Nat) : Pres NS (finishDrain v) := by
  unfold finishDrain
  pres [pres_getN _, ns_dropTable _ _ _, ns_dropEntry _ _, ns_release _ _, ns_modN _ _]
theorem ns_drainStep (v : Nat) : Pres NS (drainStep v) := by
  unfold drainStep
  pres [pres_getP, pres_getN _, ns_finishDrain _, pres_getPath _, pres_getC _,
    ns_guardedSetTag _ _, ns_setPathAt _ _ _, ns_modN _ _, pres_belowOf _ _]
theorem ns_fundLoop (j : Job) (v up src k : Nat) : Pres NS (fundLoop j v up src k) := by
  unfold fundLoop; pres [pres_getP, ns_drainStep _]
theorem ns_afterDrain (j : Job) (v up : Nat) : Pres NS (afterDrain j v up) := by
  unfold afterDrain; pres [pres_getN _, ns_fundLoop _ _ _ _ _]

theorem Pres.ok {R : Core → Core → Prop} {α : Type} {m : CM α} (h : Pres R m) {s s' : Core} {a : α}
    (hr : m.run s = .ok a s') : R s s' := by
  have := h s; rw [hr] at this; exact this

/-! ### Top steps keep the preparation state -/

/-- The preparation state is unchanged. -/
def TP (s s' : Core) : Prop := s'.prep = s.prep

instance : IsPre TP := ⟨fun _ => rfl, fun _ _ _ h1 h2 => h2.trans h1⟩

theorem tp_modN (i : Nat) (f : Node → Node) : Pres TP (modN i f) := by
  unfold modN; pres; intro s; rfl
theorem tp_setPath (c : Nat) (p : Array Nat) : Pres TP (setPath c p) := by
  unfold setPath; pres; intro s; rfl
theorem tp_setPathAt (c j v : Nat) : Pres TP (setPathAt c j v) := by
  unfold setPathAt; pres; intro s; rfl
theorem tp_setLpar (c v : Nat) : Pres TP (setLpar c v) := by
  unfold setLpar; pres; intro s; rfl
theorem tp_inTablesOf (e h : Nat) : Pres TP (inTablesOf e h) := by
  unfold inTablesOf; pres [pres_getN _]
theorem tp_setInTables (e h : Nat) (l : List Nat) : Pres TP (setInTables e h l) := by
  unfold setInTables; pres [tp_modN _ _]; intro s; rfl
theorem tp_newNode (h : Nat) : Pres TP (newNode h) := by
  unfold newNode; pres; intro s; rfl
theorem tp_guardTag (c t : Nat) : Pres TP (guardTag c t) := by
  unfold guardTag; pres [pres_getC _]
theorem tp_guardedSetTag (c t : Nat) : Pres TP (guardedSetTag c t) := by
  unfold guardedSetTag modC; pres [tp_guardTag _ _]; intro s; rfl
theorem tp_roomNextTo (t e : Nat) (b : Bool) : Pres TP (roomNextTo t e b) := by
  unfold roomNextTo; pres [pres_getP, pres_getN _]
theorem tp_tableInsert (t e new : Nat) (b : Bool) (lab : Nat) :
    Pres TP (tableInsert t e new b lab) := by
  unfold tableInsert; pres [pres_getN _, tp_modN _ _]
theorem tp_sameDrain (a b : Nat) : Pres TP (sameDrain a b) := by
  unfold sameDrain; pres
theorem tp_addTable (h t e : Nat) : Pres TP (addTable h t e) := by
  unfold addTable; pres [tp_inTablesOf _ _, tp_setInTables _ _ _]
theorem tp_insertAroundIn (v v1 v2 : Nat) (q : Nat × Nat × Nat) :
    Pres TP (insertAroundIn v v1 v2 q) := by
  unfold insertAroundIn; pres [tp_tableInsert _ _ _ _ _]
theorem tp_setParent (h w e : Nat) : Pres TP (setParent h w e) := by
  unfold setParent; pres [tp_setLpar _ _, tp_modN _ _]
theorem tp_startDrain (v : Nat) : Pres TP (startDrain v) := by
  unfold startDrain
  pres [pres_getP, pres_getN _, tp_roomNextTo _ _ _, tp_newNode _, tp_insertAroundIn _ _ _ _,
    tp_modN _ _, tp_addTable _ _ _, tp_setParent _ _ _]
theorem tp_dropTable (h v e : Nat) : Pres TP (dropTable h v e) := by
  unfold dropTable; pres [tp_inTablesOf _ _, tp_setInTables _ _ _]
theorem tp_dropEntry (v T : Nat) : Pres TP (dropEntry v T) := by
  unfold dropEntry; pres [pres_getN _, tp_modN _ _]
theorem tp_release (v t : Nat) : Pres TP (release v t) := by
  unfold release; pres [pres_getN _, tp_modN _ _]
theorem tp_finishDrain (v : Nat) : Pres TP (finishDrain v) := by
  unfold finishDrain
  pres [pres_getN _, tp_dropTable _ _ _, tp_dropEntry _ _, tp_release _ _, tp_modN _ _]
theorem tp_drainStep (v : Nat) : Pres TP (drainStep v) := by
  unfold drainStep
  pres [pres_getP, pres_getN _, tp_finishDrain _, pres_getPath _, pres_getC _,
    tp_guardedSetTag _ _, tp_setPathAt _ _ _, tp_modN _ _, pres_belowOf _ _]
theorem tp_fundLoop (j : Job) (v up src k : Nat) : Pres TP (fundLoop j v up src k) := by
  unfold fundLoop; pres [pres_getP, tp_drainStep _]
theorem tp_afterDrain (j : Job) (v up : Nat) : Pres TP (afterDrain j v up) := by
  unfold afterDrain; pres [pres_getN _, tp_fundLoop _ _ _ _ _]
theorem tp_walkBody (j : Job) (v : Nat) : Pres TP (walkBody j v) := by
  unfold walkBody; pres [pres_getP, pres_getN _, tp_modN _ _, tp_startDrain _, tp_afterDrain _ _ _]
theorem tp_jobStep (j : Job) : Pres TP (jobStep j) := by
  unfold jobStep
  pres [pres_getP, pres_getPath _, tp_setPathAt _ _ _, pres_getN _, tp_modN _ _,
    pres_getLpar _, tp_walkBody _ _, tp_afterDrain _ _ _, tp_fundLoop _ _ _ _ _]
theorem tp_insertAroundPrep (x : Nat) : Pres TP (insertAroundPrep x) := by
  unfold insertAroundPrep
  pres [pres_getPath _, tp_roomNextTo _ _ _, pres_getN _, pres_getC _, pres_getLpar _]
theorem tp_insertAroundFinish (x y z : Nat) (tabs ly lz : List Nat) (lp : Nat) :
    Pres TP (insertAroundFinish x y z tabs ly lz lp) := by
  unfold insertAroundFinish joinChunk
  pres [pres_getP, tp_insertAroundIn _ _ _ _, tp_setPath _ _, tp_setInTables _ _ _,
    tp_setLpar _ _, tp_modN _ _]
theorem tp_insertAround (x y z : Nat) : Pres TP (insertAround x y z) := by
  unfold insertAround
  pres [tp_insertAroundPrep _, tp_guardedSetTag _ _, tp_insertAroundFinish _ _ _ _ _ _ _]


/-! ### `insertAround` keeps the node count -/

theorem ns_roomNextTo (t e : Nat) (b : Bool) : Pres NS (roomNextTo t e b) := by
  unfold roomNextTo; pres [pres_getP, pres_getN _]
theorem ns_tableInsert (t e new : Nat) (b : Bool) (lab : Nat) :
    Pres NS (tableInsert t e new b lab) := by
  unfold tableInsert; pres [pres_getN _, ns_modN _ _]
theorem ns_insertAroundIn (v v1 v2 : Nat) (q : Nat × Nat × Nat) :
    Pres NS (insertAroundIn v v1 v2 q) := by
  unfold insertAroundIn; pres [ns_tableInsert _ _ _ _ _]
theorem ns_insertAroundPrep (x : Nat) : Pres NS (insertAroundPrep x) := by
  unfold insertAroundPrep
  pres [pres_getPath _, ns_roomNextTo _ _ _, pres_getN _, pres_getC _, pres_getLpar _]
theorem ns_insertAroundFinish (x y z : Nat) (tabs ly lz : List Nat) (lp : Nat) :
    Pres NS (insertAroundFinish x y z tabs ly lz lp) := by
  unfold insertAroundFinish joinChunk
  pres [pres_getP, ns_insertAroundIn _ _ _ _, ns_setPath _ _, ns_setInTables _ _ _,
    ns_setLpar _ _, ns_modN _ _]
theorem ns_insertAround (x y z : Nat) : Pres NS (insertAround x y z) := by
  unfold insertAround
  pres [ns_insertAroundPrep _, ns_guardedSetTag _ _, ns_insertAroundFinish _ _ _ _ _ _ _]

/-! ### The node count across a job step -/

open OM.Proof.Top in
/-- **A walk step adds no nodes, or starts a drain**: 2 nodes, and the job measure drops by at
least 2. -/
theorem walk_nodes {s : Core} {cl : List Nat} {ord : Nat → List Nat} {dr n0 : Nat → Nat} {j : Job} {v : Nat}
    (hpc : j.pc = .walk (some v)) (hTP : TopParams s.P) (hI : InvJ (ts s) cl ord dr n0 (some j))
    {r : Option Job} {t1 : Core} (h : (walkBody j v).run s = .ok r t1) :
    t1.nodes.size = s.nodes.size ∨
      (t1.nodes.size = s.nodes.size + 2 ∧ (∃ j', r = some j') ∧
        ∀ j', r = some j' → jobLeft (ts t1) j' + 2 ≤ jobLeft (ts s) j) := by
  by_cases hv0 : v = NIL
  · subst hv0; rw [run_walkBody_nil] at h; injection h with _ e; subst e; exact Or.inl rfl
  by_cases hd : (nd (ts s) v).livePar ≠ NIL ∧ (nd (ts s) v).draining = false ∧
      (nd (ts s) v).overflowOf = NIL ∧ Wd s.P (ht (ts s) v) < (nd (ts s) v).weight + 2
  · obtain ⟨h1, h2, h3, h4⟩ := hd
    obtain ⟨side, hside, hlook⟩ := sp_side hpc hv0 hI h1 hTP h3 h4
    have hrun := sr_run hpc hv0 hI h1 hTP h3 h4 hside hlook
    have H := sr_hyps hpc hv0 hI h1 hTP h3 h4 hlook
    have hR := sr_topRel hpc hv0 hI h1 hTP h3 h4 hside hlook
    have hht : ht (ts (sdS (wiC s v) v side)) v = ht (ts s) v := by
      show (nd (ts (sdS (wiC s v) v side)) v).height = _
      rw [H.height v, if_neg (by have := H.hv; omega)]
    have hP : (ts (sdS (wiC s v) v side)).P = s.P := hR.rest.1
    have hsz := H.size
    rw [run_walkBody_drain j s v hv0 h1 h2 h3 h4 hrun] at h
    generalize sdS (wiC s v) v side = S at h hht hP hsz
    obtain ⟨hr, ht⟩ := EStateM.Result.ok.inj h
    subst hr; subst ht
    right
    refine ⟨hsz, ⟨_, rfl⟩, fun j' hj' => ?_⟩
    cases hj'
    have hHt := (sd_ht hpc hv0 hI h1).2
    have hs3 := hTP.s3
    simp only [jobLeft, hpc, if_neg hv0, hht, hP, show (ts s).P = s.P from rfl]
    unfold walkLeft
    have e : s.P.H + 1 - ht (ts s) v = (s.P.H + 1 - (ht (ts s) v + 1)) + 1 := by
      have : (ts s).P.H = s.P.H := rfl; omega
    rw [e, Nat.add_mul, one_mul]; omega
  · left
    rw [run_walkBody_noDrain j s v hv0 hd] at h
    have := (ns_afterDrain _ _ _).ok h
    rw [this]; simp [wiC]

open OM.Proof.Top in
/-- **The node count across a job step**: `nodes.size + topMu` does not grow. -/
theorem node_step {s : Core} {job : Job} (hT : TopInv s) (hres : s.resJob = some job) {r : Option Job}
    {t1 : Core} (h : (jobStep job).run s = .ok r t1) :
    t1.nodes.size + topMu { t1 with resJob := r } ≤ s.nodes.size + topMu s := by
  obtain ⟨r', s', hrun, -, hμ⟩ := top_step sdOK hT hres
  rw [h] at hrun; injection hrun with e1 e2; subst e1; subst e2
  have hμs : topMu s = jobLeft (ts s) job := by simp only [topMu, hres]
  obtain ⟨hTP, cl, ord, dr, n0, hL, hC, hI⟩ := hT
  rw [hres] at hI
  have hcase : t1.nodes.size = s.nodes.size ∨ (t1.nodes.size = s.nodes.size + 2 ∧ (∃ j', r = some j') ∧
      ∀ j', r = some j' → jobLeft (ts t1) j' + 2 ≤ jobLeft (ts s) job) := by
    cases hpc : job.pc with
    | copy l =>
      rw [jobStep_copy hpc] at h
      obtain ⟨-, e⟩ := EStateM.Result.ok.inj h; subst e
      left; unfold copyC; dsimp only; split_ifs <;> simp
    | walk ov =>
      have hfin : finS (ts s) (some job) = ts s := by simp only [finS, hpc]
      rw [hfin] at hI
      cases ov with
      | none =>
        obtain ⟨hI', hl, hh⟩ := walkNone_inv hpc hI
        have h' : (walkBody { job with pc := .walk (some (lpr (ts s) job.y)) } (lpr (ts s) job.y)).run s =
            .ok r t1 := by rw [OM.Impl.jobStep_walkNone hpc] at h; exact h
        have e : jobLeft (ts s) { job with pc := .walk (some (lpr (ts s) job.y)) } = jobLeft (ts s) job := by
          simp only [jobLeft, hpc, if_neg hl.1.1, hh]
        rw [← e]
        exact walk_nodes rfl hTP hI' h'
      | some v =>
        rw [OM.Impl.jobStep_walkSome hpc] at h
        exact walk_nodes hpc hTP hI h
    | afterDrain v up =>
      rw [OM.Impl.jobStep_after hpc] at h
      exact Or.inl ((ns_afterDrain _ _ _).ok h)
    | fund v up src k =>
      rw [OM.Impl.jobStep_fund hpc] at h
      exact Or.inl ((ns_fundLoop _ _ _ _ _).ok h)
  rw [hμs]
  cases r with
  | none =>
    have : topMu { t1 with resJob := none } = 0 := rfl
    rw [this]
    rcases hcase with e | ⟨-, ⟨j', hj'⟩, -⟩
    · omega
    · cases hj'
  | some j' =>
    have : topMu { t1 with resJob := some j' } = jobLeft (ts t1) j' := rfl
    rw [this]
    rcases hcase with e | ⟨e, -, hle⟩
    · have h2 : jobLeft (ts t1) j' < jobLeft (ts s) job := (hμ j' rfl).2.trans_eq hμs
      omega
    · have := hle j' rfl; omega

/-- **A split start** keeps the node count and the preparation state, and adds two chunks. -/
theorem split_frame {t t2 : Core} {x : Nat} (h : (splitChunkStart x).run t = .ok () t2) :
    t2.nodes.size = t.nodes.size ∧ t2.C.size = t.C.size + 2 ∧ t2.prep = t.prep := by
  unfold splitChunkStart at h
  simp only [run_get_bind, run_require_bind] at h
  split at h
  · simp only [run_newChunk_bind, run_modify_bind, Array.size_push] at h
    have hps : ({ ({ t with C := t.C.push {} } : Core) with C := (t.C.push {}).push {} } : Core) =
        push2 t := rfl
    rw [hps, run_bind] at h
    rcases hj : (insertAround x t.C.size (t.C.size + 1)).run
        (linkChunkPair (push2 t) x t.C.size (t.C.size + 1)) with ⟨job, s2⟩ | ⟨e, s2⟩
    · rw [hj] at h
      have hN := (ns_insertAround _ _ _).ok hj
      have hP := (tp_insertAround _ _ _).ok hj
      have hR := (top_insertAround _ _ _).ok hj
      simp only [markSplit_run] at h
      obtain ⟨-, e⟩ := EStateM.Result.ok.inj h; subst e
      have hl := (linkChunkPair_rest (s := push2 t) (x := x) (y := t.C.size) (z := t.C.size + 1)).2.2.2.2.2.2.1
      refine ⟨hN, ?_, hP⟩
      simp only [markState, Array.size_modify]
      rw [hR.Csize, hl]; simp [push2]
    · rw [hj] at h; simp at h
  · simp [OM.Model.guard] at h

/-! ### Top steps without path writes keep the paths and the chunk count -/

/-- The paths and the chunk count are unchanged. -/
def PCS (s s' : Core) : Prop := s'.path = s.path ∧ s'.C.size = s.C.size

instance : IsPre PCS := ⟨fun _ => ⟨rfl, rfl⟩, fun _ _ _ h1 h2 => ⟨h2.1.trans h1.1, h2.2.trans h1.2⟩⟩

theorem pcs_modN (i : Nat) (f : Node → Node) : Pres PCS (modN i f) := by
  unfold modN; pres; intro s; simp [PCS]
theorem pcs_setLpar (c v : Nat) : Pres PCS (setLpar c v) := by
  unfold setLpar; pres; intro s; simp [PCS]
theorem pcs_inTablesOf (e h : Nat) : Pres PCS (inTablesOf e h) := by
  unfold inTablesOf; pres [pres_getN _]
theorem pcs_setInTables (e h : Nat) (l : List Nat) : Pres PCS (setInTables e h l) := by
  unfold setInTables; pres [pcs_modN _ _]; intro s; simp [PCS]
theorem pcs_newNode (h : Nat) : Pres PCS (newNode h) := by
  unfold newNode; pres; intro s; simp [PCS]
theorem pcs_guardTag (c t : Nat) : Pres PCS (guardTag c t) := by
  unfold guardTag; pres [pres_getC _]
theorem pcs_guardedSetTag (c t : Nat) : Pres PCS (guardedSetTag c t) := by
  unfold guardedSetTag modC; pres [pcs_guardTag _ _]; intro s; simp [PCS]
theorem pcs_roomNextTo (t e : Nat) (b : Bool) : Pres PCS (roomNextTo t e b) := by
  unfold roomNextTo; pres [pres_getP, pres_getN _]
theorem pcs_tableInsert (t e new : Nat) (b : Bool) (lab : Nat) :
    Pres PCS (tableInsert t e new b lab) := by
  unfold tableInsert; pres [pres_getN _, pcs_modN _ _]
theorem pcs_sameDrain (a b : Nat) : Pres PCS (sameDrain a b) := by
  unfold sameDrain; pres
theorem pcs_addTable (h t e : Nat) : Pres PCS (addTable h t e) := by
  unfold addTable; pres [pcs_inTablesOf _ _, pcs_setInTables _ _ _]
theorem pcs_insertAroundIn (v v1 v2 : Nat) (q : Nat × Nat × Nat) :
    Pres PCS (insertAroundIn v v1 v2 q) := by
  unfold insertAroundIn; pres [pcs_tableInsert _ _ _ _ _]
theorem pcs_setParent (h w e : Nat) : Pres PCS (setParent h w e) := by
  unfold setParent; pres [pcs_setLpar _ _, pcs_modN _ _]
theorem pcs_startDrain (v : Nat) : Pres PCS (startDrain v) := by
  unfold startDrain
  pres [pres_getP, pres_getN _, pcs_roomNextTo _ _ _, pcs_newNode _, pcs_insertAroundIn _ _ _ _,
    pcs_modN _ _, pcs_addTable _ _ _, pcs_setParent _ _ _]
theorem pcs_dropTable (h v e : Nat) : Pres PCS (dropTable h v e) := by
  unfold dropTable; pres [pcs_inTablesOf _ _, pcs_setInTables _ _ _]
theorem pcs_dropEntry (v T : Nat) : Pres PCS (dropEntry v T) := by
  unfold dropEntry; pres [pres_getN _, pcs_modN _ _]
theorem pcs_release (v t : Nat) : Pres PCS (release v t) := by
  unfold release; pres [pres_getN _, pcs_modN _ _]
theorem pcs_finishDrain (v : Nat) : Pres PCS (finishDrain v) := by
  unfold finishDrain
  pres [pres_getN _, pcs_dropTable _ _ _, pcs_dropEntry _ _, pcs_release _ _, pcs_modN _ _]

/-! ### Path rows beyond the chunks stay zero -/

open OM.Proof.Top

/-- The path rows of chunks not yet allocated read zero. -/
def PZ (s : Core) : Prop := ∀ c, s.C.size ≤ c → ∀ j, (s.path.getX c).getX j = 0

theorem PZ.of_frame {s s' : Core} (h : PZ s) (hC : s.C.size ≤ s'.C.size)
    (hp : ∀ c, s.C.size ≤ c → s'.path.getX c = s.path.getX c) : PZ s' := fun c hc j => by
  rw [hp c (by omega)]; exact h c (by omega) j

theorem PZ.setX {s s' : Core} (h : PZ s) (hC : s'.C.size = s.C.size) {y : Nat} {row : Array Nat}
    (hy : y < s.C.size) (hp : s'.path = s.path.setX y row) : PZ s' :=
  h.of_frame hC.ge fun c hc => by rw [hp, Array.getX_setX, if_neg (by omega)]

theorem fd_frame {v : Nat} : ∀ (l : List Nat) (hh : Nat) (s : Core),
    (l.foldl (dropTableS v hh) s).path = s.path ∧ (l.foldl (dropTableS v hh) s).C = s.C
  | [], _, _ => ⟨rfl, rfl⟩
  | e :: l, hh, s => by
    simp only [List.foldl_cons]
    obtain ⟨a, b⟩ := fd_frame l hh (dropTableS v hh s e)
    rw [a, b]; unfold dropTableS; split_ifs <;> exact ⟨rfl, rfl⟩

theorem fe_frame {v : Nat} : ∀ (l : List Nat) (s : Core),
    (l.foldl (dropEntryS v) s).path = s.path ∧ (l.foldl (dropEntryS v) s).C = s.C
  | [], _ => ⟨rfl, rfl⟩
  | e :: l, s => by
    simp only [List.foldl_cons]
    obtain ⟨a, b⟩ := fe_frame l (dropEntryS v s e)
    rw [a, b]; exact ⟨rfl, rfl⟩

theorem releaseS_frame (v t : Nat) (s : Core) : (releaseS v s t).path = s.path ∧ (releaseS v s t).C = s.C := by
  unfold releaseS; split_ifs <;> exact ⟨rfl, rfl⟩

open OM.Proof.Top in
theorem fd4_frame (v : Nat) (s : Core) : (fd4 v s).path = s.path ∧ (fd4 v s).C = s.C := by
  unfold fd4 fd2 fd1
  obtain ⟨a1, b1⟩ := releaseS_frame v (s.nodes.getX v).t2
    (releaseS v ((s.nodes.getX v).inTables.foldl (dropEntryS v)
      ((s.nodes.getX v).order.foldl (dropTableS v ((s.nodes.getX v).height - 1)) s)) (s.nodes.getX v).t1)
  obtain ⟨a2, b2⟩ := releaseS_frame v (s.nodes.getX v).t1 ((s.nodes.getX v).inTables.foldl (dropEntryS v)
      ((s.nodes.getX v).order.foldl (dropTableS v ((s.nodes.getX v).height - 1)) s))
  obtain ⟨a3, b3⟩ := fe_frame (v := v) (s.nodes.getX v).inTables
      ((s.nodes.getX v).order.foldl (dropTableS v ((s.nodes.getX v).height - 1)) s)
  obtain ⟨a4, b4⟩ := fd_frame (v := v) (s.nodes.getX v).order ((s.nodes.getX v).height - 1) s
  exact ⟨a1.trans (a2.trans (a3.trans a4)), b1.trans (b2.trans (b3.trans b4))⟩

theorem fdS_frame (v : Nat) (s : Core) : (fdS v s).path = s.path ∧ (fdS v s).C = s.C := by
  unfold fdS; exact fd4_frame v s

open OM.Proof.Top in
theorem dsS_frame (s : Core) (v tag : Nat) :
    (dsS s v tag).path = s.path.setX (dsY s v) ((s.path.getX (dsY s v)).setX (s.nodes.getX v).height (dsT s v)) ∧
    (dsS s v tag).C.size = s.C.size := by
  unfold dsS; dsimp only; split_ifs <;> simp

open OM.Proof.Top in
/-- **A sweep step keeps the zero rows** and the chunk count. -/
theorem drain_pz {s : Core} {cl : List Nat} {ord : Nat → List Nat} (S : Shape (ts s) cl ord) {v : Nat}
    (hg : ghostN (ts s) v) (hcl : CLok s cl) {b : Bool} {t : Core} (h : (drainStep v).run s = .ok b t) :
    t.C.size = s.C.size ∧ (PZ s → PZ t) := by
  by_cases hemp : rng (ts s) cl v = []
  · obtain ⟨hal, hf, hnd, hT, -⟩ := S.drain_finish_hyps hg hemp
    rw [drainStep_finish hal hf hnd hT] at h
    obtain ⟨-, e⟩ := EStateM.Result.ok.inj h; subst e
    obtain ⟨a, b⟩ := fdS_frame v s
    exact ⟨by rw [b], fun hz => hz.of_frame (by rw [b]) fun c _ => by rw [a]⟩
  · obtain ⟨hal, hf, hside, hsz, hpt, htb, hpv, hvb, hold, hok, -, -, -, -, -, -, -, hycl, -⟩ :=
      S.drain_move_hyps hg hemp hcl.1
    rw [drainStep_move hal hf hside hsz hpt htb hpv hvb hold hok] at h
    obtain ⟨-, e⟩ := EStateM.Result.ok.inj h; subst e
    obtain ⟨a, b⟩ := dsS_frame s v _
    exact ⟨b, fun hz => hz.setX b ((hcl.2 _).mp hycl).2 a⟩

/-- **The funding loop keeps the zero rows** and the chunk count. -/
theorem fund_pz {s : Core} {cl : List Nat} {ord : Nat → List Nat} {dr n0 : Nat → Nat} {j : Job}
    {v up src k : Nat} (hcl : CLok s cl) (hI : InvJ (ts s) cl ord dr n0 (some { j with pc := .fund v up src k }))
    {r : Option Job} {t : Core} (h : (fundLoop j v up src k).run s = .ok r t) :
    t.C.size = s.C.size ∧ (PZ s → PZ t) := by
  obtain ⟨-, hat⟩ := hI.job _ rfl
  simp only [JobAt] at hat
  obtain ⟨-, -, -, hg, -, -⟩ := hat
  unfold fundLoop at h
  simp only [run_getP_bind] at h
  split at h
  · rw [run_bind] at h
    rcases hd : (drainStep src).run s with ⟨b, t'⟩ | ⟨e, t'⟩
    · rw [hd] at h
      obtain ⟨hC, hz⟩ := drain_pz hI.shape hg hcl hd
      cases b <;> (simp at h; obtain ⟨-, rfl⟩ := h; exact ⟨hC, hz⟩)
    · rw [hd] at h; simp at h
  · simp at h; obtain ⟨-, rfl⟩ := h; exact ⟨rfl, id⟩

/-- **A walk step keeps the zero rows** and the chunk count. -/
theorem walk_pz {s : Core} {cl : List Nat} {ord : Nat → List Nat} {dr n0 : Nat → Nat} {j : Job} {v : Nat}
    (hpc : j.pc = .walk (some v)) (hcl : CLok s cl) (hI : InvJ (ts s) cl ord dr n0 (some j))
    {r : Option Job} {t1 : Core} (h : (walkBody j v).run s = .ok r t1) :
    t1.C.size = s.C.size ∧ (PZ s → PZ t1) := by
  have hW : PCS s (wiC s v) := ⟨rfl, rfl⟩
  by_cases hv0 : v = NIL
  · subst hv0; rw [run_walkBody_nil] at h; injection h with _ e; subst e; exact ⟨rfl, id⟩
  by_cases hd : (nd (ts s) v).livePar ≠ NIL ∧ (nd (ts s) v).draining = false ∧
      (nd (ts s) v).overflowOf = NIL ∧ Wd s.P (ht (ts s) v) < (nd (ts s) v).weight + 2
  · obtain ⟨h1, h2, h3, h4⟩ := hd
    unfold walkBody at h
    simp only [beq_iff_eq, hv0, if_false, run_getP_bind, run_getN_bind, run_modN_bind] at h
    rw [if_pos (by simp only [Bool.and_eq_true, bne_iff_ne, ne_eq, Bool.not_eq_true', beq_iff_eq,
      decide_eq_true_eq]; exact ⟨⟨⟨h1, h2⟩, h3⟩, by unfold Wd ht at h4; exact h4⟩), run_bind] at h
    rcases hs : (startDrain v).run { s with nodes := s.nodes.modify v fun n => { n with weight := n.weight + 2 } }
      with ⟨u, t'⟩ | ⟨e, t'⟩
    · rw [hs] at h; simp at h; obtain ⟨-, rfl⟩ := h
      obtain ⟨a, b⟩ := (pcs_startDrain v).ok hs
      exact ⟨b, fun hz => hz.of_frame b.ge fun c _ => by rw [a]⟩
    · rw [hs] at h; simp at h
  · rw [run_walkBody_noDrain j s v hv0 hd] at h
    have hI' := inv_winc hpc hv0 hI hd
    have hcl' := hcl.topRel (wiC_topRel s v)
    unfold afterDrain at h
    simp only [run_getN_bind] at h
    split at h
    · next hne =>
      have hsrc : ((wiC s v).nodes.getX v).overflowOf = srcOf (ts s) v := by
        show ((s.nodes.modify v _).getX v).overflowOf = _
        rw [Array.getX_modify]; split <;> rfl
      have hn : walkNext (ts s) j v = { j with pc := .fund v (nd (ts s) v).livePar (srcOf (ts s) v) 0 } := by
        simp only [walkNext]; rw [if_neg]; intro e
        rw [hsrc, e] at hne; exact absurd hne (by decide)
      rw [hn] at hI'
      have hlp : ((wiC s v).nodes.getX v).livePar = (nd (ts s) v).livePar := by
        show ((s.nodes.modify v _).getX v).livePar = _
        rw [Array.getX_modify]; split <;> rfl
      rw [hsrc] at h
      obtain ⟨a, b⟩ := fund_pz hcl' hI' h
      exact ⟨a, fun hz => b (hz.of_frame le_rfl fun _ _ => rfl)⟩
    · simp at h; obtain ⟨-, rfl⟩ := h; exact ⟨rfl, fun hz => hz.of_frame le_rfl fun _ _ => rfl⟩

theorem copyC_frame (s : Core) (j : Job) (l : Nat) : (copyC s j l).C.size = s.C.size ∧
    ∀ c, c ≠ j.y → c ≠ j.z → (copyC s j l).path.getX c = s.path.getX c := by
  unfold copyC; dsimp only
  refine ⟨by split_ifs <;> simp, fun c h1 h2 => ?_⟩
  split_ifs <;> simp [Array.getX_setX, h1, h2]

/-- **A job step keeps the zero rows** and the chunk count. -/
theorem path_step {s : Core} {job : Job} (hT : TopInv s) (hres : s.resJob = some job) {r : Option Job}
    {t1 : Core} (h : (jobStep job).run s = .ok r t1) : t1.C.size = s.C.size ∧ (PZ s → PZ t1) := by
  obtain ⟨hTP, cl, ord, dr, n0, hL, hC, hI⟩ := hT
  rw [hres] at hI
  have hcl : CLok s cl := ⟨hL, hC⟩
  cases hpc : job.pc with
  | copy l =>
    rw [jobStep_copy hpc] at h
    obtain ⟨-, e⟩ := EStateM.Result.ok.inj h; subst e
    obtain ⟨-, hy, hz, -, -, -⟩ := OM.Impl.job_chunks hcl (hI.job job rfl)
    obtain ⟨a, b⟩ := copyC_frame s job l
    exact ⟨a, fun hz' => hz'.of_frame a.ge fun c hc => b c (by have := ((hC _).mp hy).2; omega)
      (by have := ((hC _).mp hz).2; omega)⟩
  | walk ov =>
    have hfin : finS (ts s) (some job) = ts s := by simp only [finS, hpc]
    rw [hfin] at hI
    cases ov with
    | none =>
      obtain ⟨hI', -, -⟩ := walkNone_inv hpc hI
      have h' : (walkBody { job with pc := .walk (some (lpr (ts s) job.y)) } (lpr (ts s) job.y)).run s =
          .ok r t1 := by rw [OM.Impl.jobStep_walkNone hpc] at h; exact h
      exact walk_pz rfl hcl hI' h'
    | some v =>
      rw [OM.Impl.jobStep_walkSome hpc] at h
      exact walk_pz hpc hcl hI h
  | afterDrain v up =>
    have hfin : finS (ts s) (some job) = ts s := by simp only [finS, hpc]
    rw [hfin] at hI
    obtain ⟨hrun, -, -⟩ := afterDrain_step hpc hI
    rw [hrun] at h; obtain ⟨-, e⟩ := EStateM.Result.ok.inj h; subst e
    exact ⟨rfl, id⟩
  | fund v up src k =>
    have hfin : finS (ts s) (some job) = ts s := by simp only [finS, hpc]
    rw [hfin, job_eta hpc] at hI
    rw [OM.Impl.jobStep_fund hpc] at h
    exact fund_pz hcl hI h

/-- The path rows from `n` on are unchanged. -/
def PY (n : Nat) (s s' : Core) : Prop := ∀ c, n ≤ c → s'.path.getX c = s.path.getX c

instance (n : Nat) : IsPre (PY n) := ⟨fun _ _ _ => rfl, fun _ _ _ h1 h2 c hc => (h2 c hc).trans (h1 c hc)⟩

section py
variable (n : Nat)
theorem py_modN (i : Nat) (f : Node → Node) : Pres (PY n) (modN i f) := by
  unfold modN; pres; intro s c _; rfl
theorem py_setPath {c : Nat} (p : Array Nat) (hc : c < n) : Pres (PY n) (setPath c p) := by
  unfold setPath; pres; intro s d hd; simp only [Array.getX_setX]; rw [if_neg (by omega)]
theorem py_setLpar (c v : Nat) : Pres (PY n) (setLpar c v) := by
  unfold setLpar; pres; intro s c _; rfl
theorem py_setInTables (e h : Nat) (l : List Nat) : Pres (PY n) (setInTables e h l) := by
  unfold setInTables; pres [py_modN _ _ _]; intro s c _; rfl
theorem py_guardTag (c t : Nat) : Pres (PY n) (guardTag c t) := by
  unfold guardTag; pres [pres_getC _]
theorem py_guardedSetTag (c t : Nat) : Pres (PY n) (guardedSetTag c t) := by
  unfold guardedSetTag modC; pres [py_guardTag _ _ _]; intro s c _; rfl
theorem py_roomNextTo (t e : Nat) (b : Bool) : Pres (PY n) (roomNextTo t e b) := by
  unfold roomNextTo; pres [pres_getP, pres_getN _]
theorem py_tableInsert (t e new : Nat) (b : Bool) (lab : Nat) : Pres (PY n) (tableInsert t e new b lab) := by
  unfold tableInsert; pres [pres_getN _, py_modN _ _ _]
theorem py_insertAroundIn (v v1 v2 : Nat) (q : Nat × Nat × Nat) : Pres (PY n) (insertAroundIn v v1 v2 q) := by
  unfold insertAroundIn; pres [py_tableInsert _ _ _ _ _ _]
theorem py_insertAroundPrep (x : Nat) : Pres (PY n) (insertAroundPrep x) := by
  unfold insertAroundPrep
  pres [pres_getPath _, py_roomNextTo _ _ _ _, pres_getN _, pres_getC _, pres_getLpar _]
theorem py_insertAroundFinish {x y z : Nat} (tabs ly lz : List Nat) (lp : Nat) (hy : y < n) (hz : z < n) :
    Pres (PY n) (insertAroundFinish x y z tabs ly lz lp) := by
  unfold insertAroundFinish joinChunk
  pres [pres_getP, py_insertAroundIn _ _ _ _ _, py_setPath n _ hy, py_setPath n _ hz, py_setInTables _ _ _ _,
    py_setLpar _ _ _, py_modN _ _ _]
theorem py_insertAround {x y z : Nat} (hy : y < n) (hz : z < n) : Pres (PY n) (insertAround x y z) := by
  unfold insertAround
  pres [py_insertAroundPrep _ _, py_guardedSetTag _ _ _, py_insertAroundFinish n _ _ _ _ hy hz]
end py

/-- **A split start keeps the zero rows.** -/
theorem split_pz {t t2 : Core} {x : Nat} (h : (splitChunkStart x).run t = .ok () t2) (hz : PZ t) : PZ t2 := by
  have hC := (split_frame h).2.1
  unfold splitChunkStart at h
  simp only [run_get_bind, run_require_bind] at h
  split at h
  · simp only [run_newChunk_bind, run_modify_bind, Array.size_push] at h
    have hps : ({ ({ t with C := t.C.push {} } : Core) with C := (t.C.push {}).push {} } : Core) =
        push2 t := rfl
    rw [hps, run_bind] at h
    rcases hj : (insertAround x t.C.size (t.C.size + 1)).run
        (linkChunkPair (push2 t) x t.C.size (t.C.size + 1)) with ⟨job, s2⟩ | ⟨e, s2⟩
    · rw [hj] at h
      have hY := (py_insertAround (t.C.size + 2) (x := x) (by omega) (by omega)).ok hj
      simp only [markSplit_run] at h
      obtain ⟨-, e⟩ := EStateM.Result.ok.inj h; subst e
      intro c hc j
      rw [hC] at hc
      have e1 : (markState s2 x t.C.size (t.C.size + 1) job).path = s2.path := rfl
      rw [e1, hY c hc]
      exact hz c (by omega) j
    · rw [hj] at h; simp at h
  · simp [OM.Model.guard] at h

end OM.Proof
