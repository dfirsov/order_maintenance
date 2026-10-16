import OM.Impl.RebuildM
import OM.Proof.Cost.WrapSafe

/-!
# M6: the wrapper's operations as machine code

The Level M side conditions of the cores (`Mc`, `PrepM`) are not part of Level F's invariant; they
are carried alongside it (`MX`). Level F's run supplies the rest of what the core calls need
(`RLSafeF`, `insert_safe`, `delete_safe`).
-/

namespace OM.Impl

open OM.Model OM.Proof OM.Proof.Top
open OM.Machine (Reg Arr State Out exec Stmt Same Expr BinOp UnOp wp)

/-- Level F's safety facts at the proof parameters. -/
abbrev RLSafeP := RLSafeF proofParams TopInv topMu topJ nfP RfP

/-- The Level M side condition of `nxt`: in preparation, or in service with the capacities. -/
def NxtM (om : OM) (n : Core) : Prop :=
  (om.cursorSet = false → PrepM n) ∧ (om.cursorSet = true → Mc (capsOf n.P) n.P n)

/-- **The Level M side conditions of the wrapper state.** -/
def MX (om : OM) : Prop := Mc (capsOf om.cur.P) om.cur.P om.cur ∧ ∀ n, om.nxt = some n → NxtM om n

/-- A copy step keeps the capacities of `nxt`. -/
theorem copy_M {om : OM} {n : Core} (hC : CopyOK om n) (hM : Mc (capsOf n.P) n.P n) {om' : OM} {n' : Core}
    (hcp : copyAtCursor om n = .ok (om', n')) :
    om'.cursorSet = om.cursorSet ∧ om'.cur = om.cur ∧ Mc (capsOf n'.P) n'.P n' := by
  unfold copyAtCursor at hcp
  cases hl : (om.cur.E.getX om.cursor).live with
  | false =>
    simp only [hl, Bool.false_eq_true, if_false, pure, Except.pure] at hcp
    injection hcp with hcp; injection hcp with h1 h2; subst h1; subst h2
    exact ⟨rfl, rfl, hM⟩
  | true =>
    obtain ⟨L, hS, htail, -⟩ := hC.2 hl
    obtain ⟨c', hr, -, -, -, hP', hM'⟩ := hS.insert htail (om.cur.E.getX om.cursor).h
      (fun r => if r = "x" then n.tail else (om.cur.E.getX om.cursor).h) (by simp) (by simp)
    simp only [hl, if_true, bind, Except.bind, runCore, hr] at hcp
    injection hcp with hcp; injection hcp with h1 h2; subst h1; subst h2
    exact ⟨rfl, rfl, by rw [hP']; exact hM'⟩

/-- **Along the rebuild loop**: Level F's safety facts and the side conditions give what the machine
iterations need, and the side conditions hold at the end. -/
theorem loop_M : ∀ f b (om : OM) (n : Core), RLSafeP om n f b → NxtM om n →
    Mc (capsOf om.cur.P) om.cur.P om.cur → RLSafe om n f b ∧ ∀ R, rebuildLoop om n f b = .ok R → MX R := by
  intro f
  induction f with
  | zero =>
    intro b om n _ hN hMc
    refine ⟨trivial, fun R hR => ?_⟩
    cases hR
    exact ⟨hMc, fun n' hn' => by cases hn'; exact hN⟩
  | succ f ih =>
    intro b om n hF hN hMc
    by_cases hb : b = 0
    · subst hb
      refine ⟨rlSafe_zero om n _, fun R hR => ?_⟩
      rw [rebuildLoop_zero] at hR; cases hR
      exact ⟨hMc, fun n' hn' => by cases hn'; exact hN⟩
    have hF' := hF hb
    -- the prepare step
    have hprep : om.cursorSet = false → PrepM n ∧ 1 ≤ n.P.N ∧ om.cur.head < om.cur.E.size ∧
        ∀ r n', prepareStep.run n = .ok r n' → n'.count = n.count ∧
          (r = true → RLSafe { om with cursor := (om.cur.E.getX om.cur.head).next, cursorSet := true } n' f b ∧
            ∀ R, rebuildLoop { om with cursor := (om.cur.E.getX om.cur.head).next, cursorSet := true } n' f b = .ok R →
              MX R) ∧
          (r = false → RLSafe om n' f (b - 1) ∧ ∀ R, rebuildLoop om n' f (b - 1) = .ok R → MX R) := by
      intro hcs
      obtain ⟨hN1, hhd, hst⟩ := hF'.1 hcs
      refine ⟨hN.1 hcs, hN1, hhd, fun r n' hr => ?_⟩
      obtain ⟨hcnt, hT, hFl⟩ := hst r n' hr
      obtain ⟨-, hP', hF2, hT2⟩ := prepAgreeM (hN.1 hcs) hN1 hr (fun _ => 0)
      refine ⟨hcnt, fun hrt => ih _ _ _ (hT hrt) ⟨(fun h => by simp at h), fun _ => by
        rw [hP']; exact (hT2 hrt).1⟩ hMc, fun hrf => ih _ _ _ (hFl hrf) ⟨fun _ => hF2 hrf, fun h => by
        rw [hcs] at h; cases h⟩ hMc⟩
    -- the copy step
    have hcopy : om.cursorSet = true → om.cursor ≠ NIL → CopyOK om n ∧
        ∀ om' n', copyAtCursor om n = .ok (om', n') → Mc (capsOf n'.P) n'.P n' ∧ (om'.cursor ≠ NIL →
          RLSafe om' n' f (b - 1) ∧ ∀ R, rebuildLoop om' n' f (b - 1) = .ok R → MX R) := by
      intro hcs hc
      obtain ⟨hlt, hlive, hnext⟩ := hF'.2 hcs hc
      have hCO : CopyOK om n := ⟨hlt, fun hl => by
        obtain ⟨L, hok, hroom, htail, hh⟩ := hlive hl
        exact ⟨L, ⟨hok, hroom, hN.2 hcs⟩, htail, hh⟩⟩
      refine ⟨hCO, fun om' n' hcp => ?_⟩
      obtain ⟨e1, e2, hM'⟩ := copy_M hCO (hN.2 hcs) hcp
      refine ⟨hM', fun hc' => ih _ _ _ (hnext om' n' hcp hc') ⟨(fun h => by rw [e1, hcs] at h; cases h),
        fun _ => hM'⟩ (by rw [e2]; exact hMc)⟩
    refine ⟨fun _ => ⟨fun hcs => ?_, fun hcs hc => ?_⟩, fun R hR => ?_⟩
    · obtain ⟨h1, h2, h3, h4⟩ := hprep hcs
      exact ⟨h1, h2, h3, fun r n' hr => ⟨(h4 r n' hr).1, fun hrt => ((h4 r n' hr).2.1 hrt).1,
        fun hrf => ((h4 r n' hr).2.2 hrf).1⟩⟩
    · obtain ⟨h1, h2⟩ := hcopy hcs hc
      exact ⟨h1, fun om' n' hcp hc' => ((h2 om' n' hcp).2 hc').1⟩
    · unfold rebuildLoop at hR
      rw [if_neg hb] at hR
      cases hcs : om.cursorSet with
      | false =>
        rw [if_pos (by simp [hcs])] at hR
        obtain ⟨-, -, -, h4⟩ := hprep hcs
        cases hpr : prepareStep.run n with
        | error e s' => simp [runCore, hpr, bind, Except.bind] at hR
        | ok r n' =>
          have hrc : runCore n prepareStep = .ok (r, n') := by simp [runCore, hpr]
          simp only [bind, Except.bind, hrc] at hR
          cases r with
          | true => simp only [if_true] at hR; exact ((h4 true n' hpr).2.1 rfl).2 R hR
          | false => simp only [Bool.false_eq_true, if_false] at hR; exact ((h4 false n' hpr).2.2 rfl).2 R hR
      | true =>
        rw [if_neg (by simp [hcs])] at hR
        by_cases hc : om.cursor = NIL
        · rw [if_pos hc] at hR
          injection hR with hR; subst hR
          exact ⟨hN.2 hcs, fun n' hn' => by cases hn'⟩
        · rw [if_neg hc] at hR
          obtain ⟨-, h2⟩ := hcopy hcs hc
          cases hcp : copyAtCursor om n with
          | error e => simp [hcp, bind, Except.bind] at hR
          | ok r =>
            obtain ⟨om', n'⟩ := r
            simp only [bind, Except.bind, hcp] at hR
            by_cases hc' : om'.cursor = NIL
            · rw [if_pos hc'] at hR
              injection hR with hR; subst hR
              exact ⟨(h2 om' n' hcp).1, fun n'' hn'' => by cases hn''⟩
            · rw [if_neg hc'] at hR
              exact ((h2 om' n' hcp).2 hc').2 R hR

/-! ### The rebuild step -/

/-- The rebuild's share of an operation: start a rebuild, or run the loop. -/
def rebuildC (p : Nat) : Stmt :=
  .ite (.bin .eq (.load (wa 1) (.lit 0)) (.lit 0)) (startC p) (loopC p)

/-- The cost bound of the rebuild step. -/
def rebB (KB : Nat) : Nat := 3600 + (KB + 1) * (1 + iterB)

/-- The locals the rebuild step may change. -/
def RbLoc (x : Reg) : Prop := StLoc x ∧ ItLoc x ∧ x ≠ "it"

theorem pp_topPP (N : Nat) : topPP (proofParams N) := pp_proof N

/-- **The rebuild step**: the machine ends holding Level F's result (in one slot or the other),
which satisfies the side conditions. -/
theorem rebuildW_ok {om : OM} {m : State} {p : Nat} (h : WEnc om m p) (hX : MX om) (hkb : 1 ≤ om.KB)
    (hF : ∀ n, om.nxt = some n → RLSafeP { om with nxt := none } n (om.KB + 1) om.KB)
    {R : OM} (hr : om.rebuildStep proofParams = .ok R) :
    MX R ∧ wp (rebuildC p) (fun m' k => (WEnc R m' p ∨ WEnc R m' (1 - p)) ∧
      (∀ x, RbLoc x → m'.loc x = m.loc x) ∧ k ≤ rebB om.KB) m := by
  cases hn : om.nxt with
  | none =>
    have hR : R = om ∨ R = startOM om (prepStart (proofParams om.nextCapacity) false) := by
      unfold OM.rebuildStep at hr; rw [hn] at hr
      simp only at hr
      split at hr
      · simp only [newCore_true, bind, Except.bind, pure, Except.pure] at hr
        injection hr with hr; exact Or.inr hr.symm
      · injection hr with hr; exact Or.inl hr.symm
    refine ⟨?_, ?_⟩
    · rcases hR with rfl | rfl
      · exact hX
      · exact ⟨hX.1, fun n hn' => by
          cases hn'
          exact ⟨fun _ => prepM_start _ (pp_topPP _), fun h => by simp [startOM] at h⟩⟩
    · unfold rebuildC
      refine wp_ite_g 1 (by simp [Expr.eval, BinOp.eval, h.scap 1 (by decide), h.nxtOn, hn, b2n])
        (fun s1 hl1 hm1 hc1 => ?_)
      simp only [ne_eq, one_ne_zero, not_false_eq_true, if_true]
      refine OM.Machine.wp_mono (fun s2 k2 ⟨h2, hl2, hk2⟩ => ⟨Or.inl h2, fun x hx => ?_, ?_⟩)
        (startW_ok (h.congr hm1 hc1) hn hkb hr)
      · rw [hl2 x hx.1, hl1]
      · unfold rebB; simp only [Expr.cost] at hk2 ⊢; omega
  | some n0 =>
    have hr' : rebuildLoop { om with nxt := none } n0 (om.KB + 1) om.KB = .ok R := by
      unfold OM.rebuildStep at hr; rw [hn] at hr; exact hr
    obtain ⟨hS, hXR⟩ := loop_M _ _ _ _ (hF n0 hn) (hX.2 n0 hn) hX.1
    refine ⟨hXR R hr', ?_⟩
    have hom : ({ ({ om with nxt := none } : OM) with nxt := some n0 } : OM) = om := by
      cases om; simp only at hn; subst hn; rfl
    unfold rebuildC
    refine wp_ite_g 0 (by simp [Expr.eval, BinOp.eval, h.scap 1 (by decide), h.nxtOn, hn, b2n])
      (fun s1 hl1 hm1 hc1 => ?_)
    simp only [ne_eq, not_true_eq_false, if_false]
    have h1 : WEnc ({ ({ om with nxt := none } : OM) with nxt := some n0 } : OM) s1 p := by
      rw [hom]; exact h.congr hm1 hc1
    refine OM.Machine.wp_mono (fun s2 k2 ⟨h2, hl2, hk2⟩ => ⟨h2, fun x hx => ?_, ?_⟩) (loopW_ok h1 hr' hS)
    · rw [hl2 x hx.2.1 hx.2.2, hl1]
    · unfold rebB; simp only [Expr.cost] at hk2 ⊢; omega

end OM.Impl
