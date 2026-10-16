import OM.Impl.WrapM

/-!
# M6: the rebuild loop as machine code

`loopC p` runs Level F's `rebuildLoop om nxt (K_B + 1) K_B`, with `cur` in slot `p` and `nxt` in
slot `1 - p`. It is a `for` loop of `K_B + 1` iterations; the local `bud` holds the budget, and an
iteration with no budget left does nothing. The swap sets the budget to 0, so the iterations after
it do nothing either (the parity has changed, but they only read `bud`).

What each iteration needs from the run (the preconditions of the core calls) is collected along
Level F's run by `RLSafe`.
-/

namespace OM.Impl

open OM.Model OM.Proof OM.Proof.Top
open OM.Machine (Reg Arr State Out exec Stmt Same Expr BinOp UnOp wp)

/-! ### Rules that forget the intermediate state -/

theorem wp_ite_g {c : Expr} {t f : Stmt} {Q : State → Nat → Prop} {s : State} (v : Nat)
    (hc : c.eval s = some v)
    (h : ∀ s', s'.loc = s.loc → s'.mem = s.mem → s'.cap = s.cap →
      wp (if v ≠ 0 then t else f) (fun s'' n => Q s'' (1 + c.cost + n)) s') : wp (.ite c t f) Q s := by
  rw [OM.Machine.wp_ite]; exact ⟨v, hc, h _ rfl rfl rfl⟩

theorem wp_assign_g {x : Reg} {e : Expr} {Q : State → Nat → Prop} {s : State} (v : Nat)
    (he : e.eval s = some v)
    (h : ∀ s', s'.loc = OM.Machine.State.upd s.loc x v → s'.mem = s.mem → s'.cap = s.cap → Q s' (1 + e.cost)) :
    wp (.assign x e) Q s := by
  rw [OM.Machine.wp_assign]; exact ⟨v, he, h _ rfl rfl rfl⟩

theorem wp_store_g {a : Arr} {i e : Expr} {Q : State → Nat → Prop} {s : State} (j v : Nat)
    (hi : i.eval s = some j) (he : e.eval s = some v) (hj : j < s.cap a)
    (h : ∀ s', s'.loc = s.loc → s'.mem = (s.write a j v).mem → s'.cap = s.cap → Q s' (1 + i.cost + e.cost)) :
    wp (.store a i e) Q s := by
  rw [OM.Machine.wp_store]; exact ⟨j, v, hi, he, hj, h _ rfl rfl rfl⟩

theorem wp_skip_g {Q : State → Nat → Prop} {s : State} (h : Q s 1) : wp .skip Q s :=
  OM.Machine.wp_skip.mpr h

/-! ### The code -/

/-- A preparation step of `nxt`; `r` = whether it is ready. -/
def prepC (p : Nat) : Stmt :=
  .call "prepareStep" [] (prepP.body.compile (1 - p) κ₀) ["r"] [] ["r"]

/-- Copy the element at the cursor into `nxt` if it is live, and advance the cursor. -/
def copyC (p : Nat) : Stmt :=
  .seq (.assign "c" (.load (wa 2) (.lit 0)))
    (.seq (.ite (.load (arrF p (.e .dead)) (.var "c")) .skip
        (.seq (.assign "hh" (.load (arrF p (.e .h)) (.var "c")))
          (.seq (.assign "xn" (.load (arrF (1 - p) (.s .tail)) (.lit 0))) (nxtInsC p))))
      (.store (wa 2) (.lit 0) (.load (arrF p (.e .next)) (.var "c"))))

/-- The end of the rebuild: the swap, and no budget left. -/
def endC (p : Nat) : Stmt := .seq (swapC p) (.assign "bud" (.lit 0))

/-- Spend one unit of budget. -/
def spendC : Stmt := .assign "bud" (.bin .sub (.var "bud") (.lit 1))

/-- One iteration of the rebuild loop. -/
def iterC (p : Nat) : Stmt :=
  .ite (.bin .eq (.var "bud") (.lit 0)) .skip
    (.ite (.bin .eq (.load (wa 3) (.lit 0)) (.lit 0))
      (.seq (prepC p)
        (.ite (.var "r")
          (.seq (.store (wa 2) (.lit 0) (.load (arrF p (.e .next)) (.load (arrF p (.s .head)) (.lit 0))))
            (.store (wa 3) (.lit 0) (.lit 1)))
          spendC))
      (.ite (.bin .eq (.load (wa 2) (.lit 0)) (.lit 0))
        (endC p)
        (.seq (copyC p)
          (.ite (.bin .eq (.load (wa 2) (.lit 0)) (.lit 0)) (endC p) spendC))))

/-- The rebuild loop: `K_B + 1` iterations with budget `K_B`. -/
def loopC (p : Nat) : Stmt :=
  .seq (.assign "bud" (.load (wa 7) (.lit 0)))
    (.loop "it" (.bin .add (.load (wa 7) (.lit 0)) (.lit 1)) (iterC p))

/-! ### What the iterations need -/

/-- What a copy step needs: the cursor is an element of `cur`, and if it is live, `nxt` is in
service with the anchor `tail`, and the handle is below the counter. -/
def CopyOK (om : OM) (n : Core) : Prop :=
  om.cursor < om.cur.E.size ∧ ((om.cur.E.getX om.cursor).live = true →
    ∃ B, InService n B ∧ n.tail ∈ B ∧ (om.cur.E.getX om.cursor).h < om.nextHandle)

/-- **What the iterations of Level F's run need**, along the run. -/
def RLSafe (om : OM) (n : Core) : Nat → Nat → Prop
  | 0, _ => True
  | f + 1, b => b ≠ 0 →
    (om.cursorSet = false → PrepM n ∧ 1 ≤ n.P.N ∧ om.cur.head < om.cur.E.size ∧
      ∀ r n', prepareStep.run n = .ok r n' → n'.count = n.count ∧
        (r = true → RLSafe { om with cursor := (om.cur.E.getX om.cur.head).next, cursorSet := true } n' f b) ∧
        (r = false → RLSafe om n' f (b - 1))) ∧
    (om.cursorSet = true → om.cursor ≠ NIL → CopyOK om n ∧
      ∀ om' n', copyAtCursor om n = .ok (om', n') → om'.cursor ≠ NIL → RLSafe om' n' f (b - 1))

theorem rlSafe_zero (om : OM) (n : Core) : ∀ f, RLSafe om n f 0
  | 0 => trivial
  | _ + 1 => fun h => absurd rfl h

theorem rebuildLoop_zero (om : OM) (n : Core) : ∀ f, rebuildLoop om n f 0 = .ok { om with nxt := some n }
  | 0 => rfl
  | _ + 1 => rfl

/-! ### A preparation step -/

theorem prepW_ok {om : OM} {m : State} {p : Nat} (h : WEnc om m p) {n : Core} (hn : om.nxt = some n)
    (hM : PrepM n) (hN1 : 1 ≤ n.P.N) {r : Bool} {n' : Core} (hr : prepareStep.run n = .ok r n')
    (hcnt : n'.count = n.count) :
    wp (prepC p) (fun m' k => WEnc { om with nxt := some n' } m' p ∧ m'.loc "r" = b2n r ∧
      (∀ x, x ≠ "r" → m'.loc x = m.loc x) ∧ k ≤ 450) m := by
  obtain ⟨⟨L', c, he, hr', hc⟩, hP, -, -⟩ := prepAgreeM hM hN1 hr (OM.Machine.State.setLocs (fun _ => 0) [] [])
  unfold prepC
  rw [compile_κ₀ (1 - p) n.P]
  refine wp_coreCall (h.nxt n hn) (vs := []) rfl he (fun m2 hE hS hL => ?_)
  refine ⟨h.of_nxt hn (by rw [hP]; exact hE) hS hcnt hP, ?_, fun x hx => ?_, ?_⟩
  · rw [hL]; simp [OM.Machine.State.setLocs, OM.Machine.State.upd, hr']
  · rw [hL]; simp [OM.Machine.State.setLocs, OM.Machine.State.upd, hx]
  · simp [OM.Machine.costList]; omega

/-! ### A copy step -/

theorem eval_load_var {s : State} {a : Arr} {x : Reg} {j v : Nat} (hx : s.loc x = j) (hj : j < s.cap a)
    (hv : s.mem a j = v) : (Expr.load a (.var x)).eval s = some v := by
  simp [Expr.eval, hx, hj, hv]

theorem eval_load_lit {s : State} {a : Arr} {j v : Nat} (hj : j < s.cap a)
    (hv : s.mem a j = v) : (Expr.load a (.lit j)).eval s = some v := by
  simp [Expr.eval, hj, hv]

/-- The insertion bound of a core of the proof parameters (it depends only on the `K`s). -/
def insB : Nat := insBound (proofParams 0)

theorem insBound_proof (N : Nat) : insBound (proofParams N) = insB := rfl

theorem InService.insB {c : Core} {L : List Nat} (h : InService c L) : insBound c.P = insB := by
  rw [h.ok.pmk]; rfl

/-- The last part of a copy step: the cursor moves to the successor. -/
theorem copyEnd {W : OM} {s : State} {p : Nat} (h : WEnc W s p) {c : Nat} (hc : s.loc "c" = c)
    (hcE : c < W.cur.E.size) {Q : State → Nat → Prop}
    (hQ : ∀ s', WEnc { W with cursor := (W.cur.E.getX c).next } s' p → s'.loc = s.loc →
      Q s' (1 + (Expr.lit 0).cost + (Expr.load (arrF p (.e .next)) (.var "c")).cost)) :
    wp (.store (wa 2) (.lit 0) (.load (arrF p (.e .next)) (.var "c"))) Q s := by
  have hcap : c < s.cap (arrF p (.e .next)) := by
    rw [h.cur.cap]; exact Nat.lt_of_lt_of_le hcE (h.cur.sle .E)
  refine wp_store_g 0 (W.cur.E.getX c).next rfl
    (eval_load_var hc hcap (by rw [h.cur.mem _ _ (by rw [← h.cur.cap]; exact hcap)]; rfl))
    (by rw [h.scap 2 (by decide)]; decide) (fun s' hl hm hcp => ?_)
  exact hQ s' ((h.writeCursor _).congr hm hcp) hl

theorem copyW_ok {om : OM} {n : Core} {m : State} {p : Nat} (h : WEnc { om with nxt := some n } m p)
    (hC : CopyOK om n) {om' : OM} {n' : Core} (hcp : copyAtCursor om n = .ok (om', n')) :
    wp (copyC p) (fun m' k => WEnc { om' with nxt := some n' } m' p ∧
      (∀ x, x ≠ "c" → x ≠ "hh" → x ≠ "xn" → x ≠ "y2" → m'.loc x = m.loc x) ∧ k ≤ insB + 100) m := by
  have hp := h.p2
  obtain ⟨hcE, hlive⟩ := hC
  set e := om.cur.E.getX om.cursor with he
  have hcapE : om.cursor < (capsOf om.cur.P).tbl .E := Nat.lt_of_lt_of_le hcE (h.cur.sle .E)
  unfold copyC
  rw [OM.Machine.wp_seq]
  refine wp_assign_g om.cursor (eval_load_lit (by rw [h.scap 2 (by decide)]; decide) h.cursor)
    (fun s1 hl1 hm1 hc1 => ?_)
  have h1 := h.congr hm1 hc1
  have hc1' : s1.loc "c" = om.cursor := by rw [hl1]; simp [OM.Machine.State.upd]
  have hl1' : ∀ x, x ≠ "c" → s1.loc x = m.loc x := fun x hx => by rw [hl1]; simp [OM.Machine.State.upd, hx]
  rw [OM.Machine.wp_seq]
  have hdead : (Expr.load (arrF p (.e .dead)) (.var "c")).eval s1 = some (b2n !e.live) :=
    eval_load_var hc1' (by rw [h1.cur.cap]; exact hcapE) (by rw [h1.cur.mem _ _ hcapE]; rfl)
  refine wp_ite_g _ hdead (fun s2 hl2 hm2 hc2 => ?_)
  have h2 := h1.congr hm2 hc2
  cases hl : e.live with
  | false =>
    have hom : om' = { om with cursor := e.next } ∧ n' = n := by
      unfold copyAtCursor at hcp; simp only [← he, hl] at hcp; cases hcp; exact ⟨rfl, rfl⟩
    obtain ⟨rfl, rfl⟩ := hom
    simp only [hl, Bool.not_false, b2n, ne_eq, one_ne_zero, not_false_eq_true, if_true, ↓reduceIte]
    refine wp_skip_g ?_
    refine copyEnd h2 (by rw [hl2, hc1']) hcE (fun s3 h3 hl3 => ⟨h3, fun x a b c d => ?_, ?_⟩)
    · rw [hl3, hl2, hl1' x a]
    · simp [Expr.cost]
  | true =>
    obtain ⟨B, hS, htail, hhc⟩ := hlive hl
    simp only [hl, Bool.not_true, b2n, Bool.false_eq_true, ne_eq, not_true_eq_false, if_false, ↓reduceIte,
      not_false_eq_true]
    rw [OM.Machine.wp_seq]
    refine wp_assign_g e.h (eval_load_var (by rw [hl2, hc1']) (by rw [h2.cur.cap]; exact hcapE)
      (by rw [h2.cur.mem _ _ hcapE]; rfl)) (fun s3 hl3 hm3 hc3 => ?_)
    have h3 := h2.congr hm3 hc3
    rw [OM.Machine.wp_seq]
    have hnE := h3.nxt n rfl
    refine wp_assign_g n.tail (eval_load_lit (by rw [hnE.cap]; simp [Fld.cap])
      (by rw [hnE.mem _ _ (by simp [Fld.cap])]; rfl)) (fun s4 hl4 hm4 hc4 => ?_)
    have h4 := h3.congr hm4 hc4
    have hhc4 : e.h < s4.cap (wIdx (1 - p)) := by
      have := h.roomN n rfl
      rw [hc4, hc3, hc2, hc1]
      simp only at this
      omega
    obtain ⟨n2, hr2, -, -, -, -, hwp⟩ := nxtInsW_ok h4 rfl hS htail
      (by rw [hl4]; simp [OM.Machine.State.upd]) (by rw [hl4, hl3]; simp [OM.Machine.State.upd]) hhc4
    have hom : om' = { om with nxtIdx := om.nxtIdx.setX e.h n.E.size, cursor := e.next } ∧ n' = n2 := by
      unfold copyAtCursor at hcp; simp only [← he, hl, if_true, runCore, hr2] at hcp; cases hcp
      exact ⟨rfl, rfl⟩
    obtain ⟨rfl, rfl⟩ := hom
    refine OM.Machine.wp_mono (fun s5 k5 ⟨h5, hl5, hk5⟩ => ?_) hwp
    have hc5 : s5.loc "c" = om.cursor := by
      rw [hl5 "c" (by decide), hl4, hl3, hl2]; simp [OM.Machine.State.upd, hc1']
    refine copyEnd h5 hc5 hcE (fun s6 h6 hl6 => ⟨?_, fun x a b c d => ?_, ?_⟩)
    · exact h6
    · rw [hl6, hl5 x d, hl4, hl3, hl2]; simp [OM.Machine.State.upd, b, c, hl1' x a]
    · rw [hS.insB] at hk5; simp [Expr.cost]; omega

end OM.Impl
