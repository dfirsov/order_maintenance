import OM.Impl.NewCore

/-!
# M6: the wrapper as machine code

**Layout.** The cores live in slots 0 and 1 (arrays `1000·p + code`); the wrapper's own arrays
are numbered from 2000, outside both slots:
* one cell each: `wa 0` parity (the slot of `cur`), `wa 1` whether `nxt` exists, `wa 2` cursor,
  `wa 3` cursorSet, `wa 4` live, `wa 5` nextHandle, `wa 6` rebuilds, `wa 7` `K_B`;
* the handle maps `wIdx q` (`q` = 0, 1): `curIdx` in `wIdx p`, `nxtIdx` in `wIdx (1 - p)`.

`WEnc om m p` says that machine state `m` holds wrapper state `om` with `cur` in slot `p`.
The wrapper code tests the parity and runs the code specialized to it.
-/

namespace OM.Impl

open OM.Model OM.Proof OM.Proof.Top
open OM.Machine (Reg Arr State Out exec Stmt Same Expr BinOp UnOp wp)

def wa (k : Nat) : Arr := 2000 + k
def wIdx (q : Nat) : Arr := 2010 + q

theorem wa_notSlot {p k : Nat} (hp : p < 2) : ¬ InSlot p (wa k) := by
  unfold InSlot wa; omega
theorem wIdx_notSlot {p q : Nat} (hp : p < 2) : ¬ InSlot p (wIdx q) := by
  unfold InSlot wIdx; omega

/-- **The encoding of the wrapper state.** -/
structure WEnc (om : OM) (m : State) (p : Nat) : Prop where
  p2 : p < 2
  scap : ∀ k < 8, m.cap (wa k) = 1
  par : m.mem (wa 0) 0 = p
  nxtOn : m.mem (wa 1) 0 = b2n om.nxt.isSome
  cursor : m.mem (wa 2) 0 = om.cursor
  cset : m.mem (wa 3) 0 = b2n om.cursorSet
  live : m.mem (wa 4) 0 = om.live
  next : m.mem (wa 5) 0 = om.nextHandle
  reb : m.mem (wa 6) 0 = om.rebuilds
  kb : m.mem (wa 7) 0 = om.KB
  cur : Enc p (capsOf om.cur.P) om.cur m
  nxt : ∀ n, om.nxt = some n → Enc (1 - p) (capsOf n.P) n m
  idxC : ∀ h < m.cap (wIdx p), m.mem (wIdx p) h = om.curIdx.getX h
  idxN : om.nxt.isSome → ∀ h < m.cap (wIdx (1 - p)), m.mem (wIdx (1 - p)) h = om.nxtIdx.getX h
  roomC : om.nextHandle + (om.cur.P.N - om.cur.count) ≤ m.cap (wIdx p)
  roomN : ∀ n, om.nxt = some n →
    om.nextHandle + (om.cur.P.N - om.cur.count) + (n.P.N - n.count) ≤ m.cap (wIdx (1 - p))

/-- The wrapper state survives anything that keeps slot `p`'s core, the other slot, and the
wrapper's arrays. -/
theorem WEnc.of_slot {om : OM} {m m' : State} {p : Nat} (h : WEnc om m p)
    (hcur : Enc p (capsOf om.cur.P) om.cur m') (hS : ∀ b, ¬ InSlot p b → Same b m m') : WEnc om m' p := by
  have hp := h.p2
  have hw : ∀ k, Same (wa k) m m' := fun k => hS _ (wa_notSlot hp)
  have hi : ∀ q, Same (wIdx q) m m' := fun q => hS _ (wIdx_notSlot hp)
  refine ⟨hp, fun k hk => by rw [(hw k).2]; exact h.scap k hk, by rw [(hw 0).1]; exact h.par,
    by rw [(hw 1).1]; exact h.nxtOn, by rw [(hw 2).1]; exact h.cursor, by rw [(hw 3).1]; exact h.cset,
    by rw [(hw 4).1]; exact h.live, by rw [(hw 5).1]; exact h.next, by rw [(hw 6).1]; exact h.reb,
    by rw [(hw 7).1]; exact h.kb, hcur, fun n hn => ?_, fun x hx => ?_, fun hn x hx => ?_, ?_, fun n hn => ?_⟩
  · exact (h.nxt n hn).of_same fun b hb => hS b (fun hpb => inSlot_disj (by omega) hpb hb)
  · rw [(hi p).2] at hx; rw [(hi p).1]; exact h.idxC x hx
  · rw [(hi (1 - p)).2] at hx; rw [(hi (1 - p)).1]; exact h.idxN hn x hx
  · rw [(hi p).2]; exact h.roomC
  · rw [(hi (1 - p)).2]; exact h.roomN n hn

theorem WEnc.bump {om : OM} {m : State} {p : Nat} (h : WEnc om m p) (v : Nat) : WEnc om (m.bump v) p :=
  h.of_slot (h.cur.bump v) fun _ _ => ⟨rfl, rfl⟩
theorem WEnc.setLoc {om : OM} {m : State} {p : Nat} (h : WEnc om m p) (x : Reg) (v : Nat) :
    WEnc om (m.setLoc x v) p :=
  h.of_slot (h.cur.setLoc x v) fun _ _ => ⟨rfl, rfl⟩

/-- The parity test. -/
def parE : Expr := .bin .eq (.load (wa 0) (.lit 0)) (.lit 0)

/-- Run the code specialized to the parity. -/
def byPar (c : Nat → Stmt) : Stmt := .ite parE (c 0) (c 1)

theorem wp_byPar {om : OM} {m : State} {p : Nat} (h : WEnc om m p) {c : Nat → Stmt} {Q : State → Nat → Prop}
    (hc : wp (c p) (fun s' n => Q s' (1 + parE.cost + n)) (m.bump (parE.maxv m))) : wp (byPar c) Q m := by
  unfold byPar
  rw [OM.Machine.wp_ite]
  have hev : parE.eval m = some (if p = 0 then 1 else 0) := by
    simp [parE, Expr.eval, h.scap 0 (by omega), h.par, BinOp.eval]
  refine ⟨_, hev, ?_⟩
  have := h.p2
  by_cases hp : p = 0
  · subst hp; simpa using hc
  · have : p = 1 := by omega
    subst this; simpa using hc

/-! ### Order queries -/

/-- Order of the handles in locals `x`, `y`; the answer in local `r`. -/
def orderC (p : Nat) : Stmt :=
  .seq (.assign "xi" (.load (wIdx p) (.var "x"))) (.seq (.assign "yi" (.load (wIdx p) (.var "y")))
    (.call "order" ["x", "y"] (orderP.body.compile p κ₀) ["r"] [.var "xi", .var "yi"] ["r"]))

def orderWS : Stmt := byPar orderC

theorem order_run_state {x y : Nat} {s s' : Core} {b : Bool} (h : (OM.Model.order x y).run s = .ok b s') :
    s' = s := by
  unfold OM.Model.order OM.Model.key at h; simp [getE, getG, getC] at h; exact h.2.symm

/-- **An order query** at the machine level. -/
theorem orderW_ok {om : OM} {m : State} {p : Nat} (h : WEnc om m p) {x y : Nat}
    (hx : m.loc "x" = x) (hy : m.loc "y" = y) (hxc : x < m.cap (wIdx p)) (hyc : y < m.cap (wIdx p))
    {P : Params} {n R : Nat} {L : List Nat} (hC : CostInv (TIat TopInv P) topMu (topJ P) n R L om.cur)
    (hP : om.cur.P = P) (hxL : om.curIdx.getX x ∈ L) (hyL : om.curIdx.getX y ∈ L)
    (hcntL : om.cur.count = L.length) (hM : Mc (capsOf P) P om.cur) {b : Bool} {s' : Core}
    (hr : (OM.Model.order (om.curIdx.getX x) (om.curIdx.getX y)).run om.cur = .ok b s') :
    wp orderWS (fun m' c => WEnc om m' p ∧ m'.loc "r" = b2n b ∧ c ≤ 100) m := by
  have e := order_run_state hr; subst e
  refine wp_byPar h ?_
  set m0 := m.bump (parE.maxv m)
  have h0 := h.bump (parE.maxv m)
  unfold orderC
  rw [OM.Machine.wp_seq, OM.Machine.wp_assign]
  refine ⟨om.curIdx.getX x, by simp [Expr.eval, m0, hx, hxc, h.idxC x hxc], ?_⟩
  rw [OM.Machine.wp_seq, OM.Machine.wp_assign]
  set m1 := (m0.bump _).setLoc "xi" (om.curIdx.getX x)
  have h1 : WEnc om m1 p := (h0.bump _).setLoc _ _
  refine ⟨om.curIdx.getX y, by simp [Expr.eval, m1, m0, hy, hyc, h.idxC y hyc], ?_⟩
  set m2 := (m1.bump _).setLoc "yi" (om.curIdx.getX y)
  have h2 : WEnc om m2 p := (h1.bump _).setLoc _ _
  have hcur : Enc p (capsOf P) om.cur m2 := by rw [← hP]; exact h2.cur
  obtain ⟨L', c, he, hrr, hc⟩ := orderAgreeM hC hP hxL hyL (OM.Machine.State.setLocs (fun _ => 0) ["x", "y"]
    [om.curIdx.getX x, om.curIdx.getX y]) (by simp [OM.Machine.State.setLocs, OM.Machine.State.upd])
    (by simp [OM.Machine.State.setLocs, OM.Machine.State.upd]) (capsOf_ok P) hcntL hM hr
  rw [compile_κ₀ p P]
  refine wp_coreCall hcur (by simp [OM.Machine.evalList, Expr.eval, m2, m1]) he (fun m3 hE hS hL => ?_)
  refine ⟨h2.of_slot (by rw [hP]; exact hE) hS, by rw [hL]; simp [OM.Machine.State.setLocs, hrr], ?_⟩
  simp [OM.Machine.costList, Expr.cost, parE] at *; omega

/-! ### Writing the current handle map -/

/-- Writing `v` at handle `x` of the current handle map. -/
theorem WEnc.writeC {om : OM} {m : State} {p : Nat} (h : WEnc om m p) {x v : Nat} (hx : x < m.cap (wIdx p)) :
    WEnc { om with curIdx := om.curIdx.setX x v } (m.write (wIdx p) x v) p := by
  have hp := h.p2
  have hne : ∀ k < 8, wa k ≠ wIdx p := fun k hk e => by
    have : (2000 + k : Nat) = 2010 + p := e
    omega
  have hq : wIdx (1 - p) ≠ wIdx p := fun e => by
    have : (2010 + (1 - p) : Nat) = 2010 + p := e
    omega
  refine ⟨hp, fun k hk => h.scap k hk, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_,
    h.cur.of_same fun b hb => ⟨?_, rfl⟩, fun n hn => (h.nxt n hn).of_same fun b hb => ⟨?_, rfl⟩,
    fun i hi => ?_, fun hn i hi => ?_, h.roomC, h.roomN⟩
  all_goals simp only [State.write, OM.Machine.State.upd]
  · rw [if_neg (hne 0 (by decide))]; exact h.par
  · rw [if_neg (hne 1 (by decide))]; exact h.nxtOn
  · rw [if_neg (hne 2 (by decide))]; exact h.cursor
  · rw [if_neg (hne 3 (by decide))]; exact h.cset
  · rw [if_neg (hne 4 (by decide))]; exact h.live
  · rw [if_neg (hne 5 (by decide))]; exact h.next
  · rw [if_neg (hne 6 (by decide))]; exact h.reb
  · rw [if_neg (hne 7 (by decide))]; exact h.kb
  · funext i; rw [if_neg (fun e => wIdx_notSlot hp (e ▸ hb))]
  · funext i; rw [if_neg (fun e => wIdx_notSlot (p := 1 - p) (by omega) (e ▸ hb))]
  · simp only [if_true, OM.Proof.Top.getX_setX']
    by_cases e : i = x
    · simp [e]
    · simp [e, h.idxC i hi]
  · rw [if_neg hq]; exact h.idxN hn i hi

/-! ### Deletion -/

/-- Delete the element of handle `x` from `cur`. -/
def curDelC (p : Nat) : Stmt :=
  .seq (.assign "xi" (.load (wIdx p) (.var "x")))
  (.seq (.call "markDead" ["x"] (markDeadP.body.compile p κ₀) [] [.var "xi"] [])
    (.store (wIdx p) (.var "x") (.lit 0)))

theorem curDelW_ok {om : OM} {m : State} {p : Nat} (h : WEnc om m p) {x : Nat}
    (hx : m.loc "x" = x) (hxc : x < m.cap (wIdx p))
    {P : Params} {n R : Nat} {L : List Nat} (hC : CostInv (TIat TopInv P) topMu (topJ P) n R L om.cur)
    (hP : om.cur.P = P) (hxL : om.curIdx.getX x ∈ L) (hcntL : om.cur.count = L.length)
    (hM : Mc (capsOf P) P om.cur) {c' : Core} (hr : (markDead (om.curIdx.getX x)).run om.cur = .ok () c') :
    wp (curDelC p) (fun m' k => WEnc { om with cur := c', curIdx := om.curIdx.setX x 0 } m' p ∧
      m'.loc = OM.Machine.State.upd m.loc "xi" (om.curIdx.getX x) ∧ k ≤ 40) m := by
  obtain ⟨s', hr', ⟨L', c, he, hc⟩, -, hcnt', hP', -⟩ := markDeadAgreeM hC hP hxL
    (OM.Machine.State.setLocs (fun _ => 0) ["x"] [om.curIdx.getX x])
    (by simp [OM.Machine.State.setLocs, OM.Machine.State.upd]) (capsOf_ok P) hcntL hM
  rw [hr] at hr'; obtain ⟨-, rfl⟩ := EStateM.Result.ok.inj hr'
  unfold curDelC
  rw [OM.Machine.wp_seq, OM.Machine.wp_assign]
  refine ⟨om.curIdx.getX x, by simp [Expr.eval, hx, hxc, h.idxC x hxc], ?_⟩
  set m1 := (m.bump _).setLoc "xi" (om.curIdx.getX x)
  have h1 : WEnc om m1 p := (h.bump _).setLoc _ _
  rw [OM.Machine.wp_seq, compile_κ₀ p P]
  have hcur : Enc p (capsOf P) om.cur m1 := by rw [← hP]; exact h1.cur
  refine wp_coreCall hcur (by simp [OM.Machine.evalList, Expr.eval, m1]) he (fun m2 hE hS hL => ?_)
  have h2 : WEnc { om with cur := c' } m2 p := by
    have hE' : Enc p (capsOf c'.P) c' m2 := by rw [hP', hP]; exact hE
    refine ⟨h1.p2, fun k hk => by rw [(hS _ (wa_notSlot h1.p2)).2]; exact h1.scap k hk, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_,
      hE', fun n hn => (h1.nxt n hn).of_same fun b hb => hS b (fun hpb => inSlot_disj (by have := h1.p2; omega) hpb hb),
      fun i hi => ?_, fun hn i hi => ?_, ?_, fun n hn => ?_⟩
    · rw [(hS _ (wa_notSlot h1.p2)).1]; exact h1.par
    · rw [(hS _ (wa_notSlot h1.p2)).1]; exact h1.nxtOn
    · rw [(hS _ (wa_notSlot h1.p2)).1]; exact h1.cursor
    · rw [(hS _ (wa_notSlot h1.p2)).1]; exact h1.cset
    · rw [(hS _ (wa_notSlot h1.p2)).1]; exact h1.live
    · rw [(hS _ (wa_notSlot h1.p2)).1]; exact h1.next
    · rw [(hS _ (wa_notSlot h1.p2)).1]; exact h1.reb
    · rw [(hS _ (wa_notSlot h1.p2)).1]; exact h1.kb
    · rw [(hS _ (wIdx_notSlot h1.p2)).2] at hi; rw [(hS _ (wIdx_notSlot h1.p2)).1]; exact h1.idxC i hi
    · rw [(hS _ (wIdx_notSlot h1.p2)).2] at hi; rw [(hS _ (wIdx_notSlot h1.p2)).1]; exact h1.idxN hn i hi
    · rw [(hS _ (wIdx_notSlot h1.p2)).2]; show _ + (c'.P.N - c'.count) ≤ _; rw [hP', hcnt']; exact h1.roomC
    · rw [(hS _ (wIdx_notSlot h1.p2)).2]; show _ + (c'.P.N - c'.count) + _ ≤ _; rw [hP', hcnt']; exact h1.roomN n hn
  rw [OM.Machine.wp_store]
  have hxc2 : x < m2.cap (wIdx p) := by rw [(hS _ (wIdx_notSlot h1.p2)).2]; exact hxc
  refine ⟨x, 0, by simp [Expr.eval, hL, OM.Machine.State.setLocs, m1, hx], rfl, hxc2, ?_⟩
  refine ⟨(h2.bump _ |>.bump _).writeC (by simpa using hxc2), by simp [hL, OM.Machine.State.setLocs, m1], ?_⟩
  simp [OM.Machine.costList, Expr.cost] at *; omega

/-! ### The next core -/

/-- The next core changes (in its slot), with the same parameters and count. -/
theorem WEnc.of_nxt {om : OM} {m m' : State} {p : Nat} (h : WEnc om m p) {n n' : Core} (hn : om.nxt = some n)
    (hE : Enc (1 - p) (capsOf n'.P) n' m') (hS : ∀ b, ¬ InSlot (1 - p) b → Same b m m')
    (hcnt : n'.count = n.count) (hP : n'.P = n.P) : WEnc { om with nxt := some n' } m' p := by
  have hp := h.p2
  have hp' : 1 - p < 2 := by omega
  have hw : ∀ k, Same (wa k) m m' := fun k => hS _ (wa_notSlot hp')
  have hi : ∀ q, Same (wIdx q) m m' := fun q => hS _ (wIdx_notSlot hp')
  refine ⟨hp, fun k hk => by rw [(hw k).2]; exact h.scap k hk, by rw [(hw 0).1]; exact h.par,
    by rw [(hw 1).1, h.nxtOn, hn]; rfl, by rw [(hw 2).1]; exact h.cursor, by rw [(hw 3).1]; exact h.cset,
    by rw [(hw 4).1]; exact h.live, by rw [(hw 5).1]; exact h.next, by rw [(hw 6).1]; exact h.reb,
    by rw [(hw 7).1]; exact h.kb, h.cur.of_same fun b hb => hS b (fun hpb => inSlot_disj (by omega) hpb hb),
    fun n2 hn2 => ?_, fun x hx => ?_, fun _ x hx => ?_, ?_, fun n2 hn2 => ?_⟩
  · cases hn2; exact hE
  · rw [(hi p).2] at hx; rw [(hi p).1]; exact h.idxC x hx
  · rw [(hi (1 - p)).2] at hx; rw [(hi (1 - p)).1]; exact h.idxN (by rw [hn]; rfl) x hx
  · rw [(hi p).2]; exact h.roomC
  · cases hn2; rw [(hi (1 - p)).2]; show _ + (n'.P.N - n'.count) ≤ _; rw [hcnt, hP]; exact h.roomN n hn

/-- Writing `v` at handle `x` of the next handle map. -/
theorem WEnc.writeN {om : OM} {m : State} {p : Nat} (h : WEnc om m p) {x v : Nat}
    (hx : x < m.cap (wIdx (1 - p))) :
    WEnc { om with nxtIdx := om.nxtIdx.setX x v } (m.write (wIdx (1 - p)) x v) p := by
  have hp := h.p2
  have hne : ∀ k < 8, wa k ≠ wIdx (1 - p) := fun k hk e => by
    have : (2000 + k : Nat) = 2010 + (1 - p) := e
    omega
  have hq : wIdx p ≠ wIdx (1 - p) := fun e => by
    have : (2010 + p : Nat) = 2010 + (1 - p) := e
    omega
  refine ⟨hp, fun k hk => h.scap k hk, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_,
    h.cur.of_same fun b hb => ⟨?_, rfl⟩, fun n hn => (h.nxt n hn).of_same fun b hb => ⟨?_, rfl⟩,
    fun i hi => ?_, fun hn i hi => ?_, h.roomC, h.roomN⟩
  all_goals simp only [State.write, OM.Machine.State.upd]
  · rw [if_neg (hne 0 (by decide))]; exact h.par
  · rw [if_neg (hne 1 (by decide))]; exact h.nxtOn
  · rw [if_neg (hne 2 (by decide))]; exact h.cursor
  · rw [if_neg (hne 3 (by decide))]; exact h.cset
  · rw [if_neg (hne 4 (by decide))]; exact h.live
  · rw [if_neg (hne 5 (by decide))]; exact h.next
  · rw [if_neg (hne 6 (by decide))]; exact h.reb
  · rw [if_neg (hne 7 (by decide))]; exact h.kb
  · funext i; rw [if_neg (fun e => wIdx_notSlot hp (e ▸ hb))]
  · funext i; rw [if_neg (fun e => wIdx_notSlot (p := 1 - p) (by omega) (e ▸ hb))]
  · rw [if_neg hq]; exact h.idxC i hi
  · simp only [if_true, OM.Proof.Top.getX_setX']
    by_cases e : i = x
    · simp [e]
    · simp [e, h.idxN hn i hi]

/-! ### Mirroring a deletion into `nxt` -/

def mirrorDelC (p : Nat) : Stmt :=
  .ite (.bin .eq (.load (wa 1) (.lit 0)) (.lit 0)) .skip
    (.seq (.assign "xn" (.load (wIdx (1 - p)) (.var "x")))
      (.ite (.bin .eq (.var "xn") (.lit 0)) .skip
        (.seq (.call "markDead" ["x"] (markDeadP.body.compile (1 - p) κ₀) [] [.var "xn"] [])
          (.store (wIdx (1 - p)) (.var "x") (.lit 0)))))

/-- The core facts a deletion from `nxt` needs. -/
def DelOK (n : Core) (xn : Nat) : Prop :=
  ∃ (P : Params) (nn R : Nat) (L : List Nat), CostInv (TIat TopInv P) topMu (topJ P) nn R L n ∧ n.P = P ∧
    xn ∈ L ∧ n.count = L.length ∧ Mc (capsOf P) P n

theorem mirrorDelW_ok {om : OM} {m : State} {p : Nat} (h : WEnc om m p) {x : Nat}
    (hx : m.loc "x" = x) (hxc : om.nxt.isSome → x < m.cap (wIdx (1 - p)))
    (hN : ∀ n, om.nxt = some n → om.nxtIdx.getX x ≠ 0 → DelOK n (om.nxtIdx.getX x))
    {om2 : OM} (hr : om.mirrorDelete x = .ok om2) :
    wp (mirrorDelC p) (fun m' k => WEnc om2 m' p ∧ m'.loc "x" = x ∧ k ≤ 50) m := by
  have hp := h.p2
  unfold mirrorDelC
  rw [OM.Machine.wp_ite]
  cases hn : om.nxt with
  | none =>
    have : om2 = om := by unfold OM.mirrorDelete at hr; rw [hn] at hr; cases hr; rfl
    subst this
    refine ⟨1, by simp [Expr.eval, h.scap 1 (by decide), h.nxtOn, hn, BinOp.eval, b2n], ?_⟩
    simp only [ne_eq, one_ne_zero, not_false_eq_true, if_true, OM.Machine.wp_skip]
    exact ⟨h.bump _, by simp [hx], by simp [Expr.cost]⟩
  | some n =>
    refine ⟨0, by simp [Expr.eval, h.scap 1 (by decide), h.nxtOn, hn, BinOp.eval, b2n], ?_⟩
    simp only [ne_eq, not_true_eq_false, if_false]
    have hxc' := hxc (by rw [hn]; rfl)
    rw [OM.Machine.wp_seq, OM.Machine.wp_assign]
    refine ⟨om.nxtIdx.getX x, by simp [Expr.eval, hx, hxc', h.idxN (by rw [hn]; rfl) x hxc'], ?_⟩
    set m1 := ((m.bump _).bump _).setLoc "xn" (om.nxtIdx.getX x)
    have h1 : WEnc om m1 p := ((h.bump _).bump _).setLoc _ _
    rw [OM.Machine.wp_ite]
    by_cases h0 : om.nxtIdx.getX x = 0
    · have : om2 = om := by
        unfold OM.mirrorDelete at hr; rw [hn] at hr; simp [h0] at hr
        cases hr; rfl
      subst this
      refine ⟨1, by simp [Expr.eval, m1, h0, BinOp.eval], ?_⟩
      simp only [ne_eq, one_ne_zero, not_false_eq_true, if_true, OM.Machine.wp_skip]
      exact ⟨h1.bump _, by simp [m1, hx], by simp [Expr.cost]⟩
    · refine ⟨0, by simp [Expr.eval, m1, h0, BinOp.eval], ?_⟩
      simp only [ne_eq, not_true_eq_false, if_false]
      obtain ⟨P, nn, R, L, hC, hP, hxL, hcntL, hM⟩ := hN n hn h0
      obtain ⟨n', hr', ⟨L', c, he, hc⟩, -, hcnt', hP', -⟩ := markDeadAgreeM hC hP hxL
        (OM.Machine.State.setLocs (fun _ => 0) ["x"] [om.nxtIdx.getX x])
        (by simp [OM.Machine.State.setLocs, OM.Machine.State.upd]) (capsOf_ok P) hcntL hM
      have hom2 : om2 = { om with nxt := some n', nxtIdx := om.nxtIdx.setX x 0 } := by
        unfold OM.mirrorDelete at hr; rw [hn] at hr; simp [h0, runCore, hr'] at hr; exact hr.symm
      subst hom2
      rw [OM.Machine.wp_seq, compile_κ₀ (1 - p) P]
      have hb1 := h1.bump (Expr.maxv m1 (.bin .eq (.var "xn") (.lit 0)))
      have hnE : Enc (1 - p) (capsOf P) n (m1.bump (Expr.maxv m1 (.bin .eq (.var "xn") (.lit 0)))) := by
        rw [← hP]; exact hb1.nxt n hn
      refine wp_coreCall hnE (by simp [OM.Machine.evalList, Expr.eval, m1]) he (fun m2 hE hS hL => ?_)
      have h2 : WEnc { om with nxt := some n' } m2 p :=
        hb1.of_nxt hn (by rw [hP', hP]; exact hE) hS hcnt' hP'
      rw [OM.Machine.wp_store]
      have hxc2 : x < m2.cap (wIdx (1 - p)) := by
        rw [(hS _ (wIdx_notSlot (by omega))).2]; exact hxc'
      refine ⟨x, 0, by simp [Expr.eval, hL, OM.Machine.State.setLocs, m1, hx], rfl, hxc2, ?_⟩
      refine ⟨(h2.bump _ |>.bump _).writeN (by simpa using hxc2), by simp [hL, OM.Machine.State.setLocs, m1, hx], ?_⟩
      simp [OM.Machine.costList, Expr.cost] at *; omega

end OM.Impl
