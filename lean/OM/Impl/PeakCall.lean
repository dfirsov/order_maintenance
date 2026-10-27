import OM.Impl.WCall
import OM.Impl.PeakSim
import OM.Impl.PeakM

/-!
# Theorem W, option (A), stage A1: calling a core procedure with a peak budget

`wpB_coreCall` is `wp_coreCall` (`WCall.lean`) with a peak budget: the call of a compiled core
procedure computes nothing above `B` when its arguments' peak and the body's Level F peak
(`pkF`, `sim_peak`) are at most `B`. This is where the bounds of stage A2 (on `pkF` of each core
procedure) enter the machine-only proofs of stage A3.
-/

namespace OM.Impl

open OM.Model
open OM.Machine (Reg Arr State Out exec Stmt Same exec_frame wp wpB)

/-- **A call of a compiled core procedure, with a peak budget.** -/
theorem wpB_coreCall {p : Nat} {κ : Caps} {s : Core} {m : State} (h : Enc p κ s m)
    {nm : String} {ps rs ds : List Reg} {body : Stm} {args : List OM.Machine.Expr} {vs : List Nat}
    (hargs : OM.Machine.evalList m args = some vs)
    {s' : Core} {L' : Loc} {n : Nat}
    (he : evalF κ body s (OM.Machine.State.setLocs (fun _ => 0) ps vs) = .ok s' L' n)
    {B : Nat} (hBa : OM.Machine.maxvList m args ≤ B)
    (hBb : pkF κ body s (OM.Machine.State.setLocs (fun _ => 0) ps vs) ≤ B)
    {Q : State → Nat → Prop}
    (hQ : ∀ m', Enc p κ s' m' → (∀ b, ¬ InSlot p b → Same b m m') →
      m'.loc = OM.Machine.State.setLocs m.loc ds (rs.map L') →
      Q m' (1 + OM.Machine.costList args + ds.length + n)) :
    wpB B (.call nm ps (body.compile p κ) rs args ds) Q m := by
  unfold wpB
  rw [OM.Machine.wp_call]
  refine ⟨vs, hargs, ?_⟩
  set m0 := (m.bump (OM.Machine.maxvList m args)).enter ps vs
  have h0 : Enc p κ s m0 := (h.bump _).withLoc _
  have hA := sim body h0 rfl
  have hP := sim_peak body h0 rfl
  have hl : m0.loc = OM.Machine.State.setLocs (fun _ => 0) ps vs := rfl
  rw [hl, he] at hA hP
  obtain ⟨hst, hE, hL, hc⟩ := hA
  simp only [PAgree] at hP
  unfold wp OM.Machine.Out.Ok
  refine ⟨hst, ?_, ?_⟩
  · simp only [st_leave_peak, hP, m0, st_enter_peak, st_bump_peak]; omega
  · rw [hc]
    refine hQ _ ((hE.withLoc _)) (fun b hb => ?_) (by simp [OM.Machine.State.leave, hL])
    have := compile_frame p κ body m0 hb
    exact ⟨this.1, this.2⟩

end OM.Impl
