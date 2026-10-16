import OM.Impl.SlotFrame
import OM.Machine.Logic

/-!
# M6: calling a compiled core procedure from wrapper code

`wp_coreCall`: if machine state `m` holds core `s` in slot `p`, a `call` of the compiled body of a
core procedure ends as `evalF` says: the slot holds the resulting core, the results are copied
back, the cost is the source's plus the call's overhead, and every array outside slot `p` is
unchanged.
-/

namespace OM.Impl

open OM.Model
open OM.Machine (Reg Arr State Out exec Stmt Same exec_frame wp)

/-- **A call of a compiled core procedure.** -/
theorem wp_coreCall {p : Nat} {κ : Caps} {s : Core} {m : State} (h : Enc p κ s m)
    {nm : String} {ps rs ds : List Reg} {body : Stm} {args : List OM.Machine.Expr} {vs : List Nat}
    (hargs : OM.Machine.evalList m args = some vs)
    {s' : Core} {L' : Loc} {n : Nat}
    (he : evalF κ body s (OM.Machine.State.setLocs (fun _ => 0) ps vs) = .ok s' L' n)
    {Q : State → Nat → Prop}
    (hQ : ∀ m', Enc p κ s' m' → (∀ b, ¬ InSlot p b → Same b m m') →
      m'.loc = OM.Machine.State.setLocs m.loc ds (rs.map L') →
      Q m' (1 + OM.Machine.costList args + ds.length + n)) :
    wp (.call nm ps (body.compile p κ) rs args ds) Q m := by
  rw [OM.Machine.wp_call]
  refine ⟨vs, hargs, ?_⟩
  set m0 := (m.bump (OM.Machine.maxvList m args)).enter ps vs
  have h0 : Enc p κ s m0 := (h.bump _).withLoc _
  have hA := sim body h0 rfl
  have hl : m0.loc = OM.Machine.State.setLocs (fun _ => 0) ps vs := rfl
  rw [hl, he] at hA
  obtain ⟨hst, hE, hL, hc⟩ := hA
  unfold wp OM.Machine.Out.Ok
  refine ⟨hst, ?_⟩
  rw [hc]
  refine hQ _ ((hE.withLoc _)) (fun b hb => ?_) (by simp [OM.Machine.State.leave, hL])
  have := compile_frame p κ body m0 hb
  exact ⟨this.1, this.2⟩

end OM.Impl
