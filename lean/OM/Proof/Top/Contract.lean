import OM.Proof.Top.InsStart
import OM.Proof.Top.Step

/-!
# M5: the top structure's contract

`TopInv`, `topMu` and the job bound `topJ` satisfy M4's contract, relative to `SDOK`
(a drain's start keeps the invariant).
-/

namespace OM.Proof.Top

open OM.Model OM.Proof

/-- **The top structure's contract** (relative to the drain start, `SDOK`). -/
theorem topContract (hSD : SDOK) : TopContractP TopInv topMu topJ capT :=
  ⟨fun _ _ h hI => h.topInv hI, fun _ _ h => h.topMu,
    fun _ _ _ hA hT hres hx _ hcap => top_start hA hT hres hx hcap,
    fun _ _ _ _ hT hres => top_step hSD hT hres⟩

end OM.Proof.Top
