import OM.Impl.Job

/-!
# M6: the reservation loop at Level M

`reservation k`: up to `k` rounds; a round resumes the running job, or, with no job, pops the
fullest quiet chunk and starts its split, or stops when the queue is empty. The machine has no
`return`, so a flag `dn` makes the remaining rounds empty, as in `driveGroupFrom`.
-/

namespace OM.Impl

open OM.Model
open OM.Proof.Top
open OM.Machine (Reg BinOp UnOp)

local notation "upd" => OM.Machine.State.upd

/-- The body of Level F's reservation loop (as elaborated). -/
def resF : Nat → Option Unit × Unit → CM (ForInStep (Option Unit × Unit)) := fun _ _ => do
  let d ← get
  match d.resJob with
  | none => do
    let e ← pqEmpty
    if e = true then pure (ForInStep.done (some (), ())) else do
      let c ← pqPopMax
      splitChunkStart c
      pure (ForInStep.yield (none, ()))
  | some job => do
    let r ← jobStep job
    modify fun s => { s with resJob := r }
    pure (ForInStep.yield (none, ()))

theorem reservation_eq (k : Nat) (s : Core) :
    (reservation k).run s = ((forIn (List.range k) ((none : Option Unit), ()) resF) >>= fun r =>
      match r.1 with | some r => pure r | none => pure ()).run s := by
  unfold reservation
  congr 2
  funext x a
  rcases x with ⟨_ | _, _⟩ <;> rfl

def jobP : Proc := { name := "jobStep", params := [], rets := [], body := jobStepS }
def splitP : Proc := { name := "splitChunkStart", params := ["x"], rets := [], body := splitChunkStartS }

def resBody : Stm :=
  .ite ("dn" =ₑ 0)
    (.ite (.opt .jobOn) (jobP.call [] [])
      (pqEmptyP.call [] ["em"] ;; .ite "em" ("dn" ::= 1) (pqPopMaxP.call [] ["x"] ;; splitP.call [.var "x"] [])))
    .skip
/-- `reservation K_R`. -/
def reservationS : Stm := "dn" ::= 0 ;; .loop "ri" (.prm .KR) resBody

/-- A Level M round that agrees with a Level F one (`stop`: Level F's round ended the loop). -/
def ResAgree (κ : Caps) (t t' : Core) (stop : Bool) (D : Nat) : Prop :=
  ∀ L : Loc, L "dn" = 0 → ∃ L' n, evalF κ resBody t L = .ok t' L' n ∧ L' "dn" = b2n stop ∧ n ≤ D

/-- A round's Level F outcome: stop (`done`) or go on (`yield`). -/
def resOut (stop : Bool) : ForInStep (Option Unit × Unit) :=
  if stop then .done (some (), ()) else .yield (none, ())

theorem reservationS_agree (κ : Caps) (s : Core) (L : Loc) {D : Nat}
    (I : Nat → Core → Prop) (h0 : I 0 s)
    (hstep : ∀ j t, I j t → j < s.P.K_R → ∃ stop t', (resF j ((none : Option Unit), ())).run t = .ok (resOut stop) t' ∧
      (stop = false → I (j + 1) t') ∧ ResAgree κ t t' stop D) :
    ∃ t' L' n, (reservation s.P.K_R).run s = .ok () t' ∧ evalF κ reservationS s L = .ok t' L' n ∧
      n ≤ 5 + s.P.K_R * (D + 6) := by
  set K := s.P.K_R
  set R := fun (l : List Nat) (t : Core) => (forIn l ((none : Option Unit), ()) resF).run t
  -- Level F's loop ends
  have hF : ∀ (n j : Nat) (t : Core), I j t → j + n = K →
      ∃ c tF, R ((List.range K).drop j) t = .ok c tF := by
    intro n; induction n with
    | zero =>
      intro j t _ hj; refine ⟨(none, ()), t, ?_⟩
      simp only [R, show j = K by omega]; rw [List.drop_of_length_le (by simp)]; rfl
    | succ n ih =>
      intro j t hI hj
      have hjK : j < K := by omega
      rw [List.drop_eq_getElem_cons (by simpa using hjK), List.getElem_range]
      obtain ⟨stop, t', hr, hI', -⟩ := hstep j t hI hjK
      cases stop
      · obtain ⟨c, tF, h⟩ := ih (j + 1) t' (hI' rfl) (by omega)
        exact ⟨c, tF, by simp only [R, List.forIn_cons, OM.Proof.run_bind, hr, resOut]; exact h⟩
      · exact ⟨_, _, by simp only [R, List.forIn_cons, OM.Proof.run_bind, hr, resOut]; rfl⟩
  obtain ⟨c0, tF, hR0⟩ := hF K 0 s h0 (by omega)
  simp only [List.drop_zero] at hR0
  have hFrun : (reservation s.P.K_R).run s = .ok () tF := by
    rw [reservation_eq, OM.Proof.run_bind]
    have hR0' : (forIn (List.range s.P.K_R) ((none : Option Unit), ()) resF).run s = .ok c0 tF := hR0
    rw [hR0']
    dsimp only
    split <;> rfl
  -- Level M's loop
  have a1 := evalF_assign_ok (κ := κ) (s := s) (L := L) (x := "dn") (e := (0 : Exp)) (v := 0) rfl
  obtain ⟨S', L', c, he, hc, hI⟩ := evalF_loop (κ := κ) (x := "ri") (n := .prm .KR) (b := resBody) (s := s)
    (L := upd L "dn" 0) (N := K) (by simp [Exp.ev, PF.get, K])
    (fun j S L' => (L' "dn" = 0 ∧ I j S ∧ ∃ c, R ((List.range K).drop j) S = .ok c tF) ∨
      (L' "dn" = 1 ∧ S = tF)) (D + 5)
    (Or.inl ⟨by simp [OM.Machine.State.upd], h0, c0, by simpa using hR0⟩)
    (by
      intro j hj S L1 hcase
      set L2 := upd L1 "ri" j
      rcases hcase with ⟨hdn, hIj, c1, hR⟩ | ⟨hdn, hSF⟩
      · have h2dn : L2 "dn" = 0 := by simp [L2, OM.Machine.State.upd, hdn]
        obtain ⟨stop, t', hr, hI', hRA⟩ := hstep j S hIj hj
        obtain ⟨L3, n3, e3, h3dn, hn3⟩ := hRA L2 h2dn
        rw [List.drop_eq_getElem_cons (by simpa using hj), List.getElem_range] at hR
        cases stop
        · simp only [R, List.forIn_cons, OM.Proof.run_bind, hr, resOut] at hR
          exact ⟨t', L3, n3, e3, by omega, Or.inl ⟨by simpa [b2n] using h3dn, hI' rfl, c1, hR⟩⟩
        · simp only [R, List.forIn_cons, OM.Proof.run_bind, hr, resOut] at hR
          injection hR with _ hT; subst hT
          exact ⟨t', L3, n3, e3, by omega, Or.inr ⟨by simpa [b2n] using h3dn, rfl⟩⟩
      · subst hSF
        have hc0 : ("dn" =ₑ 0 : Exp).ev κ S L2 = some 0 := by simp [Exp.ev, OM.Machine.BinOp.eval, L2,
          OM.Machine.State.upd, hdn]
        exact ⟨S, L2, _, evalF_ite_f hc0 evalF_skip, by simp [Exp.cost],
          Or.inr ⟨by simp [L2, OM.Machine.State.upd, hdn], rfl⟩⟩)
  have hS' : S' = tF := by
    rcases hI with ⟨hdn, hIK, c2, hR⟩ | ⟨hdn, h⟩
    · rw [List.drop_of_length_le (by simp)] at hR
      simp only [R] at hR
      injection hR
    · exact h
  subst hS'
  refine ⟨S', L', _, hFrun, evalF_seq_ok2 a1 he, ?_⟩
  have e : K * (1 + (D + 5)) = K * (D + 6) := by ring
  simp only [Exp.cost] at hc ⊢; omega

end OM.Impl
