import OM.Proof.Top.InsViews

/-!
# M5: a chunk split keeps the invariant (the contract's `start`)

`insertAround x y z` on the linked core succeeds, writes tags that pass their guards, and the top
structure with the job's path copy completed satisfies the invariant, with the job at its start.
-/

namespace OM.Proof.Top

open OM.Model OM.Proof

set_option linter.deprecated false

/-! ### Room for an insertion event -/

theorem gap_two {β n0 dr D nmax : Nat} (hn0 : n0 ≤ nmax) (hdr : dr + 1 ≤ D)
    (hroom : 2 ^ D * (nmax + 1) ≤ 2 ^ β) : 2 ≤ gapB β n0 dr := by
  unfold gapB
  have h1 : 2 ^ (dr + 1) * (n0 + 1) ≤ 2 ^ β := by
    calc 2 ^ (dr + 1) * (n0 + 1) ≤ 2 ^ D * (nmax + 1) :=
          Nat.mul_le_mul (Nat.pow_le_pow_right (by norm_num) hdr) (by omega)
      _ ≤ 2 ^ β := hroom
  have h2 : 2 ^ (dr + 1) ≤ 2 ^ β / (n0 + 1) := by
    rw [Nat.le_div_iff_mul_le (by omega)]; exact h1
  rw [Nat.le_div_iff_mul_le (by positivity)]
  calc 2 * 2 ^ dr = 2 ^ (dr + 1) := by ring
    _ ≤ 2 ^ β / (n0 + 1) := h2

/-! ### Between jobs -/

section between
variable {s : TS} {cl : List Nat} {ord : Nat → List Nat} (S : Shape s cl ord) (Ti : Timing s cl none)
include S Ti

/-- Between jobs, a running drain has had fewer than `K_h` funding jobs. -/
theorem Timing.fund_lt (hTP : TopParams s.P) {v : Nat} (hg : ghostN s v) :
    fundOf s cl v + 1 ≤ Kd s.P (ht s v) := by
  have h1 := Ti.wC v hg
  have h2 := (Ti.wB v hg).2
  have hs := hTP.s3
  simp only [slack, Nat.add_zero] at h1
  unfold Kd
  have : fundOf s cl v ≤ (Wd s.P (ht s v) + 2) / (s.P.s - 2) := by
    rw [Nat.le_div_iff_mul_le (by omega), Nat.mul_comm]; omega
  omega

/-- Between jobs, a live non-root node weighs at most `W_h`. -/
theorem Timing.tw_live (hTP : TopParams s.P) {u : Nat} (hu : liveN s u)
    (hp : (nd s u).livePar ≠ NIL) : tw s cl u ≤ Wd s.P (ht s u) := by
  have hw := Ti.wts u hu
  simp only [pend, List.not_mem_nil, if_false, Nat.add_zero] at hw
  rw [← hw]
  by_cases hs : srcOf s u = NIL
  · exact Ti.wA u hu hp hs
  · obtain ⟨hg, htg⟩ := S.src u hu hs
    generalize hgv : srcOf s u = g at hg htg
    obtain ⟨-, -, hh1, hh2, -⟩ := S.ghost _ hg
    have := Ti.release S hTP hg htg (by simp [pend])
    have hhu : ht s u = ht s g := by rcases htg with e | e <;> rw [e] <;> assumption
    rw [hhu]; exact this

end between

/-! ### The split's tables have room -/

theorem table_split {t : List (Nat × Nat)} {e : Nat} (he : e ∈ t.map (·.1)) :
    ∃ A le Bs, t = A ++ (e, le) :: Bs ∧ e ∉ A.map (·.1) := by
  induction t with
  | nil => simp at he
  | cons p r ih =>
    obtain ⟨k, l⟩ := p
    by_cases hk : k = e
    · subst hk; exact ⟨[], l, r, rfl, by simp⟩
    · have he' : e ∈ r.map (·.1) := by simp at he ⊢; rcases he with h | h <;> [exact absurd h.symm hk; exact h]
      obtain ⟨A, le, Bs, h1, h2⟩ := ih he'
      exact ⟨(k, l) :: A, le, Bs, by simp [h1], by simp [h2, Ne.symm hk]⟩

/-- **The tables of the split chunk have room on both sides of it.** -/
theorem start_room {s : TS} {cl : List Nat} {ord : Nat → List Nat} {dr n0 : Nat → Nat}
    (hI : InvJ s cl ord dr n0 none) (hTP : TopParams s.P) {x T : Nat} (hx : x ∈ cl)
    (hT : T ∈ cinT s x) (y z : Nat) :
    ∃ A le Bs, (nd s T).table = A ++ (x, le) :: Bs ∧ x ∉ A.map (·.1) ∧
      ((nd s T).draining = true → (lookup (nd s T).side x).isSome) ∧
      roomLo A le true < roomHi s.P.beta Bs le true ∧ roomLo A le false < roomHi s.P.beta Bs le false ∧
      GapsGe s.P.beta (gapB s.P.beta (n0 T) (dr T) / 2)
        ((A ++ (y, (roomLo A le true + roomHi s.P.beta Bs le true - 1) / 2) :: (x, le) ::
          (z, (roomLo A le false + roomHi s.P.beta Bs le false - 1) / 2) :: Bs).map (·.2)) := by
  have S := hI.shape
  have Ti := hI.time
  have Ro := hI.room
  have hent : Ent ord 0 x := by unfold Ent; rw [S.ord0]; exact hx
  have hT' : T ∈ tabs s 0 x := by unfold tabs; rw [if_pos rfl]; exact hT
  obtain ⟨hTN, hTh, hxT⟩ := (S.tabsIff 0 x T hent).mp hT'
  simp only [Nat.zero_add] at hTh
  obtain ⟨A, le, Bs, htab, hA⟩ := table_split (t := (nd s T).table) hxT
  -- the drain bound of the table
  have hew : ew s cl T + 2 ≤ Pid s.P 1 := by
    obtain ⟨hl, hlh, -⟩ := S.lp x hx
    have hpar : par s 0 x = lpr s x := by simp [par]
    rcases S.Q 0 x T hent hT' with h | h <;> rw [hpar] at h
    · subst h
      obtain ⟨hpl, -, -⟩ := S.up _ hl (by have := S.H3; omega)
      have hw := Ti.tw_live S hTP hl (fun e => hpl.1.1 e)
      have : ew s cl (lpr s x) = tw s cl (lpr s x) := by unfold ew; rw [if_neg (by rw [hl.2]; simp)]
      rw [this]; rw [hlh] at hw; unfold Pid; omega
    · have hsn : srcOf s (lpr s x) ≠ NIL := fun e => hTN.1 (h.trans e)
      obtain ⟨hg, -⟩ := S.src _ hl hsn
      rw [← h] at hg
      have hf := Ti.fund_lt S hTP hg
      have hF := Ti.wF T hg
      have hB := (Ti.wB T hg).2
      rw [hTh] at hf hB
      unfold fundOf at hf
      unfold Pid; omega
  have hdr : dr T + 1 ≤ Dmax s.P 1 := by
    have hp := Ro.pot1 T hTN hTh
    unfold Dmax; simp only [le_refl, if_true]; omega
  have hB := gap_two (Ro.n0le T hTN) hdr (by have := hTP.room 1 le_rfl; rw [hTh]; exact this)
  have hg := Ro.gaps T hTN
  unfold labs at hg; rw [htab] at hg
  obtain ⟨r1, r2, r3⟩ := gaps_room_around (y := y) (z := z) hB hg
  refine ⟨A, le, Bs, htab, hA, fun hd => ?_, r1, r2, r3⟩
  have := S.side T ⟨hTN, hd⟩ x hxT
  rw [this]; rfl

end OM.Proof.Top
