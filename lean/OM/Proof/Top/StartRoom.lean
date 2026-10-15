import OM.Proof.Top.StartCount

/-!
# M5: room for `v1`, `v2` in the tables holding `v`
-/

namespace OM.Proof.Top

open OM.Model OM.Proof

set_option linter.deprecated false

/-- **Every node serves at most `Π_h`.** -/
theorem ew_le_any {s : TS} {cl : List Nat} {ord : Nat → List Nat} {oj : Option Job} (S : Shape s cl ord)
    (Ti : Timing s cl oj) (hTP : TopParams s.P) (hcap : cl.length + 2 ≤ Wd s.P (s.P.H - 1)) {T : Nat}
    (hT : isN s T) : ew s cl T ≤ Pid s.P (ht s T) := by
  by_cases hd : (nd s T).draining = true
  · exact Ti.ew_le hTP ⟨hT, hd⟩
  · have hl : liveN s T := ⟨hT, by simpa using hd⟩
    have hew : ew s cl T = tw s cl T := by unfold ew; rw [if_neg hd]
    rw [hew]
    obtain ⟨h1, hH⟩ := S.htN T hT
    by_cases hs : srcOf s T = NIL
    · by_cases hp : (nd s T).livePar = NIL
      · -- the root
        have hroot : ht s T = s.P.H := by
          by_contra h; exact (S.up T hl (by omega)).1.1.1 hp
        have := tw_le (s := s) cl T
        have ha : 2 ≤ s.P.a := by have := hTP.lamK 1 le_rfl; simp [lamd] at this; omega
        have hw : Wd s.P (s.P.H - 1) ≤ Wd s.P s.P.H := by
          unfold Wd; have := Nat.pow_le_pow_right (show 1 ≤ s.P.a by omega) (show s.P.H - 1 ≤ s.P.H by omega)
          omega
        rw [hroot]; unfold Pid; omega
      · have := Ti.wA T hl hp hs
        have hw := Ti.wts T hl
        unfold Pid; split at hw <;> omega
    · obtain ⟨hg, htg⟩ := S.src T hl hs
      generalize srcOf s T = g at hg htg
      have hle := Ti.ew_le hTP hg
      obtain ⟨-, -, hh1, hh2, -⟩ := S.ghost _ hg
      unfold ew at hle; rw [if_pos hg.2] at hle
      rcases htg with e | e
      · have : ht s T = ht s g := by rw [e]; exact hh1
        rw [this]; rw [← e] at hle; omega
      · have : ht s T = ht s g := by rw [e]; exact hh2
        rw [this]; rw [← e] at hle; omega

/-- **A table one level up has room on both sides of an entry.** -/
theorem room_up {s : TS} {cl : List Nat} {ord : Nat → List Nat} {dr n0 : Nat → Nat} {oj : Option Job}
    (hI : InvJ s cl ord dr n0 oj) (hTP : TopParams s.P) {e T : Nat} (he : isN s e) (hT : T ∈ (nd s e).inTables)
    (y z : Nat) :
    ∃ A le Bs, (nd s T).table = A ++ (e, le) :: Bs ∧ e ∉ A.map (·.1) ∧
      ((nd s T).draining = true → (lookup (nd s T).side e).isSome) ∧
      roomLo A le true < roomHi s.P.beta Bs le true ∧ roomLo A le false < roomHi s.P.beta Bs le false ∧
      2 ≤ gapB s.P.beta (n0 T) (dr T) ∧
      GapsGe s.P.beta (gapB s.P.beta (n0 T) (dr T) / 2)
        ((A ++ (y, (roomLo A le true + roomHi s.P.beta Bs le true - 1) / 2) :: (e, le) ::
          (z, (roomLo A le false + roomHi s.P.beta Bs le false - 1) / 2) :: Bs).map (·.2)) := by
  have S := hI.shape
  have Ti := hI.time
  have Ro := hI.room
  obtain ⟨h1, hH⟩ := S.htN e he
  have hent : Ent ord (ht s e) e := (S.ordMem _ h1 hH e).mpr ⟨he, rfl⟩
  have hT' : T ∈ tabs s (ht s e) e := by unfold tabs; rw [if_neg (by omega)]; exact hT
  obtain ⟨hTN, hTh, heT⟩ := (S.tabsIff _ e T hent).mp hT'
  obtain ⟨A, le, Bs, htab, hA⟩ := table_split (t := (nd s T).table) heT
  -- the insertion events of the table
  have hew := ew_le_any S Ti hTP hI.cap hTN
  have hg1 := hTP.gam1 (ht s T - 1) (by omega)
  have hp := Ro.pot2 T hTN (by omega)
  have hn0 := Ro.n0le T hTN
  have hc : 1 ≤ (if s.P.H < T then lamd s.P (ht s T) else 1) := by
    split
    · have := hTP.lamK (ht s T) (by omega); omega
    · exact le_rfl
  have hdr : dr T + 1 ≤ Dmax s.P (ht s T) := by
    unfold Dmax; rw [if_neg (by omega)]
    set g := gamd s.P (ht s T - 1)
    have key : g * dr T + 1 ≤ Pid s.P (ht s T) + g * n0 T := by omega
    by_cases hdn : dr T ≤ n0 T
    · generalize Pid s.P (ht s T) / g = q; omega
    · have : dr T - n0 T ≤ Pid s.P (ht s T) / g := by
        rw [Nat.le_div_iff_mul_le (by omega), Nat.mul_comm, Nat.mul_sub]
        omega
      generalize Pid s.P (ht s T) / g = q at this; omega
  have hB := gap_two hn0 hdr (hTP.room _ (by omega))
  have hg := Ro.gaps T hTN
  unfold labs at hg; rw [htab] at hg
  obtain ⟨r1, r2, r3⟩ := gaps_room_around (y := y) (z := z) hB hg
  refine ⟨A, le, Bs, htab, hA, fun hd => ?_, r1, r2, hB, r3⟩
  have := S.side T ⟨hTN, hd⟩ e heT
  rw [this]; rfl

end OM.Proof.Top
