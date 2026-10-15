import OM.Proof.Top.RunFinish
import OM.Proof.Top.PresDrain

/-!
# M5: the end of a drain keeps the invariant

A sweep call on a ghost `v` with an empty range removes `v` from every table, releases its targets
and marks it dead. The order loses `v`; nothing referred to it any more, since no path passes
through it. The released targets weigh at most `W_h` (Lemma T3, under `2 + 2K_h ≤ λ_h`).
-/

namespace OM.Proof.Top

open OM.Model OM.Proof

set_option linter.deprecated false

/-! ### Removing an entry from a table -/

theorem assocErase_keys {β : Type} (t : List (Nat × β)) (v : Nat) (h : (t.map (·.1)).Nodup) :
    (assocErase t v).map (·.1) = (t.map (·.1)).erase v := by
  unfold assocErase
  induction t with
  | nil => rfl
  | cons p t ih =>
    obtain ⟨k, b⟩ := p
    simp only [List.map_cons, List.nodup_cons] at h
    simp only [List.filter_cons, List.map_cons]
    by_cases hk : k = v
    · subst hk
      simp only [bne_self_eq_false, Bool.false_eq_true, if_false, List.erase_cons_head]
      have : (t.filter (fun x => x.1 != k)) = t := List.filter_eq_self.mpr fun q hq => by
        simp only [bne_iff_ne, ne_eq]; intro e
        exact h.1 (e ▸ List.mem_map_of_mem (f := fun x => x.1) hq)
      rw [this]
    · simp only [show (k != v) = true by simpa using hk, if_true, List.map_cons]
      rw [List.erase_cons_tail (by simpa using hk), ih h.2]

theorem lookup_assocErase {β : Type} (t : List (Nat × β)) (v e : Nat) (he : e ≠ v) :
    lookup (assocErase t v) e = lookup t e := by
  unfold assocErase lookup
  induction t with
  | nil => rfl
  | cons p t ih =>
    obtain ⟨k, b⟩ := p
    simp only [List.filter_cons, List.find?_cons]
    by_cases hk : k = v
    · subst hk
      simp only [bne_self_eq_false, Bool.false_eq_true, if_false]
      rw [ih, show (k == e) = false by simpa using Ne.symm he]
    · simp only [show (k != v) = true by simpa using hk, if_true, List.find?_cons]
      split <;> simp_all

theorem gapsGe_sublist {β B : Nat} {ls ls' : List Nat} (h : GapsGe β B ls) (hs : ls'.Sublist ls) :
    GapsGe β B ls' := by
  unfold GapsGe at *
  have htr : IsTrans Nat (fun a b => a + B ≤ b) := ⟨fun a b c h1 h2 => by omega⟩
  rw [List.isChain_iff_pairwise] at *
  refine List.Pairwise.sublist ?_ h
  exact List.Sublist.cons_cons 0 (List.Sublist.append (hs.map _) (List.Sublist.refl _))

theorem gapsGe_assocErase {β B : Nat} {t : List (Nat × Nat)} (v : Nat)
    (h : GapsGe β B (t.map (·.2))) : GapsGe β B ((assocErase t v).map (·.2)) :=
  gapsGe_sublist h ((List.filter_sublist).map _)

/-! ### The views after the drain ends -/

/-- What changes when ghost `v` ends: `v` dies and leaves every table; its targets are released. -/
structure FinFrame (s s' : TS) (v : Nat) : Prop where
  P : s'.P = s.P
  size : s'.nodes.size = s.nodes.size
  path : s'.path = s.path
  lpar : s'.lpar = s.lpar
  tag : s'.tag = s.tag
  resJob : s'.resJob = s.resJob
  node : ∀ u, nd s' u = { nd s u with
    alive := if u = v then false else (nd s u).alive,
    table := if u ∈ (nd s v).inTables then assocErase (nd s u).table v else (nd s u).table,
    side := if u ∈ (nd s v).inTables then assocErase (nd s u).side v else (nd s u).side,
    inTables := if u = v then [] else if u ∈ order s v ∧ ht s v - 1 ≠ 0 then (nd s u).inTables.erase v
      else (nd s u).inTables,
    overflowOf := if (u = (nd s v).t1 ∨ u = (nd s v).t2) ∧ (nd s u).overflowOf = v then NIL
      else (nd s u).overflowOf }
  cin : ∀ e, cinT s' e = if ht s v - 1 = 0 ∧ e ∈ order s v then (cinT s e).erase v else cinT s e

theorem foldl_dropEntryS_rest (v : Nat) (l : List Nat) (s : Core) :
    (l.foldl (dropEntryS v) s).cin = s.cin ∧ (l.foldl (dropEntryS v) s).path = s.path ∧
      (l.foldl (dropEntryS v) s).lpar = s.lpar ∧ (l.foldl (dropEntryS v) s).P = s.P ∧
      (l.foldl (dropEntryS v) s).C = s.C ∧ (l.foldl (dropEntryS v) s).resJob = s.resJob ∧
      (l.foldl (dropEntryS v) s).nodes.size = s.nodes.size := by
  induction l generalizing s with
  | nil => simp
  | cons x t ih =>
    obtain ⟨h1, h2, h3, h4, h5, h6, h7⟩ := ih (dropEntryS v s x)
    simp only [List.foldl_cons]
    exact ⟨h1, h2, h3, h4, h5, h6, by rw [h7]; simp [dropEntryS]⟩

theorem fdS_rest (v : Nat) (s : Core) (hno : (s.nodes.getX v).order.Nodup) :
    (∀ e, (fdS v s).cin.getX e =
      if e ∈ (s.nodes.getX v).order ∧ (s.nodes.getX v).height - 1 = 0 then (s.cin.getX e).erase v
      else s.cin.getX e) ∧
    (fdS v s).path = s.path ∧ (fdS v s).lpar = s.lpar ∧ (fdS v s).P = s.P ∧ (fdS v s).C = s.C ∧
    (fdS v s).resJob = s.resJob ∧ (fdS v s).nodes.size = s.nodes.size := by
  obtain ⟨d1, d2, d3, d4, d5, d6, d7, d8⟩ := foldl_dropTableS v ((s.nodes.getX v).height - 1) _ hno s
  obtain ⟨e1, e2, e3, e4, e5, e6, e7⟩ := foldl_dropEntryS_rest v (s.nodes.getX v).inTables (fd1 v s)
  have r1 := releaseS_rest v (fd2 v s) (s.nodes.getX v).t1
  have r2 := releaseS_rest v (releaseS v (fd2 v s) (s.nodes.getX v).t1) (s.nodes.getX v).t2
  have hf2 : (fd2 v s).cin = (fd1 v s).cin ∧ (fd2 v s).path = s.path ∧ (fd2 v s).lpar = s.lpar ∧
      (fd2 v s).P = s.P ∧ (fd2 v s).C = s.C ∧ (fd2 v s).resJob = s.resJob ∧
      (fd2 v s).nodes.size = s.nodes.size := by
    unfold fd2; exact ⟨e1, e2.trans d4, e3.trans d5, e4.trans d6, e5.trans d7, e6.trans d8, e7.trans d2⟩
  have hf4 : (fd4 v s).cin = (fd1 v s).cin ∧ (fd4 v s).path = s.path ∧ (fd4 v s).lpar = s.lpar ∧
      (fd4 v s).P = s.P ∧ (fd4 v s).C = s.C ∧ (fd4 v s).resJob = s.resJob ∧
      (fd4 v s).nodes.size = s.nodes.size := by
    unfold fd4
    exact ⟨r2.1.trans (r1.1.trans hf2.1), r2.2.1.trans (r1.2.1.trans hf2.2.1),
      r2.2.2.1.trans (r1.2.2.1.trans hf2.2.2.1), r2.2.2.2.1.trans (r1.2.2.2.1.trans hf2.2.2.2.1),
      r2.2.2.2.2.1.trans (r1.2.2.2.2.1.trans hf2.2.2.2.2.1),
      r2.2.2.2.2.2.trans (r1.2.2.2.2.2.trans hf2.2.2.2.2.2.1),
      by rw [releaseS_size, releaseS_size]; exact hf2.2.2.2.2.2.2⟩
  have hc : (fdS v s).cin = (fd4 v s).cin := by simp only [fdS]
  refine ⟨fun e => ?_, by simp only [fdS]; exact hf4.2.1, by simp only [fdS]; exact hf4.2.2.1,
    by simp only [fdS]; exact hf4.2.2.2.1, by simp only [fdS]; exact hf4.2.2.2.2.1,
    by simp only [fdS]; exact hf4.2.2.2.2.2.1, by simp only [fdS]; rw [Array.size_modify']; exact hf4.2.2.2.2.2.2⟩
  rw [hc, hf4.1]
  unfold fd1; rw [d3 e]

attribute [local irreducible] fdS

section fin
variable {s : Core} {cl : List Nat} {ord : Nat → List Nat} (S : Shape (ts s) cl ord) {v : Nat}
  (hg : ghostN (ts s) v)
include S hg

theorem Shape.fin_facts :
    v < s.nodes.size ∧ (nd (ts s) v).order.Nodup ∧ (nd (ts s) v).inTables.Nodup ∧ ((nd (ts s) v).height - 1 ≠ 0 → v ∉ (nd (ts s) v).order) ∧
      v ∉ (nd (ts s) v).inTables ∧ v ≠ (nd (ts s) v).t1 ∧ v ≠ (nd (ts s) v).t2 ∧ (nd (ts s) v).t1 ≠ (nd (ts s) v).t2 ∧ ((nd (ts s) v).height - 1 ≠ 0 → (nd (ts s) v).t1 ∉ (nd (ts s) v).order) ∧
      ((nd (ts s) v).height - 1 ≠ 0 → (nd (ts s) v).t2 ∉ (nd (ts s) v).order) ∧ (nd (ts s) v).t1 ∉ (nd (ts s) v).inTables ∧ (nd (ts s) v).t2 ∉ (nd (ts s) v).inTables ∧
      (∀ u, u ∈ (nd (ts s) v).order → (nd (ts s) v).height - 1 ≠ 0 → u ∉ (nd (ts s) v).inTables) ∧
      (∀ u ∈ (nd (ts s) v).inTables, isN (ts s) u ∧ ht (ts s) u = ht (ts s) v + 1) ∧
      (∀ u ∈ (nd (ts s) v).order, (nd (ts s) v).height - 1 ≠ 0 → isN (ts s) u ∧ ht (ts s) u = ht (ts s) v - 1) := by
  obtain ⟨hl1, hl2, hh1, hh2, -, -, -, -, -, hlt, -⟩ := S.ghost v hg
  obtain ⟨hv1, hvH⟩ := S.htN v hg.1
  have hvent : Ent ord (ht (ts s) v) v := (S.ordMem _ hv1 hvH v).mpr ⟨hg.1, rfl⟩
  have htabs : tabs (ts s) (ht (ts s) v) v = (nd (ts s) v).inTables := by
    unfold tabs; rw [if_neg (by omega)]
  have hin : ∀ u ∈ (nd (ts s) v).inTables, isN (ts s) u ∧ ht (ts s) u = ht (ts s) v + 1 := fun u hu => by
    rw [← htabs] at hu; obtain ⟨h1, h2, -⟩ := (S.tabsIff _ v u hvent).mp hu; exact ⟨h1, h2⟩
  have hent : ∀ u ∈ (nd (ts s) v).order, (nd (ts s) v).height - 1 ≠ 0 → isN (ts s) u ∧ ht (ts s) u = ht (ts s) v - 1 :=
    fun u hu h0 => by
      have := S.tabEnt v hg.1 u hu
      have h0' : ht (ts s) v - 1 ≠ 0 := h0
      exact (S.ordMem _ (by omega) (by omega) u).mp this
  have h12 := S.t1_ne_t2 hg
  refine ⟨hg.1.2.1, S.order_nodup hg.1, by rw [← htabs]; exact S.tabsNodup _ v hvent,
    fun h0 hm => ?_, fun hm => ?_, fun e => ?_, fun e => ?_, h12, fun h0 hm => ?_, fun h0 hm => ?_,
    fun hm => ?_, fun hm => ?_, fun u hu h0 hm => ?_, hin, hent⟩
  · have := (hent v hm h0).2; simp only [ht] at this hv1; omega
  · have := (hin v hm).2; omega
  · rw [e] at hg; exact absurd hg.2 (by rw [hl1.2]; simp)
  · rw [e] at hg; exact absurd hg.2 (by rw [hl2.2]; simp)
  · have := (hent _ hm h0).2; rw [hh1] at this; simp only [ht] at this hv1; omega
  · have := (hent _ hm h0).2; rw [hh2] at this; simp only [ht] at this hv1; omega
  · have := (hin _ hm).2; rw [hh1] at this; omega
  · have := (hin _ hm).2; rw [hh2] at this; omega
  · have h1 := (hin u hm).2; have h2 := (hent u hu h0).2; omega

/-- **The views after the drain ends.** -/
theorem Shape.fin_frame : FinFrame (ts s) (ts (fdS v s)) v := by
  obtain ⟨hv, hno, hni, hvo, hvi, h1, h2, h12, ho1, ho2, hi1, hi2, hoi, hin, hent⟩ := S.fin_facts hg
  obtain ⟨hc, hp, hl, hP, hC, hr, hsz⟩ := fdS_rest v s hno
  refine ⟨hP, hsz, hp, hl, by unfold ts; simp only [hC], hr, fun u => ?_, fun e => ?_⟩
  · show (fdS v s).nodes.getX u = _
    rw [fdS_getX v s hv hno hni hvo hvi h1 h2 h12 ho1 ho2 hi1 hi2 hoi u]
    by_cases huv : u = v
    · subst huv
      have : ¬ (u = (s.nodes.getX u).t1 ∨ u = (s.nodes.getX u).t2) := by
        rintro (e | e); exact h1 e; exact h2 e
      have hvi' : u ∉ (s.nodes.getX u).inTables := hvi
      simp [hvi', this, nd, ts]
    · rw [if_neg huv]
      by_cases hu1 : u ∈ (s.nodes.getX v).order ∧ (s.nodes.getX v).height - 1 ≠ 0
      · have hus : u < s.nodes.size := (hent u hu1.1 hu1.2).1.2.1
        have hi : u ∉ (s.nodes.getX v).inTables := hoi u hu1.1 hu1.2
        have hn1 : u ≠ (s.nodes.getX v).t1 := fun e => ho1 hu1.2 (e ▸ hu1.1)
        have hn2 : u ≠ (s.nodes.getX v).t2 := fun e => ho2 hu1.2 (e ▸ hu1.1)
        rw [if_pos ⟨hu1.1, hu1.2, hus⟩]
        simp only [order, ht, nd, ts] at hu1 ⊢
        simp [huv, hi, hn1, hn2, hu1]
      · rw [if_neg (fun h => hu1 ⟨h.1, h.2.1⟩)]
        by_cases hu2 : u ∈ (s.nodes.getX v).inTables
        · have hus : u < s.nodes.size := (hin u hu2).1.2.1
          have hn1 : u ≠ (s.nodes.getX v).t1 := fun e => hi1 (e ▸ hu2)
          have hn2 : u ≠ (s.nodes.getX v).t2 := fun e => hi2 (e ▸ hu2)
          rw [if_pos ⟨hu2, hus⟩]
          simp only [order, ht, nd, ts] at hu1 ⊢
          simp [huv, hu2, hn1, hn2, hu1]
        · rw [if_neg (fun h => hu2 h.1)]
          simp only [order, ht, nd, ts] at hu1 ⊢
          by_cases hu3 : (u = (s.nodes.getX v).t1 ∨ u = (s.nodes.getX v).t2) ∧
              (s.nodes.getX u).overflowOf = v
          · have hus : u < s.nodes.size := by
              obtain ⟨hl1, hl2, -⟩ := S.ghost v hg
              rcases hu3.1 with e | e <;> rw [e] <;> [exact hl1.1.2.1; exact hl2.1.2.1]
            rw [if_pos ⟨hu3.1, hu3.2, hus⟩]
            simp [huv, hu2, hu1, hu3]
          · rw [if_neg (fun h => hu3 ⟨h.1, h.2.1⟩)]
            simp [huv, hu2, hu1, hu3]
  · show (fdS v s).cin.getX e = _
    rw [hc e]
    unfold cinT order ht nd ts
    simp only [and_comm]

end fin

end OM.Proof.Top
