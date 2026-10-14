import OM.Proof.Cost.Game

/-!
# Lemma C3: group labels inside chunks (`docs/PROOF.md` §4.3)

A chunk's group labels change through split starts (a halving of each gap next to the splitting
group, or a push at an end of the chunk), group removals (two gaps merge), and chunk-split moves
(groups pushed at the receiving end; groups leaving at the other chunk's end).

The Lean proof counts all halvings of a chunk `X` in one ghost counter `hv X` (each split start
in `X` halves at most two gaps), instead of following each gap's halving history as `PROOF.md`
does. Split starts are bounded as in `PROOF.md`:

* **child splits** (`cs X`), by the charging argument of Claim 2: `cs X · g_min ≤ ins X ≤ I_C`;
* **root splits** (`rs X`): each root splits at most once, and the roots are the arrived groups
  and `X`'s first group;
* **arrivals** (`arB X`, `arF X`): the source chunk moves at most `units(s₀) + k_C` units, of at most
  three groups each.

Pushes are counted per end, as in `PROOF.md`. The coarser halving count needs a wider group label:
`B_g ≈ 30L` bits for the proof parameters instead of about `9L`, still `Θ(L)`.
-/

namespace OM.Proof

open OM.Model

set_option linter.deprecated false

/-! ### Constants -/

/-- Units a chunk-split source moves, at most: `units(T) + k_C(T)`. -/
def Mu (P : Params) : Nat := unitsOf P P.T + kC P P.T

/-- Insertions into a chunk over its life, at most: `T + 2 k_C(T)`. -/
def IC (P : Params) : Nat := P.T + 2 * kC P P.T

/-- Child splits in a chunk's life, at most. -/
def csB (P : Params) : Nat := IC P / gmin P

/-- Root splits in a chunk's life, at most. -/
def rsB (P : Params) : Nat := 3 * Mu P + 1

/-- Halvings in a chunk's life, at most. -/
def HC (P : Params) : Nat := 2 * (csB P + rsB P)

/-- Pushes at one end of a chunk, at most. -/
def PC (P : Params) : Nat := 3 * Mu P + rsB P + csB P

/-- The centre of the group label range. -/
def cG (P : Params) : Nat := 1 <<< (P.B_g - 1)

/-- The parameter conditions for group labels (I10, in the coarser form). -/
structure LParams (P : Params) : Prop where
  Dg : 1 ≤ P.D_g
  Bg : 1 ≤ P.B_g
  push : PC P * P.D_g < cG P
  halve : 2 ^ HC P ≤ P.D_g

/-! ### Ghost state -/

structure LGh where
  /-- A group created by a split start in its current chunk, and not moved since. -/
  child : Nat → Bool
  /-- Halvings, child splits, root splits, insertions of a chunk. -/
  hv : Nat → Nat
  cs : Nat → Nat
  rs : Nat → Nat
  ins : Nat → Nat
  /-- Pushes at the back and front, and groups arrived at the back and front. -/
  pb : Nat → Nat
  pf : Nat → Nat
  arB : Nat → Nat
  arF : Nat → Nat
  /-- The size of a quiet chunk when it became quiet. -/
  e0 : Nat → Nat

/-! ### Counts over the groups of a chunk -/

/-- The groups of chunk `c` (as indices). -/
def GrpsC (s : Core) (c : Nat) : Finset Nat :=
  (Finset.range s.Gs.size).filter fun g => LiveG s g ∧ gC s g = c

/-- Unsplit roots of chunk `c`: groups that are neither children nor splitting. -/
def pending (s : Core) (lg : LGh) (c : Nat) : Nat :=
  ((GrpsC s c).filter fun g => lg.child g = false ∧ gSt s g ≠ .splitting).card

/-- The charge waiting to be converted into child splits (Claim 2): a family whose children were
created in `c` carries its insertions, a quiet child carries its progress towards a split. -/
def charge (s : Core) (lg : LGh) (c : Nat) : Nat :=
  ∑ g ∈ GrpsC s c, (if gSt s g = .splitting ∧ lg.child (gLl s g) = true then famT s g - s.P.G
    else if gSt s g = .quiet ∧ lg.child g = true then gmin s.P + gSz s g - s.P.G else 0)

/-- The size of the family of a splitting chunk. -/
def famC (s : Core) (x : Nat) : Nat := cSz s (cLl s x) + cSz s x + cSz s (cRr s x)

/-! ### The invariant -/

structure LInv (s : Core) (lg : LGh) (s₀ δ δu : Nat → Nat) : Prop where
  /-- Gaps between consecutive groups of a chunk survive the chunk's halvings. -/
  gaps : ∀ g, LiveG s g → g ≠ cLs s (gC s g) →
    gL s g + s.P.D_g / 2 ^ lg.hv (gC s g) ≤ gL s (gN s g)
  /-- Labels stay within the pushes from the centre. -/
  range : ∀ g, LiveG s g →
    cG s.P ≤ gL s g + lg.pf (gC s g) * s.P.D_g ∧ gL s g ≤ cG s.P + lg.pb (gC s g) * s.P.D_g
  /-- Halvings and pushes, counted through split starts and arrivals. -/
  hv : ∀ c, lg.hv c ≤ 2 * (lg.cs c + lg.rs c)
  pb : ∀ c, lg.pb c ≤ lg.arB c + lg.rs c + lg.cs c
  pf : ∀ c, lg.pf c ≤ lg.arF c + lg.rs c + lg.cs c
  roots : ∀ c, LiveC s c → lg.rs c + pending s lg c ≤ lg.arB c + lg.arF c + 1
  /-- Claim 2: child splits, paid for by insertions. -/
  claim2 : ∀ c, LiveC s c → lg.cs c * gmin s.P + charge s lg c ≤ lg.ins c
  /-- Insertions by phase. -/
  insQ : ∀ c, LiveC s c → cSt s c = .quiet → lg.ins c + lg.e0 c ≤ cSz s c + kC s.P s.P.T
  insO : ∀ c, LiveC s c → cSt s c = .overflow → lg.ins c + s₀ (cSrc s c) ≤ famC s (cSrc s c)
  insS : ∀ c, LiveC s c → cSt s c = .splitting → lg.ins c ≤ famC s c + kC s.P s.P.T
  /-- Arrivals: a source's moved units, and the frozen total afterwards. -/
  arrS : ∀ x, LiveC s x → cSt s x = .splitting →
    lg.arB (cLl s x) + lg.arF (cLl s x) + lg.arB (cRr s x) + lg.arF (cRr s x) + 3 * units s x ≤
      3 * (unitsOf s.P (s₀ x) + ((cSz s (cLl s x) - δ (cLl s x)) + (cSz s x - δ x) +
        (cSz s (cRr s x) - δ (cRr s x)) - s₀ x)) + 3 * δu x
  arrN : ∀ c, LiveC s c → cSt s c ≠ .overflow → lg.arB c + lg.arF c ≤ 3 * Mu s.P
  /-- The quiet size at the start of the quiet period. -/
  e0 : ∀ c, LiveC s c → cSt s c = .quiet → lg.e0 c ≤ cSz s c
  /-- The two siblings of a family are children of the same split, or both arrived. -/
  famChild : ∀ p, LiveG s p → gSt s p = .splitting → lg.child (gLl s p) = lg.child (gRr s p)

end OM.Proof

namespace OM.Proof

open OM.Model

set_option linter.deprecated false

/-! ### The labels of a split start -/

theorem labBefore_val {s : Core} {g lab : Nat} (h : (labBefore g).run s = .ok lab s) :
    lab = if g = cF s (gC s g) then gL s g - s.P.D_g else (gL s (gP s g) + gL s g) / 2 := by
  unfold labBefore at h
  simp only [run_getP_bind, run_getG_bind, run_getC_bind] at h
  by_cases hf : g = (s.C.getX (s.Gs.getX g).chk).first
  · rw [if_pos (beq_iff_eq.mpr hf), run_before] at h
    simp only [cF, gC, gL] at hf ⊢; rw [if_pos hf]
    split at h
    · cases h
    · cases h; rfl
  · rw [if_neg (fun e => hf (beq_iff_eq.mp e))] at h
    simp only [run_getG_bind, run_between] at h
    simp only [cF, gC, gL, gP] at hf ⊢; rw [if_neg hf]
    split at h
    · cases h
    · cases h; rfl

theorem labAfter_val {s : Core} {g lab : Nat} (h : (labAfter g).run s = .ok lab s) :
    lab = if g = cLs s (gC s g) then gL s g + s.P.D_g else (gL s g + gL s (gN s g)) / 2 := by
  unfold labAfter at h
  simp only [run_getP_bind, run_getG_bind, run_getC_bind] at h
  by_cases hf : g = (s.C.getX (s.Gs.getX g).chk).last
  · rw [if_pos (beq_iff_eq.mpr hf), run_after] at h
    simp only [cLs, gC, gL] at hf ⊢; rw [if_pos hf]
    split at h
    · cases h
    · cases h; rfl
  · rw [if_neg (fun e => hf (beq_iff_eq.mp e))] at h
    simp only [run_getG_bind, run_between] at h
    simp only [cLs, gC, gL, gN] at hf ⊢; rw [if_neg hf]
    split at h
    · cases h
    · cases h; rfl

/-- The guard conditions of `labBefore`, when it succeeds. -/
theorem labBefore_guard {s : Core} {g lab : Nat} (h : (labBefore g).run s = .ok lab s) :
    (g = cF s (gC s g) → s.P.D_g ≤ gL s g ∧ s.P.D_g ≠ 0) ∧
    (g ≠ cF s (gC s g) → gL s (gP s g) + 1 < gL s g) := by
  unfold labBefore at h
  simp only [run_getP_bind, run_getG_bind, run_getC_bind] at h
  by_cases hf : g = (s.C.getX (s.Gs.getX g).chk).first
  · rw [if_pos (beq_iff_eq.mpr hf), run_before] at h
    simp only [cF, gC, gL] at hf ⊢
    refine ⟨fun _ => ?_, fun h' => absurd hf h'⟩
    split at h
    · cases h
    · next hg => simp only [not_or] at hg; omega
  · rw [if_neg (fun e => hf (beq_iff_eq.mp e))] at h
    simp only [run_getG_bind, run_between] at h
    simp only [cF, gC, gL, gP] at hf ⊢
    refine ⟨fun h' => absurd h' hf, fun _ => ?_⟩
    split at h
    · cases h
    · omega

theorem labAfter_guard {s : Core} {g lab : Nat} (h : (labAfter g).run s = .ok lab s) :
    (g = cLs s (gC s g) → gL s g + s.P.D_g < 1 <<< s.P.B_g ∧ s.P.D_g ≠ 0) ∧
    (g ≠ cLs s (gC s g) → gL s g + 1 < gL s (gN s g)) := by
  unfold labAfter at h
  simp only [run_getP_bind, run_getG_bind, run_getC_bind] at h
  by_cases hf : g = (s.C.getX (s.Gs.getX g).chk).last
  · rw [if_pos (beq_iff_eq.mpr hf), run_after] at h
    simp only [cLs, gC, gL] at hf ⊢
    refine ⟨fun _ => ?_, fun h' => absurd hf h'⟩
    split at h
    · cases h
    · next hg => simp only [not_or] at hg; omega
  · rw [if_neg (fun e => hf (beq_iff_eq.mp e))] at h
    simp only [run_getG_bind, run_between] at h
    simp only [cLs, gC, gL, gN] at hf ⊢
    refine ⟨fun h' => absurd h' hf, fun _ => ?_⟩
    split at h
    · cases h
    · omega

end OM.Proof

namespace OM.Proof

open OM.Model

set_option linter.deprecated false

/-! ### Across a split start -/

/-- The ghost update of a split start of `g` (new groups `gl`, `gr`, in chunk `c`). -/
def LGh.split (lg : LGh) (s : Core) (g gl gr : Nat) : LGh :=
  let c := gC s g
  { lg with
    child := fun z => if z = gl ∨ z = gr then true else lg.child z
    hv := fun d => if d = c then lg.hv d + (if g = cF s c then 0 else 1) +
      (if g = cLs s c then 0 else 1) else lg.hv d
    cs := fun d => if d = c ∧ lg.child g = true then lg.cs d + 1 else lg.cs d
    rs := fun d => if d = c ∧ lg.child g = false then lg.rs d + 1 else lg.rs d
    pb := fun d => if d = c ∧ g = cLs s c then lg.pb d + 1 else lg.pb d
    pf := fun d => if d = c ∧ g = cF s c then lg.pf d + 1 else lg.pf d }

theorem GrpsC_split {s s' : Core} {g gl gr labL labR : Nat} (S : SplitSpec s s' g gl gr labL labR)
    (c : Nat) : GrpsC s' c = if c = gC s g then insert gl (insert gr (GrpsC s c)) else GrpsC s c := by
  have key : ∀ z, (LiveG s' z ∧ gC s' z = c) ↔
      ((z = gl ∨ z = gr) ∧ c = gC s g) ∨ (LiveG s z ∧ gC s z = c) := by
    intro z
    rw [S.live, S.chk]
    by_cases hz : z = gl ∨ z = gr
    · have hnl : ¬ LiveG s z := by rcases hz with rfl | rfl; exact S.glOut; exact S.grOut
      rw [if_pos hz]; simp only [hz, true_or, true_and, hnl, false_and, or_false]; exact eq_comm
    · rw [if_neg hz]
      have : (z = gl ∨ z = gr ∨ LiveG s z) ↔ LiveG s z := by
        constructor
        · rintro (h | h | h); exact absurd (Or.inl h) hz; exact absurd (Or.inr h) hz; exact h
        · exact fun h => Or.inr (Or.inr h)
      rw [this]; simp [hz]
  unfold GrpsC
  by_cases hcc : c = gC s g
  · rw [if_pos hcc]
    ext z
    simp only [Finset.mem_insert, Finset.mem_filter, Finset.mem_range]
    constructor
    · rintro ⟨-, h⟩
      rcases (key z).mp h with ⟨h1, -⟩ | h2
      · rcases h1 with rfl | rfl; exact Or.inl rfl; exact Or.inr (Or.inl rfl)
      · exact Or.inr (Or.inr ⟨h2.1.2.1, h2⟩)
    · intro h
      have h' : LiveG s' z ∧ gC s' z = c := by
        rcases h with rfl | rfl | ⟨-, h2⟩
        · exact (key _).mpr (Or.inl ⟨Or.inl rfl, hcc⟩)
        · exact (key _).mpr (Or.inl ⟨Or.inr rfl, hcc⟩)
        · exact (key _).mpr (Or.inr h2)
      exact ⟨h'.1.2.1, h'⟩
  · rw [if_neg hcc]
    ext z
    simp only [Finset.mem_filter, Finset.mem_range]
    constructor
    · rintro ⟨-, h⟩
      rcases (key z).mp h with ⟨-, h1⟩ | h2
      · exact absurd h1 hcc
      · exact ⟨h2.1.2.1, h2⟩
    · rintro ⟨-, h2⟩
      have h' := (key z).mpr (Or.inr h2)
      exact ⟨h'.1.2.1, h'⟩

end OM.Proof

namespace OM.Proof

open OM.Model

set_option linter.deprecated false

/-- The group before a non-first group of a chunk lies in the same chunk, right before it. -/
theorem INV.prev_in_chunk {s : Core} {A : Abs} (hI : INV s A) {g : Nat} (hg : LiveG s g)
    (hf : g ≠ cF s (gC s g)) :
    LiveG s (gP s g) ∧ gC s (gP s g) = gC s g ∧ gN s (gP s g) = g ∧
      gP s g ≠ cLs s (gC s g) := by
  have hgl := hI.mem_glist_iff.mpr hg
  obtain ⟨hc, hgc⟩ := hI.mem_glist hgl
  obtain ⟨r1, r2, hrun⟩ := List.mem_iff_append.mp hgc
  have hnd := hI.grps_nodup hc
  rw [hrun] at hnd
  have hr1 : r1 ≠ [] := by
    rintro rfl
    apply hf; rw [(hI.cEnds _ hc).1, hrun]; rfl
  obtain ⟨r1', p, rfl⟩ := r1.eq_nil_or_concat.resolve_left hr1
  rw [List.concat_eq_append] at hrun hnd
  have hpm : p ∈ A.grps (gC s g) := by rw [hrun]; simp
  have hpg : p ∈ A.glist := A.grps_sub_glist hc hpm
  have hpc : gC s p = gC s g := hI.chk _ hc p hpm
  have hgp : g ∉ r1' ++ [p] := fun h => (List.nodup_append.mp hnd).2.2 g h g (by simp) rfl
  have hprev : gP s g = p := by
    rw [hI.gList.prev g hgl, INV.glist_flatten]
    have hnd' := hI.gList.nodup
    rw [INV.glist_flatten] at hnd'
    rw [predOf_flatten hnd' (List.mem_map.mpr ⟨_, hc, rfl⟩) hgc (by
      rw [hrun]
      cases r1' with
      | nil => simp; intro e; exact hgp (by simp [e])
      | cons a t => simp; intro e; exact hgp (by simp [e]))]
    rw [hrun, show r1' ++ [p] ++ g :: r2 = (r1' ++ [p]) ++ g :: r2 by simp, predOf_mid (by simpa using hnd)]
    simp
  have hp0 : p ≠ NIL := fun e => hI.gList.nonil (e ▸ hpg)
  have hnext : gN s p = g := by rw [← hprev]; exact hI.gN_gP hgl (by rw [hprev]; exact hp0)
  rw [hprev]
  refine ⟨hI.mem_glist_iff.mp hpg, hpc, hnext, ?_⟩
  intro e
  have hE := (hI.cEnds _ hc).2
  rw [hrun, show r1' ++ [p] ++ g :: r2 = (r1' ++ [p]) ++ g :: r2 by simp,
    getLastD_append_ne (by simp)] at hE
  have hm : (g :: r2).getLastD NIL ∈ g :: r2 := getLastD_cons_mem _ _ _
  rw [← hE, ← e] at hm
  have := (List.nodup_append.mp hnd).2.2 p (by simp) p
  rw [show r1' ++ [p] ++ g :: r2 = (r1' ++ [p]) ++ g :: r2 by simp] at hnd
  exact (List.nodup_append.mp hnd).2.2 p (by simp) p hm rfl

end OM.Proof

namespace OM.Proof

open OM.Model

set_option linter.deprecated false

theorem mem_GrpsC {s : Core} {c g : Nat} : g ∈ GrpsC s c ↔ LiveG s g ∧ gC s g = c := by
  unfold GrpsC; simp only [Finset.mem_filter, Finset.mem_range]
  exact ⟨fun h => h.2, fun h => ⟨h.1.2.1, h⟩⟩

/-- Unsplit roots after a split start: the splitting group stops being one. -/
theorem pending_split {s s' : Core} {g gl gr labL labR : Nat} (S : SplitSpec s s' g gl gr labL labR)
    (hg : LiveG s g) (hq : gSt s g = .quiet) (lg : LGh) (c : Nat) :
    pending s' (lg.split s g gl gr) c + (if c = gC s g ∧ lg.child g = false then 1 else 0) =
      pending s lg c := by
  unfold pending
  rw [GrpsC_split S]
  have hne : ∀ z ∈ GrpsC s c, z ≠ gl ∧ z ≠ gr := fun z hz =>
    ⟨fun e => S.glOut (e ▸ (mem_GrpsC.mp hz).1), fun e => S.grOut (e ▸ (mem_GrpsC.mp hz).1)⟩
  have hpred : ∀ z ∈ GrpsC s c, ((lg.split s g gl gr).child z = false ∧ gSt s' z ≠ .splitting) ↔
      ((lg.child z = false ∧ gSt s z ≠ .splitting) ∧ z ≠ g) := by
    intro z hz
    obtain ⟨h1, h2⟩ := hne z hz
    simp only [LGh.split, h1, h2, or_self, if_false, S.st]
    by_cases hzg : z = g
    · subst hzg; simp
    · simp [hzg]
  split
  · next hcc =>
    have hgl' : (lg.split s g gl gr).child gl = true := by simp [LGh.split]
    have hgr' : (lg.split s g gl gr).child gr = true := by simp [LGh.split]
    rw [Finset.filter_insert, if_neg (by simp [hgl']), Finset.filter_insert, if_neg (by simp [hgr'])]
    rw [Finset.filter_congr hpred]
    have hgG : g ∈ GrpsC s c := mem_GrpsC.mpr ⟨hg, hcc.symm⟩
    by_cases hch : lg.child g = false
    · rw [if_pos ⟨hcc, hch⟩]
      have hgf : g ∈ (GrpsC s c).filter (fun z => lg.child z = false ∧ gSt s z ≠ .splitting) := by
        simp only [Finset.mem_filter]; exact ⟨hgG, hch, by rw [hq]; simp⟩
      rw [← Finset.filter_filter, Finset.filter_ne', Finset.card_erase_of_mem hgf]
      have := Finset.card_pos.mpr ⟨g, hgf⟩
      omega
    · rw [if_neg (fun h => hch h.2), Nat.add_zero]
      congr 1
      rw [← Finset.filter_filter]
      apply Finset.filter_true_of_mem
      intro z hz hzg; subst hzg; simp at hz; exact hch hz.2.1
  · next hcc =>
    rw [if_neg (fun h => hcc h.1), Nat.add_zero]
    congr 1
    apply Finset.filter_congr
    intro z hz
    rw [hpred z hz]
    have : z ≠ g := by rintro rfl; exact hcc (mem_GrpsC.mp hz).2.symm
    simp [this]

end OM.Proof

namespace OM.Proof

open OM.Model

set_option linter.deprecated false

/-- One group's term in `charge`. -/
def chTerm (s : Core) (lg : LGh) (g : Nat) : Nat :=
  if gSt s g = .splitting ∧ lg.child (gLl s g) = true then famT s g - s.P.G
  else if gSt s g = .quiet ∧ lg.child g = true then gmin s.P + gSz s g - s.P.G else 0

theorem charge_eq (s : Core) (lg : LGh) (c : Nat) :
    charge s lg c = ∑ g ∈ GrpsC s c, chTerm s lg g := rfl

/-- The charge after a split start: a quiet child's `g_min` became a child split. -/
theorem charge_split {s s' : Core} {L : List Nat} {gh : GGh} {δ : Nat → Nat} {ex : Nat}
    {g gl gr labL labR : Nat} (S : SplitSpec s s' g gl gr labL labR) (hG : GInvE s L gh δ ex)
    (hg : LiveG s g) (hq : gSt s g = .quiet) (hsz : gSz s g = s.P.G) (lg : LGh) (c : Nat) :
    charge s' (lg.split s g gl gr) c + (if c = gC s g ∧ lg.child g = true then gmin s.P else 0) =
      charge s lg c := by
  have hne : ∀ z, LiveG s z → z ≠ gl ∧ z ≠ gr := fun z hz =>
    ⟨fun e => S.glOut (e ▸ hz), fun e => S.grOut (e ▸ hz)⟩
  -- terms of the old groups other than `g` are unchanged
  have hterm : ∀ z, LiveG s z → z ≠ g → chTerm s' (lg.split s g gl gr) z = chTerm s lg z := by
    intro z hz hzg
    have hz' := not_or.mpr (hne z hz)
    unfold chTerm
    rw [S.st, if_neg hzg, if_neg hz', S.l, if_neg hzg, if_neg hz']
    have hch : (lg.split s g gl gr).child z = lg.child z := by simp [LGh.split, hz']
    by_cases hs : gSt s z = .splitting
    · have F := hG.fam z hz hs
      have hl' := not_or.mpr (hne _ F.lLive)
      have hchl : (lg.split s g gl gr).child (gLl s z) = lg.child (gLl s z) := by
        simp [LGh.split, hl']
      have hfam : famT s' z = famT s z := by
        simp only [famT, S.sz, S.l, S.r, if_neg hzg, if_neg hz', if_neg hl',
          if_neg (not_or.mpr (hne _ F.rLive))]
      rw [hchl, hfam, S.P, hch, S.sz, if_neg hz']
    · simp only [hs, false_and, if_false, hch, S.sz, if_neg hz', S.P]
  rw [charge_eq, charge_eq, GrpsC_split S]
  split
  · next hcc =>
    have hgl' : chTerm s' (lg.split s g gl gr) gl = 0 := by
      unfold chTerm; rw [S.st, if_neg (Ne.symm S.ggl), if_pos (Or.inl rfl)]; simp
    have hgr' : chTerm s' (lg.split s g gl gr) gr = 0 := by
      unfold chTerm; rw [S.st, if_neg (Ne.symm S.ggr), if_pos (Or.inr rfl)]; simp
    have hglm : gl ∉ insert gr (GrpsC s c) := by
      simp only [Finset.mem_insert, mem_GrpsC, not_or]; exact ⟨S.glr, fun h => S.glOut h.1⟩
    have hgrm : gr ∉ GrpsC s c := by simp only [mem_GrpsC]; exact fun h => S.grOut h.1
    rw [Finset.sum_insert hglm, Finset.sum_insert hgrm, hgl', hgr', Nat.zero_add, Nat.zero_add]
    have hgG : g ∈ GrpsC s c := mem_GrpsC.mpr ⟨hg, hcc.symm⟩
    rw [← Finset.add_sum_erase _ _ hgG, ← Finset.add_sum_erase _ _ hgG]
    have hrest : ∑ z ∈ (GrpsC s c).erase g, chTerm s' (lg.split s g gl gr) z =
        ∑ z ∈ (GrpsC s c).erase g, chTerm s lg z := by
      refine Finset.sum_congr rfl fun z hz => ?_
      obtain ⟨hzg, hzG⟩ := Finset.mem_erase.mp hz
      exact hterm z (mem_GrpsC.mp hzG).1 hzg
    rw [hrest]
    have hg' : chTerm s' (lg.split s g gl gr) g = 0 := by
      unfold chTerm
      rw [S.st, if_pos rfl, S.l, if_pos rfl]
      simp only [LGh.split, true_or, if_true, and_self, if_true]
      simp only [famT, S.sz, S.l, S.r, if_pos rfl, true_or, or_true, if_true,
        if_neg (not_or.mpr ⟨S.ggl, S.ggr⟩), hsz, S.P]
      simp
    have hgt : chTerm s lg g = if lg.child g = true then gmin s.P else 0 := by
      unfold chTerm; rw [hq]; simp [hsz]
    rw [hg', hgt]
    by_cases hch : lg.child g = true
    · rw [if_pos ⟨hcc, hch⟩, if_pos hch]; omega
    · rw [if_neg (fun h => hch h.2), if_neg hch]; simp
  · next hcc =>
    rw [if_neg (fun h => hcc h.1), Nat.add_zero]
    refine Finset.sum_congr rfl fun z hz => ?_
    have hz' := mem_GrpsC.mp hz
    exact hterm z hz'.1 (by rintro rfl; exact hcc hz'.2.symm)

end OM.Proof

namespace OM.Proof

open OM.Model

set_option linter.deprecated false

/-- The group after a non-last group of a chunk lies in the same chunk. -/
theorem INV.next_in_chunk {s : Core} {A : Abs} (hI : INV s A) {g : Nat} (hg : LiveG s g)
    (hl : g ≠ cLs s (gC s g)) : LiveG s (gN s g) ∧ gC s (gN s g) = gC s g := by
  have hgl := hI.mem_glist_iff.mpr hg
  obtain ⟨hc, hgc⟩ := hI.mem_glist hgl
  obtain ⟨r1, r2, hrun⟩ := List.mem_iff_append.mp hgc
  have hnd := hI.grps_nodup hc
  rw [hrun] at hnd
  cases r2 with
  | nil =>
    exfalso; apply hl; rw [(hI.cEnds _ hc).2, hrun]; simp
  | cons n t =>
    have hnm : n ∈ A.grps (gC s g) := by rw [hrun]; simp
    have hnext : gN s g = n := by
      rw [hI.gList.next g hgl, INV.glist_flatten]
      have hnd' := hI.gList.nodup
      rw [INV.glist_flatten] at hnd'
      rw [succOf_flatten hnd' (List.mem_map.mpr ⟨_, hc, rfl⟩) hgc (by
        rw [hrun, show r1 ++ g :: n :: t = (r1 ++ [g]) ++ n :: t by simp,
          List.getLast?_append_of_ne_nil _ (by simp)]
        intro e
        have hm : g ∈ n :: t := List.mem_of_getLast? e
        exact (List.nodup_cons.mp (List.nodup_append.mp hnd).2.1).1 hm),
        hrun, succOf_mid hnd]
      rfl
    rw [hnext]
    exact ⟨hI.mem_glist_iff.mp (A.grps_sub_glist hc hnm), hI.chk _ hc n hnm⟩

/-- A group followed by a group of another chunk is the last of its chunk. -/
theorem INV.last_of_next {s : Core} {A : Abs} (hI : INV s A) {g : Nat} (hg : LiveG s g)
    (hc : gN s g ≠ NIL → gC s (gN s g) ≠ gC s g) : g = cLs s (gC s g) := by
  by_contra hl
  have := hI.next_in_chunk hg hl
  exact hc this.1.1 this.2

end OM.Proof

namespace OM.Proof

open OM.Model

set_option linter.deprecated false

theorem div_two_pow_succ (D k : Nat) : D / 2 ^ (k + 1) = D / 2 ^ k / 2 := by
  rw [Nat.div_div_eq_div_mul, pow_succ]

/-- **The group-label invariant across a split start.** -/
theorem linv_splitStart {s : Core} {A : Abs} {L : List Nat} {gh : GGh} {δg s₀ δ δu : Nat → Nat}
    {ex : Nat} {lg : LGh} {g labL labR : Nat} (hI : INV s A) (hG : GInvE s L gh δg ex)
    (hL : LInv s lg s₀ δ δu) (hg : LiveG s g) (hq : gSt s g = .quiet) (hsz : gSz s g = s.P.G)
    (hLb : (labBefore g).run s = .ok labL s) (hLa : (labAfter g).run s = .ok labR s) :
    LInv (splitState s g labL labR) (lg.split s g (splitL s g) (splitR s g)) s₀ δ δu := by
  have S := splitSpec hI (hI.mem_glist_iff.mpr hg) labL labR
  have hpend := pending_split S hg hq lg
  have hchg := charge_split S hG hg hq hsz lg
  have hvL := labBefore_val hLb
  have hvR := labAfter_val hLa
  have hgB := labBefore_guard hLb
  have hgA := labAfter_guard hLa
  generalize splitState s g labL labR = s' at S hpend hchg ⊢
  generalize splitL s g = gl at S hpend hchg ⊢
  generalize splitR s g = gr at S hpend hchg ⊢
  generalize hc : gC s g = c at hvL hvR hgB hgA hpend hchg
  have hne : ∀ z, LiveG s z → z ≠ gl ∧ z ≠ gr := fun z hz =>
    ⟨fun e => S.glOut (e ▸ hz), fun e => S.grOut (e ▸ hz)⟩
  -- the chunk's ends after the split
  have hCF : ∀ d, cF s' d = if d = c ∧ cF s d = g then gl else cF s d := by
    intro d; simp only [cF, S.C, hc]; by_cases hd : d = c
    · subst hd; simp
    · simp [hd]
  have hCL : ∀ d, cLs s' d = if d = c ∧ cLs s d = g then gr else cLs s d := by
    intro d; simp only [cLs, S.C, hc]; by_cases hd : d = c
    · subst hd; simp
    · simp [hd]
  have hchk : ∀ z, gC s' z = if z = gl ∨ z = gr then c else gC s z := by
    intro z; rw [S.chk, hc]
  set lg' := lg.split s g gl gr with hlg'
  have hv' : ∀ d, lg'.hv d = if d = c then lg.hv d + (if g = cF s c then 0 else 1) +
      (if g = cLs s c then 0 else 1) else lg.hv d := by
    intro d; simp only [hlg', LGh.split, hc]
  have hvge : ∀ d, lg.hv d ≤ lg'.hv d := by intro d; rw [hv']; split <;> omega
  have wmono : ∀ d, s.P.D_g / 2 ^ lg'.hv d ≤ s.P.D_g / 2 ^ lg.hv d :=
    fun d => div_pow_anti _ (hvge d)
  -- chunk records other than the ends are unchanged
  have hcf : ∀ d, cSz s' d = cSz s d ∧ cSt s' d = cSt s d ∧ cSrc s' d = cSrc s d ∧
      cLl s' d = cLl s d ∧ cRr s' d = cRr s d := by
    intro d; simp only [cSz, cSt, cSrc, cLl, cRr, S.C]; split <;> exact ⟨rfl, rfl, rfl, rfl, rfl⟩
  have hLC : ∀ d, LiveC s' d ↔ LiveC s d := by intro d; simp only [LiveC, S.Csize]
  have hfamC : ∀ x, famC s' x = famC s x := by
    intro x; simp only [famC, (hcf _).1, (hcf x).2.2.2.1, (hcf x).2.2.2.2]
  have hunits : ∀ d, units s' d = units s d := by
    intro d
    apply units_congr
    intro z
    unfold UnitG
    rw [S.live, S.chk]
    by_cases h1 : z = gl
    · subst h1; simp [S.st, Ne.symm S.ggl, S.glOut]
    · by_cases h2 : z = gr
      · subst h2; simp [S.st, Ne.symm S.ggr, S.grOut]
      · simp only [h1, h2, false_or, S.st, if_false, or_self]
        by_cases h3 : z = g
        · subst h3; simp [hq]
        · simp [h3]
  have hgL' : ∀ z, gL s' z = if z = gl then labL else if z = gr then labR else gL s z := S.lab
  refine
    { gaps := ?_, range := ?_, hv := ?_, pb := ?_, pf := ?_, roots := ?_, claim2 := ?_,
      insQ := ?_, insO := ?_, insS := ?_, arrS := ?_, arrN := ?_, e0 := ?_, famChild := ?_ }
  · -- gaps
    intro h hh hlast
    have hgl' : gL s' gl = labL := by rw [hgL', if_pos rfl]
    have hgr' : gL s' gr = labR := by rw [hgL', if_neg (Ne.symm S.glr), if_pos rfl]
    have hgg' : gL s' g = gL s g := by rw [hgL', if_neg S.ggl, if_neg S.ggr]
    have hold : ∀ z, LiveG s z → gL s' z = gL s z := by
      intro z hz; rw [hgL', if_neg (hne z hz).1, if_neg (hne z hz).2]
    rcases (S.live h).mp hh with rfl | rfl | hhL
    · -- the new left sibling
      rw [hchk, if_pos (Or.inl rfl)]
      rw [S.next, if_neg (Ne.symm S.ggl), if_pos rfl, hgl', hgg']
      by_cases hf : g = cF s c
      · rw [hvL, if_pos hf]
        have := (hgB.1 (hc ▸ hf)).1
        have := Nat.div_le_self s.P.D_g (2 ^ lg'.hv c)
        rw [S.P]; omega
      · rw [hvL, if_neg hf, S.P]
        obtain ⟨hpL, hpc, hpn, hpl⟩ := hI.prev_in_chunk hg (hc ▸ hf)
        have hgap := hL.gaps _ hpL (by rw [hpc, hc]; rw [hc] at hpl; exact hpl)
        rw [hpn, hpc, hc] at hgap
        have hw : s.P.D_g / 2 ^ lg'.hv c ≤ s.P.D_g / 2 ^ lg.hv c / 2 := by
          rw [← div_two_pow_succ]; apply div_pow_anti
          rw [hv', if_pos rfl, if_neg hf]; omega
        omega
    · -- the new right sibling
      rw [hchk, if_pos (Or.inr rfl)] at hlast ⊢
      have hl : g ≠ cLs s c := by
        intro e; apply hlast; rw [hCL, if_pos ⟨rfl, e.symm⟩]
      rw [S.next, if_neg (Ne.symm S.ggr), if_neg S.glr.symm, if_pos rfl, hgr', S.P]
      obtain ⟨hnL, hnc⟩ := hI.next_in_chunk hg (hc ▸ hl)
      rw [hold _ hnL, hvR, if_neg hl]
      have hgap := hL.gaps g hg (hc ▸ hl)
      rw [hc] at hgap
      have hw : s.P.D_g / 2 ^ lg'.hv c ≤ s.P.D_g / 2 ^ lg.hv c / 2 := by
        rw [← div_two_pow_succ]; apply div_pow_anti
        rw [hv', if_pos rfl, if_neg hl]; omega
      omega
    · have hh' := not_or.mpr (hne h hhL)
      rw [hchk, if_neg hh'] at hlast ⊢
      rw [hold h hhL, S.P]
      by_cases hhg : h = g
      · -- the splitting group
        subst hhg
        rw [hc, S.next, if_pos rfl, hgr']
        by_cases hl : h = cLs s c
        · rw [hvR, if_pos hl]
          have := Nat.div_le_self s.P.D_g (2 ^ lg'.hv c); omega
        · rw [hvR, if_neg hl]
          have hgap := hL.gaps h hhL (hc ▸ hl)
          rw [hc] at hgap
          have hw : s.P.D_g / 2 ^ lg'.hv c ≤ s.P.D_g / 2 ^ lg.hv c / 2 := by
            rw [← div_two_pow_succ]; apply div_pow_anti
            rw [hv', if_pos rfl, if_neg hl]; omega
          omega
      · by_cases hp : h = gP s g ∧ gP s g ≠ NIL
        · -- the group before `g`
          rw [S.next, if_neg hhg, if_neg (hne h hhL).1, if_neg (hne h hhL).2, if_pos hp, hgl']
          by_cases hf : g = cF s c
          · exfalso
            -- `h` is the last of its chunk
            have hgN : gN s h = g := by rw [hp.1]; exact hI.gN_gP (hI.mem_glist_iff.mpr hg) hp.2
            have hcd : gC s h ≠ c := by
              intro e
              have hcf0 : cF s c ≠ NIL := by rw [← hf]; exact hg.1
              exact hI.not_before_first hcf0 (hI.mem_glist_iff.mpr hhL) e (by rw [hgN]; exact hf)
            have hlast' := hI.last_of_next hhL (by rw [hgN]; intro _; rw [hc]; exact Ne.symm hcd)
            apply hlast; rw [hCL, if_neg (fun h' => hcd h'.1)]; exact hlast'
          · obtain ⟨hpL, hpc, hpn, hpl⟩ := hI.prev_in_chunk hg (hc ▸ hf)
            rw [← hp.1] at hpc hpn
            rw [hpc, hc, hvL, if_neg hf, ← hp.1]
            have hgap := hL.gaps h hhL (by rw [hpc, hc]; rw [hc, ← hp.1] at hpl; exact hpl)
            rw [hpn, hpc, hc] at hgap
            have hw : s.P.D_g / 2 ^ lg'.hv c ≤ s.P.D_g / 2 ^ lg.hv c / 2 := by
              rw [← div_two_pow_succ]; apply div_pow_anti
              rw [hv', if_pos rfl, if_neg hf]; omega
            omega
        · -- any other group
          rw [S.next, if_neg hhg, if_neg (hne h hhL).1, if_neg (hne h hhL).2, if_neg hp]
          have hl : h ≠ cLs s (gC s h) := by
            intro e; apply hlast; rw [hCL]
            split
            · next h' => exact absurd (e.trans (h'.1 ▸ h'.2)) hhg
            · exact e
          obtain ⟨hnL, -⟩ := hI.next_in_chunk hhL hl
          rw [hold _ hnL]
          exact le_trans (by have := wmono (gC s h); omega) (hL.gaps h hhL hl)
  · -- range
    intro h hh
    have hpf : ∀ d, lg.pf d ≤ lg'.pf d := by intro d; simp only [hlg', LGh.split]; split <;> omega
    have hpb : ∀ d, lg.pb d ≤ lg'.pb d := by intro d; simp only [hlg', LGh.split]; split <;> omega
    rcases (S.live h).mp hh with rfl | rfl | hhL
    · rw [hchk, if_pos (Or.inl rfl), hgL', if_pos rfl, S.P]
      obtain ⟨r1, r2⟩ := hL.range g hg
      rw [hc] at r1 r2
      have hb1 := Nat.mul_le_mul_right s.P.D_g (hpb c)
      by_cases hf : g = cF s c
      · have hpf1 : lg'.pf c = lg.pf c + 1 := by
          simp only [hlg', LGh.split]; rw [if_pos ⟨hc.symm, by rw [hc]; exact hf⟩]
        rw [hvL, if_pos hf, hpf1]
        have := (hgB.1 (hc ▸ hf)).1
        constructor
        · rw [Nat.add_mul]; omega
        · omega
      · rw [hvL, if_neg hf]
        obtain ⟨hpL, hpc, hpn, hpl⟩ := hI.prev_in_chunk hg (hc ▸ hf)
        obtain ⟨p1, -⟩ := hL.range _ hpL
        rw [hpc, hc] at p1
        have hb2 := Nat.mul_le_mul_right s.P.D_g (hpf c)
        have := hgB.2 (hc ▸ hf)
        constructor <;> omega
    · rw [hchk, if_pos (Or.inr rfl), hgL', if_neg (Ne.symm S.glr), if_pos rfl, S.P]
      obtain ⟨r1, r2⟩ := hL.range g hg
      rw [hc] at r1 r2
      have hb2 := Nat.mul_le_mul_right s.P.D_g (hpf c)
      by_cases hl : g = cLs s c
      · have hpb1 : lg'.pb c = lg.pb c + 1 := by
          simp only [hlg', LGh.split]; rw [if_pos ⟨hc.symm, by rw [hc]; exact hl⟩]
        rw [hvR, if_pos hl, hpb1]
        constructor
        · omega
        · rw [Nat.add_mul]; omega
      · rw [hvR, if_neg hl]
        obtain ⟨hnL, hnc⟩ := hI.next_in_chunk hg (hc ▸ hl)
        obtain ⟨-, n2⟩ := hL.range _ hnL
        rw [hnc, hc] at n2
        have hb1 := Nat.mul_le_mul_right s.P.D_g (hpb c)
        have := hgA.2 (hc ▸ hl)
        constructor <;> omega
    · have hh' := not_or.mpr (hne h hhL)
      rw [hchk, if_neg hh', hgL', if_neg (hne h hhL).1, if_neg (hne h hhL).2, S.P]
      obtain ⟨r1, r2⟩ := hL.range h hhL
      have hb1 := Nat.mul_le_mul_right s.P.D_g (hpb (gC s h))
      have hb2 := Nat.mul_le_mul_right s.P.D_g (hpf (gC s h))
      constructor <;> omega
  · intro d
    have h := hL.hv d
    by_cases hdc : d = c
    · subst hdc
      cases hch : lg.child g <;>
        simp only [hlg', LGh.split, hc, hch, and_true, and_false, if_true, if_false,
          Bool.false_eq_true, Bool.true_eq_false] <;> split_ifs <;> omega
    · simp only [hlg', LGh.split, hc, hdc, false_and, if_false]; exact h
  · intro d
    have h := hL.pb d
    by_cases hdc : d = c
    · subst hdc
      cases hch : lg.child g <;>
        simp only [hlg', LGh.split, hc, hch, and_true, and_false, if_true, if_false,
          Bool.false_eq_true, Bool.true_eq_false, true_and] <;> split_ifs <;> omega
    · simp only [hlg', LGh.split, hc, hdc, false_and, if_false]; exact h
  · intro d
    have h := hL.pf d
    by_cases hdc : d = c
    · subst hdc
      cases hch : lg.child g <;>
        simp only [hlg', LGh.split, hc, hch, and_true, and_false, if_true, if_false,
          Bool.false_eq_true, Bool.true_eq_false, true_and] <;> split_ifs <;> omega
    · simp only [hlg', LGh.split, hc, hdc, false_and, if_false]; exact h
  · intro d hd
    rw [hLC] at hd
    have h1 := hL.roots d hd
    have h2 := hpend d
    by_cases hdc : d = c
    · subst hdc
      cases hch : lg.child g <;>
        simp only [hlg', LGh.split, hc, hch, and_true, and_false, if_true, if_false,
          Bool.false_eq_true, Bool.true_eq_false] at h2 ⊢ <;> omega
    · simp only [hlg', LGh.split, hc, hdc, false_and, if_false] at h2 ⊢; omega
  · intro d hd
    rw [hLC] at hd
    have h1 := hL.claim2 d hd
    have h2 := hchg d
    simp only [hlg', LGh.split, hc, S.P] at h2 ⊢
    by_cases hdc : d = c
    · subst hdc
      by_cases hch : lg.child g = true
      · simp only [hch, and_self, true_and, if_true] at h2 ⊢
        rw [Nat.add_mul]; omega
      · have hch' : lg.child g = false := by simpa using hch
        simp only [hch', Bool.false_eq_true, and_false, true_and, if_false] at h2 ⊢
        omega
    · simp only [hdc, false_and, if_false] at h2 ⊢; omega
  · intro d hd hds
    rw [hLC] at hd; rw [(hcf d).2.1] at hds
    rw [(hcf d).1, S.P]; exact hL.insQ d hd hds
  · intro d hd hds
    rw [hLC] at hd; rw [(hcf d).2.1] at hds
    rw [(hcf d).2.2.1, hfamC]; exact hL.insO d hd hds
  · intro d hd hds
    rw [hLC] at hd; rw [(hcf d).2.1] at hds
    rw [hfamC, S.P]; exact hL.insS d hd hds
  · intro x hx hxs
    rw [hLC] at hx; rw [(hcf x).2.1] at hxs
    rw [(hcf x).2.2.2.1, (hcf x).2.2.2.2, hunits, (hcf _).1, (hcf x).1, (hcf _).1, S.P]
    exact hL.arrS x hx hxs
  · intro d hd hds
    rw [hLC] at hd; rw [(hcf d).2.1] at hds
    rw [S.P]; exact hL.arrN d hd hds
  · intro d hd hds
    rw [hLC] at hd; rw [(hcf d).2.1] at hds
    rw [(hcf d).1]; exact hL.e0 d hd hds
  · intro p hp hps
    rcases (S.live p).mp hp with rfl | rfl | hpL
    · rw [S.st, if_neg (Ne.symm S.ggl), if_pos (Or.inl rfl)] at hps; cases hps
    · rw [S.st, if_neg (Ne.symm S.ggr), if_pos (Or.inr rfl)] at hps; cases hps
    · by_cases hpg : p = g
      · subst hpg
        rw [S.l, S.r, if_pos rfl, if_pos rfl]
        simp [hlg', LGh.split]
      · rw [S.st, if_neg hpg, if_neg (not_or.mpr (hne p hpL))] at hps
        have F := hG.fam p hpL hps
        rw [S.l, S.r, if_neg hpg, if_neg hpg, if_neg (not_or.mpr (hne p hpL)),
          if_neg (not_or.mpr (hne p hpL))]
        simp only [hlg', LGh.split, if_neg (not_or.mpr (hne _ F.lLive)),
          if_neg (not_or.mpr (hne _ F.rLive))]
        exact hL.famChild p hpL hps

end OM.Proof

namespace OM.Proof

open OM.Model

set_option linter.deprecated false

/-! ### Across a split move -/

/-- **The group-label invariant across a split move** (an element moves inside a family). -/
theorem linv_move {s s' : Core} {A : Abs} {L : List Nat} {gh : GGh} {δg s₀ δ δu : Nat → Nat}
    {ex : Nat} {lg : LGh} {src dst e lab : Nat} (hI : INV s A) (hG : GInvE s L gh δg ex) (hL : LInv s lg s₀ δ δu)
    (M : MoveSpec s s' src dst e lab) (hsrc : LiveG s src) (hss : gSt s src = .splitting)
    (hdst : dst = gLl s src ∨ dst = gRr s src) (hne : 1 ≤ gSz s src) : LInv s' lg s₀ δ δu := by
  have hK := M.links
  have Fs := hG.fam src hsrc hss
  have hdst' : dst ≠ src := by
    rcases hdst with rfl | rfl
    · intro e; have := Fs.lSt; rw [e, hss] at this; cases this
    · intro e; have := Fs.rSt; rw [e, hss] at this; cases this
  have hLv : ∀ z, LiveG s' z ↔ LiveG s z := hK.liveG
  have hCs : ∀ c, s'.C.getX c = s.C.getX c := fun c => by rw [M.C]
  have hcf : ∀ d, cSz s' d = cSz s d ∧ cSt s' d = cSt s d ∧ cSrc s' d = cSrc s d ∧
      cLl s' d = cLl s d ∧ cRr s' d = cRr s d ∧ cLs s' d = cLs s d := by
    intro d; simp only [cSz, cSt, cSrc, cLl, cRr, cLs, hCs, and_self]
  have hLC : ∀ d, LiveC s' d ↔ LiveC s d := by intro d; simp only [LiveC, M.C]
  have hfamC : ∀ x, famC s' x = famC s x := by
    intro x; simp only [famC, (hcf _).1, (hcf x).2.2.2.1, (hcf x).2.2.2.2.1]
  have hunits : ∀ d, units s' d = units s d := by
    intro d; apply units_congr; intro z; unfold UnitG; rw [hLv, hK.chk, hK.st]
  have hGrps : ∀ c, GrpsC s' c = GrpsC s c := by
    intro c; ext z; simp only [mem_GrpsC, hLv, hK.chk]
  -- family sizes are unchanged, and so are quiet groups' sizes
  have hfamT : ∀ p, LiveG s p → gSt s p = .splitting → famT s' p = famT s p := by
    intro p hp hps
    by_cases hpe : p = src
    · subst hpe
      have hlr := Fs.lr hI hsrc
      have hlp := Fs.lp hI hsrc
      have hrp := Fs.rp hI hsrc
      have e2 : gSz s' p = gSz s p - 1 := by rw [M.sz, if_pos rfl]
      unfold famT
      rw [hK.l, hK.r, e2]
      rcases hdst with rfl | rfl
      · have e1 : gSz s' (gLl s p) = gSz s (gLl s p) + 1 := by rw [M.sz, if_neg hlp, if_pos rfl]
        have e3 : gSz s' (gRr s p) = gSz s (gRr s p) := by
          rw [M.sz, if_neg hrp, if_neg (Ne.symm hlr)]
        rw [e1, e3]; omega
      · have e1 : gSz s' (gLl s p) = gSz s (gLl s p) := by rw [M.sz, if_neg hlp, if_neg hlr]
        have e3 : gSz s' (gRr s p) = gSz s (gRr s p) + 1 := by rw [M.sz, if_neg hrp, if_pos rfl]
        rw [e1, e3]; omega
    · have D := Fs.disjoint (hG.fam p hp hps) (Ne.symm hpe) hss hps
      obtain ⟨d1, d2, d3, d4, d5, d6, d7, d8⟩ := D
      have hdl : gLl s p ≠ dst := by rcases hdst with rfl | rfl; exact d3; exact d4
      have hdr : gRr s p ≠ dst := by rcases hdst with rfl | rfl; exact d6; exact d7
      have hdp : p ≠ dst := by rcases hdst with rfl | rfl; exact d1; exact d2
      simp only [famT, hK.l, hK.r, M.sz, if_neg d5, if_neg hdl, if_neg hpe, if_neg hdp, if_neg d8,
        if_neg hdr]
  have hqsz : ∀ z, gSt s z = .quiet → gSz s' z = gSz s z := by
    intro z hz
    have h1 : z ≠ src := by rintro rfl; rw [hss] at hz; cases hz
    have h2 : z ≠ dst := by
      rcases hdst with rfl | rfl
      · intro e; have := Fs.lSt; rw [← e, hz] at this; cases this
      · intro e; have := Fs.rSt; rw [← e, hz] at this; cases this
    rw [M.sz, if_neg h1, if_neg h2]
  have hcharge : ∀ c, charge s' lg c = charge s lg c := by
    intro c
    rw [charge_eq, charge_eq, hGrps]
    refine Finset.sum_congr rfl fun z hz => ?_
    have hzL := (mem_GrpsC.mp hz).1
    unfold chTerm
    rw [hK.st, hK.l, M.P]
    by_cases hs : gSt s z = .splitting
    · rw [hfamT z hzL hs]
      have hnq : ¬ (gSt s z = .quiet) := by rw [hs]; simp
      simp only [hnq, false_and, if_false]
    · by_cases hq : gSt s z = .quiet
      · rw [hqsz z hq]; simp only [hs, false_and, if_false]
      · simp only [hs, hq, false_and, if_false]
  have hpend : ∀ c, pending s' lg c = pending s lg c := by
    intro c; unfold pending; rw [hGrps]
    congr 1; apply Finset.filter_congr; intro z _; rw [hK.st]
  refine
    { gaps := ?_, range := ?_, hv := hL.hv, pb := hL.pb, pf := hL.pf, roots := ?_, claim2 := ?_,
      insQ := ?_, insO := ?_, insS := ?_, arrS := ?_, arrN := ?_, e0 := ?_, famChild := ?_ }
  · intro h hh hl
    rw [hLv] at hh; rw [hK.chk, (hcf _).2.2.2.2.2] at hl; rw [hK.chk]
    rw [M.lab, M.lab, hK.next, M.P]; exact hL.gaps h hh hl
  · intro h hh; rw [hLv] at hh; rw [hK.chk, M.lab, M.P]; exact hL.range h hh
  · intro d hd; rw [hLC] at hd; rw [hpend]; exact hL.roots d hd
  · intro d hd; rw [hLC] at hd; rw [hcharge, M.P]; exact hL.claim2 d hd
  · intro d hd hds; rw [hLC] at hd; rw [(hcf d).2.1] at hds; rw [(hcf d).1, M.P]
    exact hL.insQ d hd hds
  · intro d hd hds; rw [hLC] at hd; rw [(hcf d).2.1] at hds; rw [(hcf d).2.2.1, hfamC]
    exact hL.insO d hd hds
  · intro d hd hds; rw [hLC] at hd; rw [(hcf d).2.1] at hds; rw [hfamC, M.P]
    exact hL.insS d hd hds
  · intro x hx hxs; rw [hLC] at hx; rw [(hcf x).2.1] at hxs
    rw [(hcf x).2.2.2.1, (hcf x).2.2.2.2.1, hunits, (hcf _).1, (hcf x).1, (hcf _).1, M.P]
    exact hL.arrS x hx hxs
  · intro d hd hds; rw [hLC] at hd; rw [(hcf d).2.1] at hds; rw [M.P]; exact hL.arrN d hd hds
  · intro d hd hds; rw [hLC] at hd; rw [(hcf d).2.1] at hds; rw [(hcf d).1]; exact hL.e0 d hd hds
  · intro p hp hps; rw [hLv] at hp; rw [hK.st] at hps; rw [hK.l, hK.r]
    exact hL.famChild p hp hps

end OM.Proof

namespace OM.Proof

open OM.Model

set_option linter.deprecated false

/-! ### Across a group removal -/

/-- **The group-label invariant across a group removal**: two gaps merge, the siblings become
quiet, and the family's charge pays for theirs. -/
theorem linv_remove {s : Core} {A : Abs} {L : List Nat} {gh : GGh} {δg s₀ δ δu : Nat → Nat}
    {ex : Nat} {lg : LGh} {p : Nat} (hI : INV s A) (hG : GInvE s L gh δg ex)
    (hL : LInv s lg s₀ δ δu) (hp : LiveG s p) (hs : gSt s p = .splitting) (he : gSz s p = 0)
    (hql : gmin s.P ≤ gSz s (gLl s p)) (hqr : gmin s.P ≤ gSz s (gRr s p))
    (hg2 : 2 * gmin s.P ≤ s.P.G) :
    LInv (removeState s p) lg s₀ δ (Function.update δu (gC s p) (δu (gC s p) + 1)) := by
  have Fp := hG.fam p hp hs
  have hp' := hI.mem_glist_iff.mpr hp
  have hpp : gP s p ≠ p := by
    rw [hI.gList.prev p hp']; exact predOf_ne_self hI.gList.nodup p hp.1
  have hgPl : gP s p = gLl s p := by
    have := hI.gP_gN (hI.mem_glist_iff.mpr Fp.lLive) (by rw [Fp.lAdj]; exact hp.1)
    rw [Fp.lAdj] at this; exact this
  have R := removeState_spec hp.2.1 Fp.lLive.2.1 Fp.rLive.2.1 hpp
    (fun _ => by rw [hgPl]; exact Fp.lLive.2.1)
  have hlp := Fp.lp hI hp
  have hrp := Fp.rp hI hp
  have hlr := Fp.lr hI hp
  generalize hc : gC s p = c at *
  -- `p` is neither the first nor the last of its chunk
  obtain ⟨hcm, hpc⟩ := hI.mem_glist hp'
  rw [hc] at hcm hpc
  have hcs : c < s.C.size := ((hI.cAlloc c).mp hcm).2
  have hcf0 : cF s c ≠ NIL := by
    intro h0
    have hE := (hI.cEnds c hcm).1
    rw [h0] at hE
    cases hgr : A.grps c with
    | nil => rw [hgr] at hpc; simp at hpc
    | cons a t => rw [hgr] at hE; simp at hE; exact hI.gList.nonil (hE ▸ A.grps_sub_glist hcm (hgr ▸ by simp))
  have hpf : p ≠ cF s c := by
    have := hI.not_before_first hcf0 (hI.mem_glist_iff.mpr Fp.lLive) (by rw [Fp.lC, hc])
    rw [Fp.lAdj] at this; exact this
  have hpl : p ≠ cLs s c := by
    intro e
    have := hI.not_after_last hcf0 (a := gRr s p) (by rw [← e]; exact Fp.rAdj) Fp.rLive.1
    exact this (by rw [Fp.rC, hc])
  have hC : ∀ d, (removeState s p).C.getX d = s.C.getX d := by
    intro d
    rw [R.C, unlinkGroup_C (s := s) (g := p) d (by rw [hc]; exact hcs), hc]
    have h1 : ¬ (cF s c = p) := fun h => hpf h.symm
    have h2 : ¬ (cLs s c = p) := fun h => hpl h.symm
    split
    · next hd => subst hd; simp only [h1, h2, false_and, if_false]
    · rfl
  generalize removeState s p = s' at R hC ⊢
  have hU : (unlinkGroup s p).C.size = s.C.size := (unlinkGroup_rest (s := s) (g := p)).2.1
  have hLC : ∀ d, LiveC s' d ↔ LiveC s d := by intro d; simp only [LiveC, R.C, hU]
  have hcf : ∀ d, cSz s' d = cSz s d ∧ cSt s' d = cSt s d ∧ cSrc s' d = cSrc s d ∧
      cLl s' d = cLl s d ∧ cRr s' d = cRr s d ∧ cLs s' d = cLs s d := by
    intro d; simp only [cSz, cSt, cSrc, cLl, cRr, cLs, hC, and_self]
  have hfamC : ∀ x, famC s' x = famC s x := by
    intro x; simp only [famC, (hcf _).1, (hcf x).2.2.2.1, (hcf x).2.2.2.2.1]
  generalize hl : gLl s p = l at *
  generalize hr : gRr s p = r at *
  have hlL : LiveG s l := hl ▸ Fp.lLive
  have hrL : LiveG s r := hr ▸ Fp.rLive
  have hlst : gSt s l = .overflow := hl ▸ Fp.lSt
  have hrst : gSt s r = .overflow := hr ▸ Fp.rSt
  have hlc : gC s l = c := by rw [← hl, Fp.lC, hc]
  have hrc : gC s r = c := by rw [← hr, Fp.rC, hc]
  have hlp' : l ≠ p := hl ▸ hlp
  have hrp' : r ≠ p := hr ▸ hrp
  -- units: one more in `c`
  have hunits : ∀ d, units s' d + δu d = units s d + Function.update δu c (δu c + 1) d := by
    intro d
    by_cases hdc : d = c
    · subst hdc
      have : units s' d = units s d + 1 := by
        refine units_swap (p := p) (l := l) (r := r) ⟨hp, hc, by rw [hs]; simp⟩
          (fun h => h.2.2 hlst) (fun h => h.2.2 hrst) hlr ?_ ?_ ?_ ?_
        · refine ⟨(R.live _).mpr ⟨hlL, hlp'⟩, by rw [R.chk, hlc], ?_⟩
          rw [R.st, if_pos (Or.inl rfl)]; simp
        · refine ⟨(R.live _).mpr ⟨hrL, hrp'⟩, by rw [R.chk, hrc], ?_⟩
          rw [R.st, if_pos (Or.inr rfl)]; simp
        · intro h; exact ((R.live p).mp h.1).2 rfl
        · intro z h1 h2 h3
          unfold UnitG; rw [R.live, R.chk, R.st, if_neg (not_or.mpr ⟨h2, h3⟩)]
          simp [h1]
      rw [this, Function.update_self]; omega
    · rw [Function.update_of_ne hdc]
      congr 1
      apply units_congr
      intro z
      unfold UnitG; rw [R.live, R.chk, R.st]
      by_cases h1 : z = l ∨ z = r
      · rw [if_pos h1]
        have hzc : gC s z = c := by
          rcases h1 with rfl | rfl
          · exact hlc
          · exact hrc
        simp only [hzc, Ne.symm hdc]; simp
      · rw [if_neg h1]
        by_cases h3 : z = p
        · subst h3; simp [hc, Ne.symm hdc]
        · simp [h3]
  have hgrps : ∀ d, ∀ z, z ∈ GrpsC s' d ↔ z ∈ GrpsC s d ∧ z ≠ p := by
    intro d z; simp only [mem_GrpsC, R.live, R.chk]; tauto
  have hpend : ∀ d, pending s' lg d = pending s lg d := by
    intro d; unfold pending
    congr 1
    ext z
    simp only [Finset.mem_filter, hgrps, R.st]
    constructor
    · rintro ⟨⟨hz, -⟩, h1, h2⟩
      refine ⟨hz, h1, ?_⟩
      by_cases hlr' : z = l ∨ z = r
      · rcases hlr' with rfl | rfl
        · rw [hlst]; simp
        · rw [hrst]; simp
      · rwa [if_neg hlr'] at h2
    · rintro ⟨hz, h1, h2⟩
      have hzp : z ≠ p := by rintro rfl; exact h2 hs
      refine ⟨⟨hz, hzp⟩, h1, ?_⟩
      split
      · simp
      · exact h2
  have hterm : ∀ z, LiveG s z → z ≠ p → z ≠ l → z ≠ r → chTerm s' lg z = chTerm s lg z := by
    intro z hz h1 h2 h3
    unfold chTerm
    rw [R.st, if_neg (not_or.mpr ⟨h2, h3⟩), R.l, R.sz, R.P]
    simp only [famT, R.sz, R.l, R.r]
  have hcharge : charge s' lg c ≤ charge s lg c := by
    rw [charge_eq, charge_eq]
    have hpG : p ∈ GrpsC s c := mem_GrpsC.mpr ⟨hp, hc⟩
    have hlG : l ∈ GrpsC s c := mem_GrpsC.mpr ⟨hlL, hlc⟩
    have hrG : r ∈ GrpsC s c := mem_GrpsC.mpr ⟨hrL, hrc⟩
    have hG' : GrpsC s' c = (GrpsC s c).erase p := by
      ext z; rw [hgrps, Finset.mem_erase]; tauto
    rw [hG']
    have hlG' : l ∈ (GrpsC s c).erase p := Finset.mem_erase.mpr ⟨hlp', hlG⟩
    have hrG' : r ∈ ((GrpsC s c).erase p).erase l :=
      Finset.mem_erase.mpr ⟨Ne.symm hlr, Finset.mem_erase.mpr ⟨hrp', hrG⟩⟩
    rw [← Finset.add_sum_erase _ _ hlG', ← Finset.add_sum_erase _ _ hrG']
    rw [← Finset.add_sum_erase _ _ hpG, ← Finset.add_sum_erase _ _ hlG', ← Finset.add_sum_erase _ _ hrG']
    have hrest : ∑ z ∈ (((GrpsC s c).erase p).erase l).erase r, chTerm s' lg z =
        ∑ z ∈ (((GrpsC s c).erase p).erase l).erase r, chTerm s lg z := by
      refine Finset.sum_congr rfl fun z hz => ?_
      simp only [Finset.mem_erase] at hz
      exact hterm z (mem_GrpsC.mp hz.2.2.2).1 hz.2.2.1 hz.2.1 hz.1
    rw [hrest]
    -- the siblings' terms against the family's
    have hl0 : chTerm s lg l = 0 := by
      unfold chTerm; rw [hlst]; simp
    have hr0 : chTerm s lg r = 0 := by
      unfold chTerm; rw [hrst]; simp
    have hl' : chTerm s' lg l = if lg.child l = true then gmin s.P + gSz s l - s.P.G else 0 := by
      unfold chTerm; rw [R.st, if_pos (Or.inl rfl), R.sz, R.P]; simp
    have hr' : chTerm s' lg r = if lg.child r = true then gmin s.P + gSz s r - s.P.G else 0 := by
      unfold chTerm; rw [R.st, if_pos (Or.inr rfl), R.sz, R.P]; simp
    have hpt : chTerm s lg p = if lg.child l = true then gSz s l + gSz s r - s.P.G else 0 := by
      unfold chTerm; rw [hs, hl]; simp only [true_and]
      split
      · simp only [famT, hl, hr, he]; omega
      · simp
    have hfc : lg.child l = lg.child r := by have := hL.famChild p hp hs; rw [hl, hr] at this; exact this
    rw [hl0, hr0, hl', hr', hpt, ← hfc]
    split <;> omega
  refine
    { gaps := ?_, range := ?_, hv := hL.hv, pb := hL.pb, pf := hL.pf, roots := ?_, claim2 := ?_,
      insQ := ?_, insO := ?_, insS := ?_, arrS := ?_, arrN := ?_, e0 := ?_, famChild := ?_ }
  · intro h hh hlast
    rw [R.live] at hh
    rw [R.chk, (hcf _).2.2.2.2.2] at hlast; rw [R.chk, R.lab, R.lab, R.P]
    by_cases hhl : h = l
    · rw [hhl]
      rw [← hgPl, R.nextp (by rw [hgPl]; exact hlL.1), hgPl, Fp.rAdj, hr]
      have hlN : gN s l = p := by rw [← hl]; exact Fp.lAdj
      have hl1 := hL.gaps l hlL (by
        intro e; rw [hlc] at e
        exact hI.not_after_last hcf0 (a := p) (by rw [← e]; exact hlN) hp.1 hc)
      rw [hlN, hlc] at hl1
      have hp1 := hL.gaps p hp (by rw [hc]; exact hpl)
      rw [Fp.rAdj, hc, hr] at hp1
      rw [hlc]
      generalize s.P.D_g / 2 ^ lg.hv c = t at hl1 hp1 ⊢
      omega
    · rw [R.next h hh.2 (by rw [hgPl]; exact hhl)]
      exact hL.gaps h hh.1 hlast
  · intro h hh; rw [R.live] at hh; rw [R.chk, R.lab, R.P]; exact hL.range h hh.1
  · intro d hd; rw [hLC] at hd; rw [hpend]; exact hL.roots d hd
  · intro d hd; rw [hLC] at hd; rw [R.P]
    by_cases hdc : d = c
    · subst hdc; have := hL.claim2 d hd; omega
    · have : charge s' lg d = charge s lg d := by
        rw [charge_eq, charge_eq]
        have hG' : GrpsC s' d = GrpsC s d := by
          ext z; rw [hgrps]
          constructor
          · exact fun h => h.1
          · intro h; exact ⟨h, by rintro rfl; exact hdc ((mem_GrpsC.mp h).2.symm.trans hc)⟩
        rw [hG']
        refine Finset.sum_congr rfl fun z hz => ?_
        have hz' := mem_GrpsC.mp hz
        have hzp : z ≠ p := by rintro rfl; exact hdc (hz'.2.symm.trans hc)
        have hzl : z ≠ l := by rintro rfl; exact hdc (hz'.2.symm.trans hlc)
        have hzr : z ≠ r := by rintro rfl; exact hdc (hz'.2.symm.trans hrc)
        exact hterm z hz'.1 hzp hzl hzr
      rw [this]; exact hL.claim2 d hd
  · intro d hd hds; rw [hLC] at hd; rw [(hcf d).2.1] at hds; rw [(hcf d).1, R.P]
    exact hL.insQ d hd hds
  · intro d hd hds; rw [hLC] at hd; rw [(hcf d).2.1] at hds; rw [(hcf d).2.2.1, hfamC]
    exact hL.insO d hd hds
  · intro d hd hds; rw [hLC] at hd; rw [(hcf d).2.1] at hds; rw [hfamC, R.P]
    exact hL.insS d hd hds
  · intro x hx hxs; rw [hLC] at hx; rw [(hcf x).2.1] at hxs
    rw [(hcf x).2.2.2.1, (hcf x).2.2.2.2.1, (hcf _).1, (hcf x).1, (hcf _).1, R.P]
    have h1 := hL.arrS x hx hxs
    have h2 := hunits x
    omega
  · intro d hd hds; rw [hLC] at hd; rw [(hcf d).2.1] at hds; rw [R.P]; exact hL.arrN d hd hds
  · intro d hd hds; rw [hLC] at hd; rw [(hcf d).2.1] at hds; rw [(hcf d).1]; exact hL.e0 d hd hds
  · intro z hz hzs
    rw [R.live] at hz
    have hzlr : ¬ (z = l ∨ z = r) := by
      rintro (rfl | rfl) <;> rw [R.st] at hzs <;> simp at hzs
    rw [R.st, if_neg hzlr] at hzs
    rw [R.l, R.r]; exact hL.famChild z hz.1 hzs

end OM.Proof
