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

structure LInv (s : Core) (lg : LGh) (s₀ : Nat → Nat) : Prop where
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
      3 * (unitsOf s.P (s₀ x) + (famC s x - s₀ x))
  arrN : ∀ c, LiveC s c → cSt s c ≠ .overflow → lg.arB c + lg.arF c ≤ 3 * Mu s.P
  /-- The quiet size at the start of the quiet period. -/
  e0 : ∀ c, LiveC s c → cSt s c = .quiet → lg.e0 c ≤ cSz s c

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
