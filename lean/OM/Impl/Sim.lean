import OM.Impl.Fields

/-!
# M6: the compiled code simulates the source

`sim`: if machine state `m` holds core `s` (`Enc`) with the same locals, then running the
compiled statement on `m` ends exactly as `evalF` says: the same outcome, a machine state that
holds the resulting core, the same locals, and **the same number of steps**. A `.bug` outcome
promises nothing (the agreement lemmas exclude it).
-/

namespace OM.Impl

open OM.Model
open OM.Machine (Reg Arr BinOp UnOp State Out exec)

variable {p : Nat} {κ : Caps}

/-! ### The encoding under machine updates -/

theorem Enc.congr {s : Core} {m m' : State} (h : Enc p κ s m) (hm : m'.mem = m.mem)
    (hc : m'.cap = m.cap) : Enc p κ s m' :=
  ⟨fun f => by rw [hc]; exact h.cap f, fun f i hi => by rw [hm]; exact h.mem f i hi,
    fun t => by rw [hc]; exact h.scap t, fun t => by rw [hm]; exact h.smem t, h.sle,
    by rw [hc]; exact h.pcap, fun k => by rw [hm]; exact h.pmem k⟩

theorem Enc.bump {s : Core} {m : State} (h : Enc p κ s m) (v : Nat) : Enc p κ s (m.bump v) :=
  h.congr rfl rfl
theorem Enc.setLoc {s : Core} {m : State} (h : Enc p κ s m) (x : Reg) (v : Nat) :
    Enc p κ s (m.setLoc x v) := h.congr rfl rfl
theorem Enc.withLoc {s : Core} {m : State} (h : Enc p κ s m) (l : Reg → Nat) :
    Enc p κ s { m with loc := l } := h.congr rfl rfl

theorem Enc.write {s s' : Core} {m : State} (h : Enc p κ s m) {f : Fld} {j v : Nat}
    (hs : f.set κ s j v = some s') :
    Enc p κ s' (m.write (arrF p f) j v) := by
  obtain ⟨hT, hP⟩ := Fld.set_keep hs
  refine ⟨fun g => h.cap g, fun g i hi => ?_, fun t => h.scap t, fun t => ?_, fun t => ?_, h.pcap,
    fun k => ?_⟩
  · simp only [State.write]
    rw [Fld.get_set hs g hi]
    by_cases eg : arrF p g = arrF p f
    · have := arrF_inj eg; subst this
      rw [if_pos eg]; simp only [State.upd]
      by_cases ei : i = j
      · subst ei; simp
      · rw [if_neg ei, if_neg (fun h => ei h.2)]; exact h.mem g i hi
    · rw [if_neg eg, if_neg (fun h' => eg (by rw [h'.1]))]; exact h.mem g i hi
  · simp only [State.write]; rw [if_neg (Ne.symm (arrF_ne_arrS p f t)), hT]; exact h.smem t
  · rw [hT]; exact h.sle t
  · simp only [State.write]; rw [if_neg (Ne.symm (arrF_ne_arrP p f)), hP]; exact h.pmem k

theorem Enc.push {s : Core} {m : State} (h : Enc p κ s m) {t : Tbl} (ht : t.size s < κ.tbl t) :
    Enc p κ (t.push s) (m.write (arrS p t) 0 (t.size s + 1)) := by
  refine ⟨fun g => h.cap g, fun g i hi => ?_, fun t' => h.scap t', fun t' => ?_, fun t' => ?_,
    h.pcap, fun k => ?_⟩
  · simp only [State.write]; rw [if_neg (arrF_ne_arrS p g t), Tbl.push_get]; exact h.mem g i hi
  · simp only [State.write, Tbl.push_size]
    by_cases e : arrS p t' = arrS p t
    · have := arrS_inj e; subst this; rw [if_pos e, if_pos rfl]; simp [State.upd]
    · rw [if_neg e, if_neg (fun h' => e (by rw [h']))]; exact h.smem t'
  · rw [Tbl.push_size]; split
    · next e => subst e; omega
    · exact h.sle t'
  · simp only [State.write]; rw [if_neg (Ne.symm (arrS_ne_arrP p t)), Tbl.push_P]; exact h.pmem k

/-! ### Expressions -/

theorem Exp.ev_compile {s : Core} {m : State} {L : Loc} (h : Enc p κ s m) (hL : m.loc = L) :
    ∀ (e : Exp) {v : Nat}, e.ev κ s L = some v → (e.compile p).eval m = some v
  | .lit n, v, hv => by simp [Exp.ev] at hv; simp [Exp.compile, hv]
  | .var x, v, hv => by simp [Exp.ev] at hv; simp [Exp.compile, hL, hv]
  | .rd f i, v, hv => by
    simp only [Exp.ev, Option.bind_eq_some_iff] at hv
    obtain ⟨j, hj, hv⟩ := hv
    split at hv
    · next hlt =>
      cases hv
      simp only [Exp.compile, OM.Machine.Expr.eval, Exp.ev_compile h hL i hj, Option.bind_some,
        h.cap f, if_pos hlt, h.mem f j hlt]
    · simp at hv
  | .size t, v, hv => by
    simp [Exp.ev] at hv; subst hv
    simp [Exp.compile, h.scap t, h.smem t]
  | .prm k, v, hv => by
    simp [Exp.ev] at hv; subst hv
    simp [Exp.compile, h.pcap, h.pmem k, k.idx_lt]
  | .bin op a b, v, hv => by
    simp only [Exp.ev, Option.bind_eq_some_iff] at hv
    obtain ⟨x, hx, y, hy, hv⟩ := hv
    simp only [Exp.compile, OM.Machine.Expr.eval, Exp.ev_compile h hL a hx, Exp.ev_compile h hL b hy,
      Option.bind_some, hv]
  | .un op a, v, hv => by
    simp only [Exp.ev, Option.map_eq_some_iff] at hv
    obtain ⟨x, hx, hv⟩ := hv
    simp only [Exp.compile, OM.Machine.Expr.eval, Exp.ev_compile h hL a hx, Option.map_some, hv]

theorem evList_compile {s : Core} {m : State} {L : Loc} (h : Enc p κ s m) (hL : m.loc = L) :
    ∀ (es : List Exp) {vs : List Nat}, evList κ s L es = some vs →
      OM.Machine.evalList m (es.map (Exp.compile p)) = some vs
  | [], vs, hv => by simp [evList] at hv; subst hv; rfl
  | e :: es, vs, hv => by
    simp only [evList, List.mapM_cons] at hv
    cases he : e.ev κ s L with
    | none => simp [he] at hv
    | some v =>
      cases hes : es.mapM (·.ev κ s L) with
      | none => simp [he, hes] at hv
      | some ws =>
        simp [he, hes] at hv; subst hv
        have := evList_compile h hL es (vs := ws) hes
        simp only [OM.Machine.evalList, List.map_cons, List.mapM_cons] at this ⊢
        rw [Exp.ev_compile h hL e he, this]; rfl

theorem costList_compile (es : List Exp) :
    OM.Machine.costList (es.map (Exp.compile p)) = costList es := by
  simp only [OM.Machine.costList, costList, List.map_map]
  congr 1
  exact List.map_congr_left (fun e _ => Exp.cost_compile p e)

/-! ### Statements -/

/-- Outcome `r` of the source and outcome `o` of the compiled code agree. -/
def Agree (p : Nat) (κ : Caps) : Res → Out → Prop
  | .ok s L n, o => o.status = .ok ∧ Enc p κ s o.st ∧ o.st.loc = L ∧ o.cost = n
  | .fail s L n, o => o.status = .fail ∧ Enc p κ s o.st ∧ o.st.loc = L ∧ o.cost = n
  | .bug, _ => True

theorem Agree.addCost {r : Res} {o : Out} (h : Agree p κ r o) (c : Nat) :
    Agree p κ (r.addCost c) ⟨o.st, c + o.cost, o.status⟩ := by
  cases r with
  | ok s L n => obtain ⟨h1, h2, h3, h4⟩ := h; exact ⟨h1, h2, h3, by simp [h4]⟩
  | fail s L n => obtain ⟨h1, h2, h3, h4⟩ := h; exact ⟨h1, h2, h3, by simp [h4]⟩
  | bug => trivial

theorem Agree.bind {r : Res} {o : Out} (h : Agree p κ r o) {g : Core → Loc → Res} {k : State → Out}
    (hg : ∀ s L m, Enc p κ s m → m.loc = L → Agree p κ (g s L) (k m)) :
    Agree p κ (r.bind g) (o.bind k) := by
  cases r with
  | ok s L n =>
    obtain ⟨h1, h2, h3, h4⟩ := h
    have := (hg s L o.st h2 h3).addCost n
    simp only [Res.bind, Out.bind, h1]
    rw [h4]; exact this
  | fail s L n =>
    obtain ⟨h1, h2, h3, h4⟩ := h
    simp only [Res.bind, Out.bind, h1]; exact ⟨h1, h2, h3, h4⟩
  | bug => trivial

theorem Fld.set_lt {s s' : Core} {f : Fld} {j v : Nat} (h : f.set κ s j v = some s')
    (hle : ∀ t, t.size s ≤ κ.tbl t) : j < f.cap κ := by
  cases f with
  | e k => simp only [Fld.set] at h; split at h <;> [skip; simp at h]; next hc =>
      have := hle .E; simp [Fld.cap, Tbl.size] at *; omega
  | g k => simp only [Fld.set] at h; split at h <;> [skip; simp at h]; next hc =>
      have := hle .G; simp [Fld.cap, Tbl.size] at *; omega
  | c k => simp only [Fld.set] at h; split at h <;> [skip; simp at h]; next hc =>
      have := hle .C; simp [Fld.cap, Tbl.size] at *; omega
  | n k => simp only [Fld.set] at h; split at h <;> [skip; simp at h]; next hc =>
      have := hle .N; simp [Fld.cap, Tbl.size] at *; omega
  | a k => simp only [Fld.set] at h; split at h <;> [skip; simp at h]; next hc =>
      simp [Fld.cap]; exact hc
  | s k => simp only [Fld.set] at h; split at h <;> [skip; simp at h]; next hc =>
      simp [Fld.cap]; have := hc.1; omega

theorem sim_runFor {b : Stm} {x : Reg}
    (ih : ∀ s L m, Enc p κ s m → m.loc = L → Agree p κ (evalF κ b s L) (exec (b.compile p) m)) :
    ∀ n k s L m, Enc p κ s m → m.loc = L →
      Agree p κ (runForF (evalF κ b) x k n s L) (OM.Machine.runFor (exec (b.compile p)) x k n m)
  | 0, _, s, L, m, h, hL => ⟨rfl, h, hL, rfl⟩
  | n + 1, k, s, L, m, h, hL => by
    simp only [runForF, OM.Machine.runFor]
    refine Agree.bind ?_ (fun s' L' m' h' hL' => sim_runFor ih n (k + 1) s' L' m' h' hL')
    have := (ih s (OM.Machine.State.upd L x k) (m.setLoc x k) (h.setLoc x k) (by simp [hL])).addCost 1
    exact this

/-- **The compiled code simulates the source**, step for step. -/
theorem sim (c : Stm) : ∀ {s : Core} {L : Loc} {m : State}, Enc p κ s m → m.loc = L →
    Agree p κ (evalF κ c s L) (exec (c.compile p) m) := by
  induction c with
  | skip => intro s L m h hL; exact ⟨rfl, h, hL, rfl⟩
  | assign x e =>
    intro s L m h hL
    simp only [evalF]
    cases he : e.ev κ s L with
    | none => trivial
    | some v =>
      simp only [Stm.compile, exec, Exp.ev_compile h hL e he]
      exact ⟨rfl, (h.bump _).setLoc x v, by simp [hL], by simp [Exp.cost_compile]⟩
  | wr f i e =>
    intro s L m h hL
    simp only [evalF]
    cases hi : i.ev κ s L with
    | none => trivial
    | some j =>
      cases he : e.ev κ s L with
      | none => trivial
      | some v =>
        simp only
        cases hs : f.set κ s j v with
        | none => trivial
        | some s' =>
          have hj := Fld.set_lt hs h.sle
          simp only [Stm.compile, exec, Exp.ev_compile h hL i hi, Exp.ev_compile h hL e he]
          rw [if_pos (by simp [h.cap f]; exact hj)]
          exact ⟨rfl, ((h.bump _).bump _).write hs, by simp [hL], by simp [Exp.cost_compile]⟩
  | push t x =>
    intro s L m h hL
    simp only [evalF]
    split
    · next ht =>
      have h1 : Enc p κ s ((m.bump (t.size s)).setLoc x (t.size s)) := (h.bump _).setLoc _ _
      have h2 := ((h1.bump (t.size s)).bump (t.size s + 1)).push ht
      simp only [Stm.compile, exec, OM.Machine.Out.bind, OM.Machine.Expr.eval, State.setLoc, State.bump,
        State.upd, h.scap t, h.smem t, Nat.zero_lt_one, Option.bind_some, OM.Machine.BinOp.eval, if_pos]
      refine ⟨rfl, h2.congr rfl rfl, by simp [hL], rfl⟩
    · trivial
  | seq c d ihc ihd =>
    intro s L m h hL
    simp only [evalF, Stm.compile, exec]
    exact Agree.bind (ihc h hL) (fun s' L' m' h' hL' => ihd h' hL')
  | ite c t f iht ihf =>
    intro s L m h hL
    simp only [evalF]
    cases hc : c.ev κ s L with
    | none => trivial
    | some v =>
      simp only [Stm.compile, exec, Exp.ev_compile h hL c hc, OM.Machine.Out.bind]
      rw [← Exp.cost_compile p c]
      by_cases hv : v ≠ 0
      · simp only [if_pos hv]; exact (iht (h.bump _) (by simp [hL])).addCost _
      · simp only [if_neg hv]; exact (ihf (h.bump _) (by simp [hL])).addCost _
  | loop x n b ihb =>
    intro s L m h hL
    simp only [evalF]
    cases hn : n.ev κ s L with
    | none => trivial
    | some k =>
      simp only [Stm.compile, exec, Exp.ev_compile h hL n hn, OM.Machine.Out.bind]
      rw [← Exp.cost_compile p n]
      exact (sim_runFor (fun s L m h hL => ihb h hL) k 0 s L _ (h.bump _) (by simp [hL])).addCost _
  | call nm ps b rs args ds ihb =>
    intro s L m h hL
    simp only [evalF]
    cases ha : evList κ s L args with
    | none => trivial
    | some vs =>
      simp only [Stm.compile, exec, evList_compile h hL args ha]
      have hb := ihb (s := s) (L := OM.Machine.State.setLocs (fun _ => 0) ps vs)
        (m := (m.bump (OM.Machine.maxvList m (args.map (Exp.compile p)))).enter ps vs)
        ((h.bump (OM.Machine.maxvList m (args.map (Exp.compile p)))).congr rfl rfl) (by simp)
      revert hb
      generalize evalF κ b s (OM.Machine.State.setLocs (fun _ => 0) ps vs) = r
      generalize exec (b.compile p) _ = o
      intro hb
      cases r with
      | ok s' L' n =>
        obtain ⟨h1, h2, h3, h4⟩ := hb
        simp only [h1]
        exact ⟨rfl, h2.congr rfl rfl, by simp [hL, h3], by simp only [costList_compile, h4]⟩
      | fail s' L' n =>
        obtain ⟨h1, h2, h3, h4⟩ := hb
        simp only [h1]
        exact ⟨rfl, h2.withLoc _, by simp [hL], by simp only [costList_compile, h4]⟩
      | bug => trivial
  | fail => intro s L m h hL; exact ⟨rfl, h, hL, rfl⟩
  | bug => intro s L m h hL; trivial
  | «catch» c hd ihc ihh =>
    intro s L m h hL
    simp only [evalF, Stm.compile, exec]
    have hc := ihc h hL
    revert hc
    generalize evalF κ c s L = r
    generalize exec (c.compile p) m = o
    intro hc
    cases r with
    | ok s' L' n =>
      obtain ⟨h1, h2, h3, h4⟩ := hc
      simp only [h1]; exact ⟨rfl, h2, h3, by simp [h4]⟩
    | fail s' L' n =>
      obtain ⟨h1, h2, h3, h4⟩ := hc
      simp only [h1]
      have := (ihh h2 h3).addCost (1 + n)
      rw [h4]; exact this
    | bug => trivial

end OM.Impl
