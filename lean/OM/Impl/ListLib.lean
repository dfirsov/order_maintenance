import OM.Impl.Loop

/-!
# M6: a list library for the core language

Procedures on list `k` of record `i`, each with its agreement lemma:
* `findP k`: the position of the first element with key `x` (`List.findIdx`), or the length.
-/

namespace OM.Impl

open OM.Model
open OM.Machine (Reg BinOp UnOp)

/-- The key of element `m` of a list (0 past the end). -/
abbrev key (l : List (Nat × Nat)) (m : Nat) : Nat := (l.getD m (0, 0)).1

def findP (k : LK) : Proc where
  name := "find"
  params := ["i", "x"]
  rets := ["r"]
  body :=
    "n" ::= .llen k "i" ;;
    "r" ::= "n" ;;
    "f" ::= 0 ;;
    .loop "j" "n" (.ite (("f" =ₑ 0) &&ₑ (.lrd k false "i" "j" =ₑ "x")) ("r" ::= "j" ;; "f" ::= 1) .skip)

theorem findIdx_key (l : List (Nat × Nat)) (x : Nat) :
    (∀ m < l.length, key l m ≠ x) → l.findIdx (·.1 == x) = l.length := by
  intro h
  apply List.findIdx_eq_length.mpr
  intro y hy
  obtain ⟨m, hm, rfl⟩ := List.getElem_of_mem hy
  have := h m hm
  simp only [key, List.getD_eq_getElem _ _ hm] at this
  simpa using this

theorem findIdx_key_eq (l : List (Nat × Nat)) (x r : Nat) (hr : r < l.length) (h1 : key l r = x)
    (h2 : ∀ m < r, key l m ≠ x) : l.findIdx (·.1 == x) = r := by
  apply (List.findIdx_eq hr).mpr
  refine ⟨?_, fun m hm => ?_⟩
  · simp only [key, List.getD_eq_getElem _ _ hr] at h1; simpa using h1
  · have := h2 m hm
    simp only [key] at this; rw [List.getD_eq_getElem _ _ (by omega)] at this; simpa using this

/-- **`findP` computes `findIdx`.** -/
theorem findP_agree (κ : Caps) (k : LK) (s : Core) (L : Loc) {i x : Nat} (hi : L "i" = i) (hx : L "x" = x)
    (hir : i < κ.lrec k) :
    ∃ L' c, evalF κ (findP k).body s L = .ok s L' c ∧ L' "r" = (k.view s i).findIdx (·.1 == x) ∧
      c ≤ 20 + 20 * (k.view s i).length := by
  set l := k.view s i
  have hlen : (Exp.llen k (.var "i")).ev κ s L = some l.length := by simp [Exp.ev, hi, hir, l]
  -- the three assignments
  let I : Nat → Core → Loc → Prop := fun j s' L' => s' = s ∧ L' "i" = i ∧ L' "x" = x ∧ L' "n" = l.length ∧
    ((L' "f" = 0 ∧ L' "r" = l.length ∧ ∀ m < j, key l m ≠ x) ∨
     (L' "f" = 1 ∧ L' "r" < j ∧ key l (L' "r") = x ∧ ∀ m < L' "r", key l m ≠ x))
  have hn : (Exp.var "n").ev κ s
      (OM.Machine.State.upd (OM.Machine.State.upd (OM.Machine.State.upd L "n" l.length) "r" l.length) "f" 0) =
      some l.length := by simp [Exp.ev, OM.Machine.State.upd]
  obtain ⟨s', L', c, he, hc, hI⟩ := evalF_loop (x := "j") (b := .ite (("f" =ₑ 0) &&ₑ (.lrd k false "i" "j" =ₑ "x"))
    ("r" ::= "j" ;; "f" ::= 1) .skip) hn I 17
    ⟨rfl, by simp [OM.Machine.State.upd, hi], by simp [OM.Machine.State.upd, hx], by simp [OM.Machine.State.upd],
      Or.inl ⟨by simp [OM.Machine.State.upd], by simp [OM.Machine.State.upd], fun m hm => absurd hm (by omega)⟩⟩
    (by
      intro j hj s1 L1 ⟨hs, h1, h2, h3, h4⟩
      subst hs
      have hjl : j < l.length := hj
      by_cases hf : L1 "f" = 0 ∧ key l j = x
      · refine ⟨s1, OM.Machine.State.upd (OM.Machine.State.upd (OM.Machine.State.upd L1 "j" j) "r" j) "f" 1, 17,
          ?_, by omega, rfl, by simp [OM.Machine.State.upd, h1], by simp [OM.Machine.State.upd, h2],
          by simp [OM.Machine.State.upd, h3], Or.inr ⟨by simp [OM.Machine.State.upd], by simp [OM.Machine.State.upd],
          by simp [OM.Machine.State.upd]; exact hf.2, ?_⟩⟩
        · have : (l.getD j (0, 0)).1 = x := hf.2
          rw [List.getD_eq_getElem _ _ hjl] at this
          simp [evalF, Exp.ev, OM.Machine.State.upd, h1, h2, hir, hjl, hf.1, this, Res.bind, Res.addCost,
            Exp.cost, l]
        · simp only [OM.Machine.State.upd, if_true]
          rcases h4 with ⟨-, -, h⟩ | ⟨h, -⟩
          · exact h
          · rw [hf.1] at h; simp at h
      · refine ⟨s1, OM.Machine.State.upd L1 "j" j, 14, ?_, by omega, rfl, by simp [OM.Machine.State.upd, h1],
          by simp [OM.Machine.State.upd, h2], by simp [OM.Machine.State.upd, h3], ?_⟩
        · have hc : ¬(L1 "f" = 0 ∧ (LK.view s1 i k)[j].1 = x) := by
            intro h; apply hf; refine ⟨h.1, ?_⟩
            show (l.getD j (0, 0)).1 = x; rw [List.getD_eq_getElem _ _ hjl]; exact h.2
          have hc' : L1 "f" = 0 → ¬(LK.view s1 i k)[j].1 = x := fun a b => hc ⟨a, b⟩
          simp [evalF, Exp.ev, OM.Machine.State.upd, h1, h2, hir, hjl, Res.bind, Res.addCost, Exp.cost, l]
          rw [if_pos hc']
        · simp only [OM.Machine.State.upd, show ("f" = "j") = False by decide, show ("r" = "j") = False by decide,
            ite_false]
          rcases h4 with ⟨h5, h6, h7⟩ | ⟨h5, h6, h7, h8⟩
          · refine Or.inl ⟨h5, h6, fun m hm => ?_⟩
            rcases Nat.lt_succ_iff_lt_or_eq.mp hm with hm | rfl
            · exact h7 m hm
            · exact fun e => hf ⟨h5, e⟩
          · exact Or.inr ⟨h5, by omega, h7, h8⟩)
  obtain ⟨hss, -, -, -, hI⟩ := hI; rw [hss] at he
  have a1 := evalF_assign_ok (x := "n") hlen
  have a2 := evalF_assign_ok (κ := κ) (s := s) (x := "r") (e := .var "n")
    (L := OM.Machine.State.upd L "n" l.length) (v := l.length) (by simp [Exp.ev, OM.Machine.State.upd])
  have a3 := evalF_assign_ok (κ := κ) (s := s) (x := "f") (e := (0 : Exp))
    (L := OM.Machine.State.upd (OM.Machine.State.upd L "n" l.length) "r" l.length) (v := 0) (by simp [Exp.ev])
  refine ⟨L', (1 + (Exp.llen k (.var "i")).cost) + ((1 + (Exp.var "n").cost) + ((1 + (0 : Exp).cost) + c)),
    ?_, ?_, ?_⟩
  · show evalF κ (_ ;; (_ ;; (_ ;; _))) s L = _
    rw [evalF_seq_ok a1, evalF_seq_ok a2, evalF_seq_ok a3, he]; rfl
  · rcases hI with ⟨-, h6, h7⟩ | ⟨-, h6, h7, h8⟩
    · rw [h6]; exact (findIdx_key l x h7).symm
    · exact (findIdx_key_eq l x _ h6 h7 h8).symm
  · simp only [Exp.cost] at hc ⊢; nlinarith

end OM.Impl
