import OM.Impl.ListLib
import OM.Proof.Top.StartData

/-!
# M6: `startDrain`'s side list (`drainSide`), built in place

`drainSideP` builds the side list of `v` directly in `v`'s side list: first `sidesOf` (a fold
over `v`'s table with `assocSet`), then, above height 1, `fixSides` (ghost entries take the side of
their first target).
-/

namespace OM.Impl

open OM.Model

/-- A side list as stored: sides as 0 / 1. -/
abbrev encS (l : List (Nat × Side)) : List (Nat × Nat) := l.map fun q => (q.1, sideN q.2)

theorem lookup_encS (l : List (Nat × Side)) (x : Nat) : lookup (encS l) x = (lookup l x).map sideN := by
  unfold lookup
  rw [List.find?_map]
  simp [Function.comp_def, Option.map_map]

theorem assocSet_encS (l : List (Nat × Side)) (x : Nat) (st : Side) :
    assocSet (encS l) x (sideN st) = encS (assocSet l x st) := by
  unfold assocSet
  simp only [List.any_map, Function.comp_def]
  split
  · simp only [List.map_map, Function.comp_def]
    congr 1; funext p; split <;> rfl
  · simp

theorem sideOfN_sideN (st : Side) : sideOfN (sideN st) = st := by cases st <;> rfl

theorem sideN_le (st : Side) : sideN st ≤ 1 := by cases st <;> simp [sideN]

theorem fixSides_append (ns : Array Node) : ∀ (l1 l2 : List Nat) (side : List (Nat × Side)),
    fixSides ns (l1 ++ l2) side = (fixSides ns l1 side).bind (fixSides ns l2)
  | [], l2, side => by simp [fixSides]
  | e :: l1, l2, side => by
    simp only [List.cons_append, fixSides]
    split
    · split
      · exact fixSides_append ns l1 l2 _
      · rfl
    · exact fixSides_append ns l1 l2 side

open OM.Machine (Reg BinOp UnOp)
open OM.Proof.Top (sideStep sidesOf_eq)

local notation "upd" => OM.Machine.State.upd

theorem put_side_encS (s : Core) (v : Nat) (l : List (Nat × Side)) :
    LK.put s v (encS l) .side = { s with nodes := s.nodes.modify v fun n => { n with side := l } } := by
  simp [LK.put, encS, List.map_map, Function.comp_def, sideOfN_sideN]

@[simp] theorem LK.put_nodes_size (s : Core) (i : Nat) (l : List (Nat × Nat)) (k : LK) :
    (k.put s i l).nodes.size = s.nodes.size := by
  cases k <;> simp [LK.put]

/-- One round of `sidesOf`: entry `j` of `v`'s table takes the current side (`right` from `b` on). -/
def sideBody : Stm :=
  "e" ::= .lrd .table false "v" "j" ;;
  .ite ("e" =ₑ "b") ("sd" ::= 1) .skip ;;
  (assocSetP .side).call [.var "v", .var "e", .var "sd"] []

/-- `sidesOf` over the first `j` entries. -/
abbrev preSides (o : List Nat) (b j : Nat) : List (Nat × Side) × Side := (o.take j).foldl (sideStep b) ([], .left)

theorem length_preSides (o : List Nat) (b j : Nat) : (preSides o b j).1.length ≤ j := by
  have := OM.Proof.Top.length_sideStep_fold b (o.take j) ([], .left)
  show (List.foldl (sideStep b) ([], Side.left) (List.take j o)).1.length ≤ j
  simp at this; omega

theorem length_assocSet_le' {β : Type} (l : List (Nat × β)) (k : Nat) (v : β) :
    (assocSet l k v).length ≤ l.length + 1 := by
  unfold assocSet; split <;> simp

theorem preSides_succ (o : List Nat) (b j : Nat) (hj : j < o.length) :
    preSides o b (j + 1) = sideStep b (preSides o b j) o[j] := by
  simp only [preSides]; rw [List.take_succ_eq_append_getElem hj, List.foldl_append]; rfl

theorem sideLoop_ok {κ : Caps} {s : Core} {L : Loc} {v b : Nat} (hv : L "v" = v) (hb : L "b" = b)
    (hn : L "n" = (s.nodes.getX v).table.length) (hsd : L "sd" = 0) (hvs : v < s.nodes.size)
    (hvr : v < κ.lrec .side) (hvt : v < κ.lrec .table) (hcap : (s.nodes.getX v).table.length + 1 ≤ κ.lcap .side) :
    ∃ L' c, evalF κ (.loop "j" "n" sideBody) (LK.put s v [] .side) L =
      .ok (LK.put s v (encS (sidesOf ((s.nodes.getX v).table.map (·.1)) b)) .side) L' c ∧
      c ≤ 3 + (s.nodes.getX v).table.length * (80 + 25 * (s.nodes.getX v).table.length) ∧
      ∀ r, r ≠ "j" → r ≠ "e" → r ≠ "sd" → L' r = L r := by
  set o := (s.nodes.getX v).table.map (·.1)
  set n := (s.nodes.getX v).table.length
  have hon : o.length = n := by simp [o, n]
  have hval : ∀ (l : List (Nat × Side)), LK.side.valid (encS l) = true := by
    intro l; simp [LK.valid, encS, sideN_le]
  have hview : ∀ (l : List (Nat × Side)), LK.view (LK.put s v (encS l) .side) v .table = (s.nodes.getX v).table := by
    intro l; rw [LK.view_put (by simp [LK.recOk, hvs]) (hval l)]; simp [LK.view]
  have hviewS : ∀ (l : List (Nat × Side)), LK.view (LK.put s v (encS l) .side) v .side = encS l := by
    intro l; rw [LK.view_put (by simp [LK.recOk, hvs]) (hval l)]; simp
  let I : Nat → Core → Loc → Prop := fun j s' L' => s' = LK.put s v (encS (preSides o b j).1) .side ∧
    L' "sd" = sideN (preSides o b j).2 ∧ ∀ r, r ≠ "j" → r ≠ "e" → r ≠ "sd" → L' r = L r
  obtain ⟨s', L', c, he, hc, hs', -, hF⟩ := evalF_loop (x := "j") (n := .var "n") (b := sideBody)
    (s := LK.put s v [] .side) (L := L) (N := n) (by simp [Exp.ev, hn, n]) I (79 + 25 * n)
    ⟨rfl, by rw [hsd]; rfl, fun r _ _ _ => rfl⟩
    (by
      intro j hj s1 L1 ⟨hs1, hsd1, hF1⟩
      subst hs1
      set acc := preSides o b j
      have hjo : j < o.length := by omega
      set L2 := upd L1 "j" j
      have hv2 : L2 "v" = v := by
        simp only [L2, OM.Machine.State.upd]; simp; rw [hF1 "v" (by decide) (by decide) (by decide), hv]
      have hb2 : L2 "b" = b := by
        simp only [L2, OM.Machine.State.upd]; simp; rw [hF1 "b" (by decide) (by decide) (by decide), hb]
      have e1 := evalF_assign_ok (κ := κ) (s := LK.put s v (encS acc.1) .side) (L := L2) (x := "e")
        (e := .lrd .table false "v" "j") (v := o[j]) (by
          simp [Exp.ev, hv2, L2, OM.Machine.State.upd, hvt, hview, show j < (s.nodes.getX v).table.length by omega, o])
      set L3 := upd L2 "e" o[j]
      set st' : Side := if o[j] == b then .right else acc.2
      have e2 : ∃ c2, evalF κ (.ite ("e" =ₑ "b") ("sd" ::= 1) .skip) (LK.put s v (encS acc.1) .side) L3 =
          .ok (LK.put s v (encS acc.1) .side) (upd L3 "sd" (sideN st')) c2 ∧ c2 ≤ 6 := by
        by_cases hm : o[j] = b
        · have hst : sideN st' = 1 := by simp [st', hm, sideN]
          rw [hst]
          exact ⟨_, evalF_ite_t (v := 1) (by simp [Exp.ev, OM.Machine.BinOp.eval, L3, OM.Machine.State.upd, hb2, hm])
            one_ne_zero (evalF_assign_ok (v := 1) rfl), by simp [Exp.cost]⟩
        · have hst : upd L3 "sd" (sideN st') = L3 := by
            funext r; simp only [OM.Machine.State.upd]; split
            · next h => subst h; simp [L3, L2, OM.Machine.State.upd, hsd1, st', hm]
            · rfl
          rw [hst]
          exact ⟨_, evalF_ite_f (by simp [Exp.ev, OM.Machine.BinOp.eval, L3, OM.Machine.State.upd, hb2, hm])
            evalF_skip, by simp [Exp.cost]⟩
      obtain ⟨c2, e2, hc2⟩ := e2
      set L4 := upd L3 "sd" (sideN st')
      have hL4 : ∀ r, r ≠ "j" → r ≠ "e" → r ≠ "sd" → L4 r = L1 r := fun r h1 h2 h3 => by
        simp [L4, L3, L2, OM.Machine.State.upd, h1, h2, h3]
      obtain ⟨L5, c5, e5, hc5⟩ := assocSetP_agree κ .side (LK.put s v (encS acc.1) .side)
        (OM.Machine.State.setLocs (fun _ => 0) ["i", "x", "y"] [v, o[j], sideN st']) (i := v) (x := o[j])
        (y := sideN st') (by simp [OM.Machine.State.setLocs, OM.Machine.State.upd])
        (by simp [OM.Machine.State.setLocs, OM.Machine.State.upd])
        (by simp [OM.Machine.State.setLocs, OM.Machine.State.upd])
        (by simp [LK.idOk, LK.recOk, hvs]) (by simp [LK.recOk, hvs]) hvr
        (fun a => by simp [LK.valid, sideN_le]) (by
          rw [hviewS]
          have h1 := length_assocSet_le' (encS acc.1) o[j] (sideN st')
          have h2 : acc.1.length ≤ j := length_preSides o b j
          simp only [encS, List.length_map] at h1 ⊢; omega)
      have ec := evalF_call_ok (q := assocSetP .side) (args := [.var "v", .var "e", .var "sd"]) (ds := [])
        (L := L4) (by simp [evList, Exp.ev, L4, L3, OM.Machine.State.upd, hv2]) e5
      rw [hviewS, assocSet_encS, LK.put_put] at ec
      refine ⟨_, _, _, evalF_seq_ok2 e1 (evalF_seq_ok2 e2 ec), ?_, ?_, ?_, ?_⟩
      · have h2 : acc.1.length ≤ j := length_preSides o b j
        rw [hviewS] at hc5; simp only [encS, List.length_map] at hc5
        simp only [Exp.cost, costList, List.map, List.sum_cons, List.sum_nil, List.length_nil] at hc2 hc5 ⊢
        omega
      · rw [preSides_succ o b j hjo]; rfl
      · rw [preSides_succ o b j hjo]; simp [OM.Machine.State.setLocs, L4, OM.Machine.State.upd, sideStep, st']; rfl
      · intro r h1 h2 h3; simp only [OM.Machine.State.setLocs]; exact (hL4 r h1 h2 h3).trans (hF1 r h1 h2 h3))
  have hfin : (preSides o b n).1 = sidesOf o b := by
    simp only [preSides, sidesOf_eq]; rw [← hon, List.take_length]
  rw [hs', hfin] at he
  refine ⟨L', c, he, ?_, hF⟩
  have e : n * (1 + (79 + 25 * n)) = n * (80 + 25 * n) := by ring
  simp only [Exp.cost] at hc; rw [e] at hc; omega

end OM.Impl
