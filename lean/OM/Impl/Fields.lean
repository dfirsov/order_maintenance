import OM.Impl.Compile
import OM.Proof.Top.PrepRun

/-!
# M6: reading back what was written

A write to field `f` of record `i` changes exactly that value (`Fld.get_set`), keeps every
table size and the parameters, and a `push` changes no value at all (a pushed record is a
default record, which reads like a record past the end).
-/

namespace OM.Impl

open OM.Model
open OM.Proof.Top (getX_modify' getX_setX' getX_push')

theorem b2n_not_beq {v : Nat} (h : v ≤ 1) : b2n (!(v == 0)) = v := by
  rcases v with _ | _ | v <;> simp [b2n] at *
theorem b2n_bne {v : Nat} (h : v ≤ 1) : b2n (v != 0) = v := by
  rcases v with _ | _ | v <;> simp [b2n] at * <;> omega

theorem EF.get_set (x : Elem) (v : Nat) (k k' : EF) (h : k.ok v = true) :
    EF.get (EF.set x v k) k' = if k' = k then v else EF.get x k' := by
  cases k <;> cases k' <;> simp_all [EF.get, EF.set, EF.ok, b2n_not_beq]

theorem GF.get_set (x : Group) (v : Nat) (k k' : GF) (h : k.ok v = true) :
    GF.get (GF.set x v k) k' = if k' = k then v else GF.get x k' := by
  cases k <;> cases k' <;> simp_all [GF.get, GF.set, GF.ok, b2n_not_beq, St.toN_ofN]

theorem CF.get_set (x : Chunk) (v : Nat) (k k' : CF) (h : k.ok v = true) :
    CF.get (CF.set x v k) k' = if k' = k then v else CF.get x k' := by
  cases k <;> cases k' <;> simp_all [CF.get, CF.set, CF.ok, b2n_not_beq, St.toN_ofN]

theorem NF.get_set (x : Node) (v : Nat) (k k' : NF) (h : k.ok v = true) :
    NF.get (NF.set x v k) k' = if k' = k then v else NF.get x k' := by
  cases k <;> cases k' <;> simp_all [NF.get, NF.set, NF.ok, b2n_not_beq, b2n_bne]

theorem AF.get_set (s : Core) (a : Array Nat) (k k' : AF) :
    k'.get (k.set s a) = if k' = k then a else k'.get s := by
  cases k <;> cases k' <;> rfl

theorem SF.get_set (s : Core) (v : Nat) (k k' : SF) (h : k.ok v = true) :
    k'.get (k.set s v) = if k' = k then v else k'.get s := by
  cases k <;> cases k' <;> simp_all [SF.get, SF.set, SF.ok, b2n_not_beq]

/-- What an `AF` write keeps. -/
theorem AF.set_keep (s : Core) (a : Array Nat) (k : AF) :
    (k.set s a).E = s.E ∧ (k.set s a).Gs = s.Gs ∧ (k.set s a).C = s.C ∧ (k.set s a).nodes = s.nodes ∧
      (k.set s a).P = s.P ∧ ∀ k' : SF, k'.get (k.set s a) = k'.get s := by
  cases k <;> exact ⟨rfl, rfl, rfl, rfl, rfl, fun k' => by cases k' <;> rfl⟩

/-- What a scalar write keeps. -/
theorem SF.set_keep (s : Core) (v : Nat) (k : SF) :
    (k.set s v).E = s.E ∧ (k.set s v).Gs = s.Gs ∧ (k.set s v).C = s.C ∧ (k.set s v).nodes = s.nodes ∧
      (k.set s v).P = s.P ∧ ∀ k' : AF, k'.get (k.set s v) = k'.get s := by
  cases k <;> exact ⟨rfl, rfl, rfl, rfl, rfl, fun k' => by cases k' <;> rfl⟩

theorem Fld.cap_scalar {κ : Caps} {k : SF} {j : Nat} (h : j < (Fld.s k).cap κ) : j = 0 := by
  simp [Fld.cap] at h; exact h

/-- **A write changes exactly the written value.** -/
theorem Fld.get_set {κ : Caps} {s s' : Core} {i v : Nat} {f : Fld} (h : f.set κ s i v = some s')
    (g : Fld) {j : Nat} (hj : j < g.cap κ) :
    g.get s' j = if g = f ∧ j = i then v else g.get s j := by
  cases f with
  | e k =>
    simp only [Fld.set] at h; split at h <;> [skip; simp at h]
    next hc =>
    cases h
    cases g with
    | e k' =>
      simp only [Fld.get, getX_modify']
      by_cases e1 : j = i
      · subst e1; rw [if_pos ⟨rfl, hc.1⟩, EF.get_set _ _ _ _ hc.2]; by_cases e2 : k' = k <;> simp [e2]
      · rw [if_neg (fun h => e1 h.1)]; simp [e1]
    | _ k' => cases k' <;> simp [Fld.get, AF.get, SF.get]
  | g k =>
    simp only [Fld.set] at h; split at h <;> [skip; simp at h]
    next hc =>
    cases h
    cases g with
    | g k' =>
      simp only [Fld.get, getX_modify']
      by_cases e1 : j = i
      · subst e1; rw [if_pos ⟨rfl, hc.1⟩, GF.get_set _ _ _ _ hc.2]; by_cases e2 : k' = k <;> simp [e2]
      · rw [if_neg (fun h => e1 h.1)]; simp [e1]
    | _ k' => cases k' <;> simp [Fld.get, AF.get, SF.get]
  | c k =>
    simp only [Fld.set] at h; split at h <;> [skip; simp at h]
    next hc =>
    cases h
    cases g with
    | c k' =>
      simp only [Fld.get, getX_modify']
      by_cases e1 : j = i
      · subst e1; rw [if_pos ⟨rfl, hc.1⟩, CF.get_set _ _ _ _ hc.2]; by_cases e2 : k' = k <;> simp [e2]
      · rw [if_neg (fun h => e1 h.1)]; simp [e1]
    | _ k' => cases k' <;> simp [Fld.get, AF.get, SF.get]
  | n k =>
    simp only [Fld.set] at h; split at h <;> [skip; simp at h]
    next hc =>
    cases h
    cases g with
    | n k' =>
      simp only [Fld.get, getX_modify']
      by_cases e1 : j = i
      · subst e1; rw [if_pos ⟨rfl, hc.1⟩, NF.get_set _ _ _ _ hc.2]; by_cases e2 : k' = k <;> simp [e2]
      · rw [if_neg (fun h => e1 h.1)]; simp [e1]
    | _ k' => cases k' <;> simp [Fld.get, AF.get, SF.get]
  | a k =>
    simp only [Fld.set] at h; split at h <;> [skip; simp at h]
    cases h
    obtain ⟨hE, hG, hC, hN, -, hS⟩ := AF.set_keep s ((k.get s).setX i v) k
    cases g with
    | a k' =>
      simp only [Fld.get, AF.get_set]
      by_cases e2 : k' = k
      · subst e2; rw [if_pos rfl, getX_setX']; by_cases e1 : j = i <;> simp [e1]
      · simp [e2]
    | e k' => simp only [Fld.get, hE]; simp
    | g k' => simp only [Fld.get, hG]; simp
    | c k' => simp only [Fld.get, hC]; simp
    | n k' => simp only [Fld.get, hN]; simp
    | s k' => simp only [Fld.get, hS]; simp
  | s k =>
    simp only [Fld.set] at h; split at h <;> [skip; simp at h]
    next hc =>
    cases h
    obtain ⟨hE, hG, hC, hN, -, hS⟩ := SF.set_keep s v k
    cases g with
    | s k' =>
      have hj0 := Fld.cap_scalar hj
      have hi0 : i = 0 := by omega
      subst hj0; subst hi0
      simp only [Fld.get, SF.get_set _ _ _ _ hc.2]
      by_cases e2 : k' = k <;> simp [e2]
    | e k' => simp only [Fld.get, hE]; simp
    | g k' => simp only [Fld.get, hG]; simp
    | c k' => simp only [Fld.get, hC]; simp
    | n k' => simp only [Fld.get]; rw [hN]; simp
    | a k' =>
      cases k <;> cases k' <;> simp [Fld.get, SF.set, AF.get]

/-- A write keeps the table sizes and the parameters. -/
theorem Fld.set_keep {κ : Caps} {s s' : Core} {i v : Nat} {f : Fld} (h : f.set κ s i v = some s') :
    (∀ t : Tbl, t.size s' = t.size s) ∧ s'.P = s.P := by
  cases f with
  | e k | g k | c k | n k =>
    simp only [Fld.set] at h; split at h <;> [skip; simp at h]
    cases h; exact ⟨fun t => by cases t <;> simp [Tbl.size], rfl⟩
  | a k =>
    simp only [Fld.set] at h; split at h <;> [skip; simp at h]
    cases h
    obtain ⟨hE, hG, hC, hN, hP, -⟩ := AF.set_keep s ((k.get s).setX i v) k
    exact ⟨fun t => by cases t <;> simp [Tbl.size, hE, hG, hC, hN], hP⟩
  | s k =>
    simp only [Fld.set] at h; split at h <;> [skip; simp at h]
    cases h
    obtain ⟨hE, hG, hC, hN, hP, -⟩ := SF.set_keep s v k
    exact ⟨fun t => by cases t <;> simp [Tbl.size, hE, hG, hC, hN], hP⟩

theorem getX_push_default {α : Type} [Inhabited α] (a : Array α) (i : Nat) :
    (a.push default).getX i = a.getX i := by
  rw [getX_push']
  split
  · next h => subst h; unfold Array.getX; simp [Array.getD]
  · rfl

/-- **A push changes no value**, and adds one to its table's size. -/
theorem Tbl.push_get (s : Core) (t : Tbl) (f : Fld) (i : Nat) : f.get (t.push s) i = f.get s i := by
  cases t <;> cases f <;> (rename_i k; cases k) <;>
    simp only [Tbl.push, Fld.get, AF.get, SF.get, getX_push_default]

theorem Tbl.push_size (s : Core) (t t' : Tbl) :
    t'.size (t.push s) = if t' = t then t.size s + 1 else t'.size s := by
  cases t <;> cases t' <;> simp [Tbl.push, Tbl.size]

theorem Tbl.push_P (s : Core) (t : Tbl) : (t.push s).P = s.P := by cases t <;> rfl

end OM.Impl
