import OM.Machine.Logic

/-!
# Examples

Small programs with proved results and exact costs, exercising every rule of the logic.
-/

namespace OM.Machine.Examples

open OM.Machine

/-- Straight-line code. -/
def incr : Stmt := "x" ::= "x" + 1

example (s : State) : wp incr (fun s' n => s'.loc "x" = s.loc "x" + 1 ∧ n = 4) s := by
  simp [incr, wp_assign]

/-- A branch: `m := max(a, b)`. -/
def max2 : Stmt := .ite ("a" <ₑ "b") ("m" ::= "b") ("m" ::= "a")

theorem max2_spec (s : State) :
    wp max2 (fun s' n => s'.loc "m" = max (s.loc "a") (s.loc "b") ∧ n = 6) s := by
  by_cases h : s.loc "a" < s.loc "b"
  · simp [max2, wp_ite, wp_assign, h]; omega
  · simp [max2, wp_ite, wp_assign, h]; omega

/-- A procedure with locals, and a call. -/
def maxProc : Proc := ⟨"max", ["a", "b"], ["m"], max2⟩

def callMax : Stmt := maxProc.invoke ["y", "x" + 1] ["z"]

example (s : State) :
    wp callMax (fun s' n => s'.loc "z" = max (s.loc "y") (s.loc "x" + 1) ∧
      s'.loc "x" = s.loc "x" ∧ n = 1 + 4 + 1 + 6) s := by
  simp only [callMax, Proc.invoke, maxProc, wp_call]
  refine ⟨_, rfl, ?_⟩
  refine wp_mono ?_ (max2_spec _)
  rintro s' n ⟨hm, rfl⟩
  simp [hm]

/-- A loop: `acc := A[0] + … + A[n-1]`, for the array `A` named 0. Cost `4 + 6n`. -/
def sumProg : Stmt :=
  "acc" ::= 0 ;;
  .loop "i" "n" ("acc" ::= "acc" + (0 : Arr)[["i"]])

def prefixSum (f : Nat → Nat) : Nat → Nat
  | 0 => 0
  | k + 1 => prefixSum f k + f k

theorem sumProg_spec (s : State) (h : s.loc "n" ≤ s.cap 0) :
    wp sumProg (fun s' c => s'.loc "acc" = prefixSum (s.mem 0) (s.loc "n") ∧
      c ≤ 4 + 6 * s.loc "n") s := by
  simp only [sumProg, wp_seq, wp_assign]
  refine ⟨0, rfl, ?_⟩
  refine wp_loop (s.loc "n")
    (fun k s' => s'.mem = s.mem ∧ s'.cap = s.cap ∧ s'.loc "acc" = prefixSum (s.mem 0) k)
    5 (by simp) (by simp [prefixSum]) ?_ ?_
  · rintro k hk s' ⟨hm, hc, hacc⟩
    have hk' : k < s.cap 0 := by omega
    simp [wp_assign, hk', hm, hc, hacc, prefixSum]
  · rintro s' c ⟨-, -, hacc⟩ hc
    simp at hc ⊢
    exact ⟨hacc, by omega⟩

/-- `catch`: a guard that fails is handled. -/
def guarded : Stmt := .catch (.ite ("x" =ₑ 0) .fail ("y" ::= 1)) ("y" ::= 2)

example (s : State) (h : s.loc "x" = 0) : wp guarded (fun s' _ => s'.loc "y" = 2) s := by
  refine wp_catch_fail (by simp [exec, h, Out.bind]) ?_
  simp [exec, h, Out.bind, wp_assign]

/-! ### Running the interpreter

`exec` is an ordinary Lean function, so programs can be run; this is how traces from the
Python prototype will be replayed (`docs/LEAN.md` §8). -/

/-- `A = [5, 7, 11]` (array 0), `n = 3`. -/
def s₀ : State :=
  { State.init with
    mem := fun a i => if a = 0 then [5, 7, 11].getD i 0 else 0
    cap := fun a => if a = 0 then 3 else 0
    loc := fun x => if x = "n" then 3 else 0 }

example : (exec sumProg s₀).st.loc "acc" = 23 := by decide
example : (exec sumProg s₀).cost = 4 + 6 * 3 := by decide
example : (exec sumProg s₀).st.peak = 23 := by decide

/-- Reading beyond the capacity is a machine error. -/
example : (exec sumProg { s₀ with loc := fun x => if x = "n" then 4 else 0 }).status = .err := by
  decide

end OM.Machine.Examples
