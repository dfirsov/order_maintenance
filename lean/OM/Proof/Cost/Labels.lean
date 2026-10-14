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
