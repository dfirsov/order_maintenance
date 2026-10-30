/-
The axiom audit of the paper's main theorems: `scripts/reproduce.sh` runs
`lake env lean Audit.lean` and checks that each theorem depends only on `propext`,
`Classical.choice` and `Quot.sound`. This file is not part of the `OM` library.
-/
import OM
open OM OM.Impl OM.Machine OM.Proof.Word

#print axioms theoremABW_MW   -- Theorems A, B and W (Fig. 7)
#print axioms theoremAB_M     -- Theorems A and B with `runM`
#print axioms theoremAB_word  -- Theorems A and B on w-bit words
#print axioms execW_agree     -- the w-bit machine agrees with `exec`
#print axioms theoremW_stored -- stored values (Level F)
#print axioms sim             -- the compiler simulation
#print axioms insertW_ok      -- the insertion returns the specification's handle
#print axioms core_mem        -- core array capacity
#print axioms opB_four
#print axioms initB_eq
#print axioms flatten_sim          -- the translation to a RAM without `alloc`: simulation
#print axioms theoremAB_flat       -- Theorems A and B on a RAM without `alloc`
#print axioms theoremAB_flat_word  -- the same on w-bit words
