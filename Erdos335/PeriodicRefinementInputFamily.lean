import Erdos335.Density

/-!
# The two inputs and their sumset in the macroscopic construction
-/

set_option autoImplicit false

open scoped Pointwise

namespace Erdos335.PeriodicRefinement

def macroInput (A B : Set ℕ) (i : Fin 3) : Set ℕ :=
  if i = 0 then A else if i = 1 then B else A + B

end Erdos335.PeriodicRefinement
