import Erdos335.IntegerKneser
import Erdos335.Bohr
import Erdos335.Singleton
import Erdos335.MaskDensity

/-!
# The sufficient direction of the proposed characterization

Every listed alternative implies the required density equality. The converse
remains a separate proof obligation.
-/

set_option autoImplicit false

open Filter Topology
open scoped Pointwise

namespace Erdos335.Proposed

theorem Classified.hasDensity {A B : Set ℕ} {a b : ℝ}
    (h : Classified A B (a + b)) (hApos : A ⊆ Set.Ioi 0) (hBpos : B ⊆ Set.Ioi 0)
    (hA : HasDensity A a) (hB : HasDensity B b) : HasDensity (A + B) (a + b) := by
  rcases h with hgamma | ⟨hgap, hbohr | hsingleton | hmask⟩
  · exact hasDensity_sum_of_gamma_eq hApos hBpos hA hB hgamma
  · exact hbohr.hasDensity hApos hBpos hA hB
  · exact hsingleton.hasDensity hApos hBpos hA hB
  · exact maskBranch_hasDensity A B (a + b) hmask

theorem isErdos335Pair_of_classified (A B : Set ℕ) (a b : ℝ)
    (hApos : A ⊆ Set.Ioi 0) (hBpos : B ⊆ Set.Ioi 0)
    (ha0 : 0 < a) (hb0 : 0 < b) (hA : HasDensity A a) (hB : HasDensity B b)
    (h : Classified A B (a + b)) : IsErdos335Pair A B :=
  ⟨hApos, hBpos, a, b, ha0, hb0, hA, hB, h.hasDensity hApos hBpos hA hB⟩

end Erdos335.Proposed
