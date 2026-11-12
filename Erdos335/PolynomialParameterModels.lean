import Erdos335.AnnularBlockParameters
import Erdos335.AnnularParameterWindows

/-!
# Variable-frequency polynomial models and parameter variation
-/

set_option autoImplicit false

open Filter Topology Finset
open scoped BigOperators Classical

namespace Erdos335.IntermediateScale

noncomputable def variableFrequencyPolynomial {d : ℕ}
    (c : ℕ → Fin d → ℂ) (α : ℕ → Fin d → ℝ) (n : ℕ) : ℂ :=
  ∑ j, c n j * unitCharacter ((n : ℝ) * α n j)

noncomputable def varyingPolynomialParameters {d : ℕ} (N W : ℕ)
    (c : ℕ → Fin d → ℂ) (α : ℕ → Fin d → ℝ) : Finset ℕ :=
  (range N).filter fun n => ∃ i ≤ W, ∃ j : Fin d,
    c (n + i) j ≠ c n j ∨ α (n + i) j ≠ α n j

theorem variableFrequencyPolynomial_stitched
    {F : ℕ → ℝ} {H : ℕ → ℕ} {L : ℕ} {ε : ℝ}
    (N : ℕ → ℕ) (hN : Tendsto N atTop atTop)
    (m : ∀ s, BlockRegularModel F (H s) L ε) :
    variableFrequencyPolynomial (stitchedBlockCoefficient N hN m) (stitchedBlockFrequency N hN m) =
      stitchedBlockPolynomial N hN m := rfl

theorem varyingPolynomialParameters_stitched
    {F : ℕ → ℝ} {H : ℕ → ℕ} {L : ℕ} {ε : ℝ}
    (N : ℕ → ℕ) (hN : Tendsto N atTop atTop)
    (m : ∀ s, BlockRegularModel F (H s) L ε) (s W : ℕ) :
    varyingPolynomialParameters (N s) W (stitchedBlockCoefficient N hN m) (stitchedBlockFrequency N hN m) =
      varyingParameterWindows N hN m s W := rfl

end Erdos335.IntermediateScale
