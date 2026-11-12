import Erdos335.AnnularBlockModels
import Erdos335.BlockBoundaryDensity

/-!
# Locally constant coefficients of stitched block polynomials
-/

set_option autoImplicit false

open Filter Topology
open scoped BigOperators

namespace Erdos335.IntermediateScale

variable {F : ℕ → ℝ} {H : ℕ → ℕ} {L : ℕ} {ε : ℝ}

noncomputable def stitchedBlockCoefficient (N : ℕ → ℕ) (hN : Tendsto N atTop atTop)
    (m : ∀ s, BlockRegularModel F (H s) L ε) (n : ℕ) (j : Fin L) : ℂ :=
  (m (firstCutIndex N hN n)).coefficient (n / H (firstCutIndex N hN n)) j

noncomputable def stitchedBlockFrequency (N : ℕ → ℕ) (hN : Tendsto N atTop atTop)
    (m : ∀ s, BlockRegularModel F (H s) L ε) (n : ℕ) (j : Fin L) : ℝ :=
  (m (firstCutIndex N hN n)).frequency (n / H (firstCutIndex N hN n)) j

theorem stitchedBlockPolynomial_representation (N : ℕ → ℕ) (hN : Tendsto N atTop atTop)
    (m : ∀ s, BlockRegularModel F (H s) L ε) (n : ℕ) :
    stitchedBlockPolynomial N hN m n =
      ∑ j, stitchedBlockCoefficient N hN m n j * unitCharacter ((n : ℝ) * stitchedBlockFrequency N hN m n j) := rfl

theorem stitchedBlockCoefficient_bound (N : ℕ → ℕ) (hN : Tendsto N atTop atTop)
    (m : ∀ s, BlockRegularModel F (H s) L ε) (n : ℕ) (j : Fin L) :
    ‖stitchedBlockCoefficient N hN m n j‖ ≤ 1 := (m _).coefficient_bound _ j

theorem stitchedBlockParameters_constant_on_window
    (N : ℕ → ℕ) (hN : Tendsto N atTop atTop) (hmono : Monotone N)
    (m : ∀ s, BlockRegularModel F (H s) L ε) (s n W : ℕ)
    (hlow : N (s - 1) ≤ n) (hhigh : n + W < N s)
    (hblock : n / H s = (n + W) / H s) (i : ℕ) (hi : i ≤ W) (j : Fin L) :
    stitchedBlockCoefficient N hN m (n + i) j = stitchedBlockCoefficient N hN m n j ∧
      stitchedBlockFrequency N hN m (n + i) j = stitchedBlockFrequency N hN m n j := by
  have hbase := firstCutIndex_eq N hN hmono s n (by omega) hlow
  have hnext := firstCutIndex_eq N hN hmono s (n + i) (by omega) (by omega)
  have hquot := block_quotient_constant (H s) n W i hblock hi
  unfold stitchedBlockCoefficient stitchedBlockFrequency
  rw [hnext, hbase, hquot]
  exact ⟨rfl, rfl⟩

end Erdos335.IntermediateScale
