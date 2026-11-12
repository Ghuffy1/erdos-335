import Erdos335.BlockFourierTransfer

/-!
# The Fourier norm on a moving finite interval
-/

set_option autoImplicit false

open Finset
open scoped BigOperators

namespace Erdos335.IntermediateScale

noncomputable def windowFourierNorm (r : ℕ → ℝ) (n W : ℕ) : ℝ :=
  ⨆ β : ℝ, ‖(∑ i ∈ range W, (r (n + i) : ℂ) * unitCharacter ((i : ℝ) * β)) / (W : ℂ)‖

theorem window_fourier_coefficient_le_abs_average (r : ℕ → ℝ) (n W : ℕ) (β : ℝ) :
    ‖(∑ i ∈ range W, (r (n + i) : ℂ) * unitCharacter ((i : ℝ) * β)) / (W : ℂ)‖ ≤
      (∑ i ∈ range W, |r (n + i)|) / W := by
  rw [norm_div, Complex.norm_natCast]
  apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg W)
  simpa only [norm_mul, unitCharacter_norm, mul_one, Complex.norm_real, Real.norm_eq_abs]
    using norm_sum_le (range W) (fun i => (r (n + i) : ℂ) * unitCharacter ((i : ℝ) * β))

theorem window_fourier_coefficients_bddAbove (r : ℕ → ℝ) (n W : ℕ) :
    BddAbove (Set.range (fun β : ℝ =>
      ‖(∑ i ∈ range W, (r (n + i) : ℂ) * unitCharacter ((i : ℝ) * β)) / (W : ℂ)‖)) := by
  refine ⟨(∑ i ∈ range W, |r (n + i)|) / W, ?_⟩
  rintro _ ⟨β, rfl⟩
  exact window_fourier_coefficient_le_abs_average r n W β

theorem windowFourierNorm_nonneg (r : ℕ → ℝ) (n W : ℕ) : 0 ≤ windowFourierNorm r n W :=
  le_ciSup_of_le (window_fourier_coefficients_bddAbove r n W) (0 : ℝ) (norm_nonneg _)

theorem windowFourierNorm_le_of_coefficients (r : ℕ → ℝ) (n W : ℕ) (A : ℝ)
    (hbound : ∀ β : ℝ,
      ‖(∑ i ∈ range W, (r (n + i) : ℂ) * unitCharacter ((i : ℝ) * β)) / (W : ℂ)‖ ≤ A) :
    windowFourierNorm r n W ≤ A := ciSup_le hbound

theorem windowFourierNorm_le_one (r : ℕ → ℝ) (hr : ∀ n, |r n| ≤ 1)
    (n W : ℕ) (hW : 0 < W) : windowFourierNorm r n W ≤ 1 := by
  apply windowFourierNorm_le_of_coefficients
  intro β
  have hWr : (0 : ℝ) < W := by exact_mod_cast hW
  calc
    _ ≤ (∑ i ∈ range W, |r (n + i)|) / W := window_fourier_coefficient_le_abs_average r n W β
    _ ≤ (∑ _i ∈ range W, (1 : ℝ)) / W :=
      div_le_div_of_nonneg_right (sum_le_sum fun i hi => hr _) hWr.le
    _ = 1 := by simp [hWr.ne']

theorem windowFourierNorm_of_blocks (r : ℕ → ℝ) (hr : ∀ n, |r n| ≤ 1)
    (H n W : ℕ) (hH : 0 < H) (hW : 0 < W)
    (ε : ℝ) (hε0 : 0 ≤ ε) (hε1 : ε ≤ 1)
    (hblock : ∀ b β, ‖∑ i ∈ range H, (r (H * b + i) : ℂ) *
      unitCharacter (((H * b + i : ℕ) : ℝ) * β)‖ ≤ ε * H) :
    windowFourierNorm r n W ≤ ε + 3 * (H : ℝ) / W := by
  apply windowFourierNorm_le_of_coefficients
  exact fun β => window_fourier_bound_of_blocks r hr H n W hH hW ε hε0 hε1 hblock β

end Erdos335.IntermediateScale
