import Erdos335.AnnularBlockModels

/-!
# Mean-square errors of polynomial models on finite prefixes
-/

set_option autoImplicit false

open Finset
open scoped BigOperators

namespace Erdos335.IntermediateScale

theorem prefix_polynomial_triangle (f g : ℕ → ℝ) (p : ℕ → ℂ) (N : ℕ) :
    (∑ n ∈ range N, ‖(f n : ℂ) - p n‖ ^ 2) / N ≤
      2 * prefixEnergy (fun n => f n - g n) N +
        2 * ((∑ n ∈ range N, ‖(g n : ℂ) - p n‖ ^ 2) / N) := by
  have hp (n : ℕ) : ‖(f n : ℂ) - p n‖ ^ 2 ≤
      2 * (f n - g n) ^ 2 + 2 * ‖(g n : ℂ) - p n‖ ^ 2 := by
    have ht : ‖(f n : ℂ) - p n‖ ≤ ‖(f n : ℂ) - g n‖ + ‖(g n : ℂ) - p n‖ := by
      simpa only [dist_eq_norm] using dist_triangle (f n : ℂ) (g n : ℂ) (p n)
    rw [← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs] at ht
    have hsq : |f n - g n| ^ 2 = (f n - g n) ^ 2 := sq_abs _
    nlinarith [sq_nonneg (|f n - g n| - ‖(g n : ℂ) - p n‖),
      norm_nonneg ((f n : ℂ) - p n), norm_nonneg ((g n : ℂ) - p n), abs_nonneg (f n - g n)]
  have hs := div_le_div_of_nonneg_right (sum_le_sum fun n (_hn : n ∈ range N) => hp n)
    (Nat.cast_nonneg N : (0 : ℝ) ≤ N)
  simpa only [prefixEnergy, sum_add_distrib, ← mul_sum, add_div, mul_div_assoc] using hs

end Erdos335.IntermediateScale
