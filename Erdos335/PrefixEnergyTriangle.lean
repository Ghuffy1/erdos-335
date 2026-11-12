import Erdos335.PrefixEnergyAlgebra

/-!
# A mean-square triangle estimate on finite prefixes
-/

set_option autoImplicit false

open Finset
open scoped BigOperators

namespace Erdos335.IntermediateScale

theorem prefixEnergy_triangle (f g h : ℕ → ℝ) (N : ℕ) :
    prefixEnergy (fun n => f n - h n) N ≤
      2 * prefixEnergy (fun n => f n - g n) N + 2 * prefixEnergy (fun n => g n - h n) N := by
  have hp (n : ℕ) : (f n - h n) ^ 2 ≤ 2 * (f n - g n) ^ 2 + 2 * (g n - h n) ^ 2 := by
    nlinarith [sq_nonneg (f n - 2 * g n + h n)]
  have hs := sum_le_sum fun n (_hn : n ∈ range N) => hp n
  have hd := div_le_div_of_nonneg_right hs (Nat.cast_nonneg N : (0 : ℝ) ≤ N)
  simpa only [prefixEnergy, sum_add_distrib, ← mul_sum, add_div, mul_div_assoc] using hd

end Erdos335.IntermediateScale
