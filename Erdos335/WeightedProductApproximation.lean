import Erdos335.FiniteProductApproximation

/-!
# Uniform approximation of finite weighted product models
-/

set_option autoImplicit false

open Finset
open scoped BigOperators Classical

namespace Erdos335.IntermediateScale

theorem weighted_product_approximation {I R : Type*} [Fintype I] [Fintype R]
    (F P : R → I → ℂ) (c : R → ℂ) (ε : ℝ) (hε : 0 ≤ ε) (hε1 : ε ≤ 1)
    (hF : ∀ r i, ‖F r i‖ ≤ 1) (hc : ∀ r, ‖c r‖ ≤ 1)
    (happrox : ∀ r i, ‖F r i - P r i‖ ≤ ε) :
    ‖(∑ r : R, c r * ∏ i : I, F r i) - ∑ r : R, c r * ∏ i : I, P r i‖ ≤
      Fintype.card R * (Fintype.card I * ε * 2 ^ Fintype.card I) := by
  have hP (r : R) (i : I) : ‖P r i‖ ≤ 2 := by
    calc
      ‖P r i‖ = ‖F r i - (F r i - P r i)‖ := by congr 1; ring
      _ ≤ ‖F r i‖ + ‖F r i - P r i‖ := norm_sub_le _ _
      _ ≤ 2 := by linarith [hF r i, happrox r i]
  have hproduct (r : R) : ‖(∏ i : I, F r i) - ∏ i : I, P r i‖ ≤
      Fintype.card I * ε * 2 ^ Fintype.card I := by
    simpa only [card_univ] using norm_prod_approximation univ (F r) (P r) ε hε
      (fun i _ => hF r i) (fun i _ => hP r i) (fun i _ => happrox r i)
  have heq : (∑ r : R, c r * ∏ i : I, F r i) - ∑ r : R, c r * ∏ i : I, P r i =
      ∑ r : R, c r * ((∏ i : I, F r i) - ∏ i : I, P r i) := by
    rw [← sum_sub_distrib]
    apply sum_congr rfl
    intro r hr
    ring
  rw [heq]
  calc
    _ ≤ ∑ r : R, ‖c r * ((∏ i : I, F r i) - ∏ i : I, P r i)‖ := norm_sum_le _ _
    _ ≤ ∑ _r : R, Fintype.card I * ε * 2 ^ Fintype.card I := by
      apply sum_le_sum
      intro r hr
      rw [norm_mul]
      exact (mul_le_mul (hc r) (hproduct r) (norm_nonneg _) zero_le_one).trans_eq (one_mul _)
    _ = _ := by simp

end Erdos335.IntermediateScale
