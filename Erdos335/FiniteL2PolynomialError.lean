import Erdos335.SoftCharacterPolynomials

/-!
# Combining mean-square and uniform approximation errors
-/

set_option autoImplicit false

open Finset
open scoped BigOperators

namespace Erdos335.IntermediateScale

theorem finite_l2_uniform_triangle {X : Type*} [Fintype X] [Nonempty X]
    (f s : X → ℝ) (p : X → ℂ) (α β : ℝ) (hβ : 0 ≤ β)
    (hs : (∑ x : X, (s x - f x) ^ 2) / Fintype.card X ≤ α ^ 2)
    (hp : ∀ x, ‖(s x : ℂ) - p x‖ ≤ β) :
    (∑ x : X, ‖(f x : ℂ) - p x‖ ^ 2) / Fintype.card X ≤
      2 * α ^ 2 + 2 * β ^ 2 := by
  have hcard : (0 : ℝ) < Fintype.card X := by exact_mod_cast Fintype.card_pos
  have hpoint (x : X) : ‖(f x : ℂ) - p x‖ ^ 2 ≤
      2 * (s x - f x) ^ 2 + 2 * β ^ 2 := by
    have htriangle : ‖(f x : ℂ) - p x‖ ≤ ‖(f x : ℂ) - s x‖ + ‖(s x : ℂ) - p x‖ := by
      simpa only [dist_eq_norm] using dist_triangle (f x : ℂ) (s x : ℂ) (p x)
    have hn := htriangle.trans
      (add_le_add le_rfl (hp x))
    rw [← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs] at hn
    have habs : |f x - s x| ^ 2 = (s x - f x) ^ 2 := by rw [sq_abs]; ring
    nlinarith [sq_nonneg (|f x - s x| - β), norm_nonneg ((f x : ℂ) - p x),
      abs_nonneg (f x - s x)]
  have hsum := sum_le_sum (fun x (_ : x ∈ (univ : Finset X)) => hpoint x)
  simp only [sum_add_distrib, ← mul_sum, sum_const, card_univ, nsmul_eq_mul] at hsum
  have hbase := (div_le_iff₀ hcard).mp hs
  apply (div_le_iff₀ hcard).mpr
  nlinarith

end Erdos335.IntermediateScale
