import Erdos335.FiniteFourierConvolution
import Erdos335.FinitePolynomialCorrelation

/-!
# Convolution energy controlled by the largest Fourier coefficient
-/

set_option autoImplicit false

open Finset
open scoped BigOperators

namespace Erdos335.FiniteFourier

theorem convolution_energy_le_of_coefficients
    {G : Type*} [AddCommGroup G] [Fintype G]
    (f g : G → ℂ) (ε : ℝ) (h : ∀ χ : AddChar G ℂ, ‖coefficient f χ‖ ≤ ε) :
    (Fintype.card G : ℝ)⁻¹ * ∑ x : G, ‖convolution f g x‖ ^ 2 ≤
      ε ^ 2 * ((Fintype.card G : ℝ)⁻¹ * ∑ x : G, ‖g x‖ ^ 2) := by
  classical
  rw [← parseval (convolution f g), ← parseval g, Finset.mul_sum]
  apply Finset.sum_le_sum
  intro χ hχ
  rw [coefficient_convolution, norm_mul, mul_pow]
  exact mul_le_mul_of_nonneg_right
    (pow_le_pow_left₀ (norm_nonneg _) (h χ) 2) (sq_nonneg _)

theorem convolution_l1_le_of_coefficients
    {G : Type*} [AddCommGroup G] [Fintype G]
    (f g : G → ℂ) (ε : ℝ) (hε : 0 ≤ ε)
    (hf : ∀ χ : AddChar G ℂ, ‖coefficient f χ‖ ≤ ε)
    (hg : ∀ x, ‖g x‖ ≤ 1) :
    (∑ x : G, ‖convolution f g x‖) / Fintype.card G ≤ ε := by
  have hcard : (0 : ℝ) < Fintype.card G := by exact_mod_cast Fintype.card_pos
  have hgSum : (∑ x : G, ‖g x‖ ^ 2) ≤ (Fintype.card G : ℝ) := by
    calc
      _ ≤ ∑ _x : G, (1 : ℝ) := by
        apply sum_le_sum
        intro x hx
        nlinarith [hg x, norm_nonneg (g x)]
      _ = _ := by simp
  have hgEnergy : (Fintype.card G : ℝ)⁻¹ * (∑ x : G, ‖g x‖ ^ 2) ≤ 1 := by
    apply (inv_mul_le_iff₀ hcard).mpr
    simpa only [mul_one] using hgSum
  have hEnergy := (convolution_energy_le_of_coefficients f g ε hf).trans
    (mul_le_mul_of_nonneg_left hgEnergy (sq_nonneg ε))
  have hEnergy' : (∑ x : G, ‖convolution f g x‖ ^ 2) / Fintype.card G ≤ ε ^ 2 := by
    simpa only [div_eq_mul_inv, mul_comm, mul_one] using hEnergy
  exact (div_le_iff₀ hcard).mpr
    (Erdos335.IntermediateScale.finite_l1_of_mean_square (convolution f g) ε hε hEnergy')

end Erdos335.FiniteFourier
