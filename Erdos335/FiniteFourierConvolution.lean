import Erdos335.FiniteFourier

/-!
# Finite convolution and spectral approximation

Normalized convolution multiplies Fourier coefficients. Truncating to the
large spectrum of the first input gives a uniform mean-square error bound.
-/

set_option autoImplicit false

open Finset RCLike
open scoped BigOperators ComplexConjugate

namespace Erdos335.FiniteFourier

variable {G : Type*} [AddCommGroup G] [Fintype G]

theorem coefficient_eq_expect (f : G → ℂ) (χ : AddChar G ℂ) :
    coefficient f χ = 𝔼 x, f x * conj (χ x) := by
  simpa only [coefficient, RCLike.inner_apply] using
    (RCLike.wInner_cWeight_eq_expect (𝕜 := ℂ) (χ : G → ℂ) f)

noncomputable def convolution (f g : G → ℂ) (x : G) : ℂ :=
  𝔼 y, f y * g (x - y)

theorem coefficient_convolution (f g : G → ℂ) (χ : AddChar G ℂ) :
    coefficient (convolution f g) χ = coefficient f χ * coefficient g χ := by
  classical
  rw [coefficient_eq_expect, coefficient_eq_expect, coefficient_eq_expect]
  conv_lhs => simp only [convolution, Finset.expect_mul]
  rw [Finset.expect_comm]
  rw [Fintype.expect_mul_expect]
  apply Finset.expect_congr rfl
  intro y _
  have hshift : (𝔼 x, f y * g (x - y) * conj (χ x)) =
      𝔼 z, f y * g z * conj (χ (z + y)) := by
    symm
    apply Fintype.expect_equiv (Equiv.addRight y)
    intro z
    change f y * g z * conj (χ (z + y)) = f y * g (z + y - y) * conj (χ (z + y))
    rw [add_sub_cancel_right]
  rw [hshift]
  apply Finset.expect_congr rfl
  intro z _
  rw [AddChar.map_add_eq_mul, map_mul]
  ring

theorem coefficient_ext {f g : G → ℂ}
    (h : ∀ χ : AddChar G ℂ, coefficient f χ = coefficient g χ) : f = g := by
  rw [← expansion f, ← expansion g]
  exact Finset.sum_congr rfl (fun χ _ => by rw [h χ])

theorem convolution_comm (f g : G → ℂ) : convolution f g = convolution g f := by
  apply coefficient_ext
  intro χ
  rw [coefficient_convolution, coefficient_convolution, mul_comm]

theorem convolution_truncation_energy_bound (f g : G → ℂ) (ε : ℝ) (hε : 0 < ε) :
    (Fintype.card G : ℝ)⁻¹ *
        ∑ x : G, ‖convolution f g x - truncation (convolution f g) (largeSpectrum f ε) x‖ ^ 2 ≤
      ε ^ 2 * ((Fintype.card G : ℝ)⁻¹ * ∑ x : G, ‖g x‖ ^ 2) := by
  classical
  change (Fintype.card G : ℝ)⁻¹ *
      ∑ x : G, ‖(convolution f g - truncation (convolution f g) (largeSpectrum f ε)) x‖ ^ 2 ≤ _
  rw [← parseval (convolution f g - truncation (convolution f g) (largeSpectrum f ε)),
    ← parseval g, Finset.mul_sum]
  apply Finset.sum_le_sum
  intro χ _
  rw [coefficient_sub, coefficient_truncation]
  by_cases hχ : χ ∈ largeSpectrum f ε
  · simp only [hχ, ite_true, sub_self, norm_zero, zero_pow (by omega : 2 ≠ 0)]
    positivity
  · have hsmall : ‖coefficient f χ‖ < ε := by
      simpa only [largeSpectrum, Finset.mem_filter, Finset.mem_univ, true_and, not_le] using hχ
    simp only [hχ, ite_false, sub_zero, coefficient_convolution, norm_mul, mul_pow]
    exact mul_le_mul_of_nonneg_right
      (pow_le_pow_left₀ (norm_nonneg _) hsmall.le 2) (sq_nonneg _)

end Erdos335.FiniteFourier
