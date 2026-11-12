import Erdos335.PolynomialParameterModels
import Erdos335.PolynomialTranslation

/-!
# Polynomial translations on windows with constant parameters
-/

set_option autoImplicit false

open Finset
open scoped BigOperators

namespace Erdos335.IntermediateScale

theorem polynomial_parameters_constant_of_not_mem {d : ℕ}
    (c : ℕ → Fin d → ℂ) (α : ℕ → Fin d → ℝ) (N n W : ℕ)
    (hn : n < N) (hgood : n ∉ varyingPolynomialParameters N W c α)
    (i : ℕ) (hi : i ≤ W) : c (n + i) = c n ∧ α (n + i) = α n := by
  constructor
  · funext j
    by_contra h
    exact hgood (mem_filter.mpr ⟨mem_range.mpr hn, i, hi, j, Or.inl h⟩)
  · funext j
    by_contra h
    exact hgood (mem_filter.mpr ⟨mem_range.mpr hn, i, hi, j, Or.inr h⟩)

theorem variable_polynomial_translation_norm_le {d : ℕ}
    (c : ℕ → Fin d → ℂ) (α : ℕ → Fin d → ℝ) (n t Q W : ℕ)
    (ht : t ≤ W) (hQ : Q ≤ 2 * W) (η : ℝ)
    (hc : ∀ j, ‖c n j‖ ≤ 1)
    (hphase : ∀ j, ‖unitCharacter ((Q : ℝ) * α n j) - 1‖ ≤ η)
    (hconstant : ∀ i ≤ 3 * W, c (n + i) = c n ∧ α (n + i) = α n) :
    ‖variableFrequencyPolynomial c α (n + t + Q) - variableFrequencyPolynomial c α (n + t)‖ ≤ d * η := by
  have ht' := hconstant t (by omega)
  have hQ' := hconstant (t + Q) (by omega)
  unfold variableFrequencyPolynomial
  rw [Nat.add_assoc n t Q, hQ'.1, hQ'.2, ht'.1, ht'.2]
  simpa only [Nat.add_assoc] using polynomial_translation_norm_le (c n) (α n) (n + t) Q η hc hphase

theorem variable_polynomial_translation_of_not_mem {d : ℕ}
    (c : ℕ → Fin d → ℂ) (α : ℕ → Fin d → ℝ) (N n t Q W : ℕ)
    (hn : n < N) (ht : t ≤ W) (hQ : Q ≤ 2 * W) (η : ℝ)
    (hc : ∀ j, ‖c n j‖ ≤ 1)
    (hphase : ∀ j, ‖unitCharacter ((Q : ℝ) * α n j) - 1‖ ≤ η)
    (hgood : n ∉ varyingPolynomialParameters N (3 * W) c α) :
    ‖variableFrequencyPolynomial c α (n + t + Q) - variableFrequencyPolynomial c α (n + t)‖ ≤ d * η :=
  variable_polynomial_translation_norm_le c α n t Q W ht hQ η hc hphase
    (polynomial_parameters_constant_of_not_mem c α N n (3 * W) hn hgood)

end Erdos335.IntermediateScale
