import Erdos335.FiniteL2PolynomialError
import Mathlib.Algebra.Order.BigOperators.Ring.Finset

/-!
# Correlation estimates from a finite character approximation
-/

set_option autoImplicit false

open Finset
open scoped BigOperators

namespace Erdos335.IntermediateScale

theorem finite_l1_of_mean_square {X : Type*} [Fintype X] [Nonempty X]
    (e : X → ℂ) (ε : ℝ) (hε : 0 ≤ ε)
    (he : (∑ x : X, ‖e x‖ ^ 2) / Fintype.card X ≤ ε ^ 2) :
    ∑ x : X, ‖e x‖ ≤ ε * Fintype.card X := by
  have hcard : (0 : ℝ) < Fintype.card X := by exact_mod_cast Fintype.card_pos
  have hcs := sum_mul_sq_le_sq_mul_sq (univ : Finset X) (fun x => ‖e x‖) (fun _ => (1 : ℝ))
  simp only [mul_one, one_pow, sum_const, card_univ, nsmul_eq_mul] at hcs
  have hbase := (div_le_iff₀ hcard).mp he
  have hsquare : (∑ x : X, ‖e x‖) ^ 2 ≤ (ε * Fintype.card X) ^ 2 := by nlinarith
  have hnonneg := sum_nonneg (fun x (_ : x ∈ (univ : Finset X)) => norm_nonneg (e x))
  nlinarith [mul_nonneg hε hcard.le]

theorem finite_polynomial_correlation_bound
    {X I : Type*} [Fintype X] [Nonempty X] [Fintype I]
    (s r : X → ℝ) (ψ : I → X → ℂ) (a : I → ℂ)
    (ε η : ℝ) (hε : 0 ≤ ε)
    (hr : ∀ x, |r x| ≤ 1) (ha : ∀ i, ‖a i‖ ≤ 1)
    (happrox : (∑ x : X, ‖(s x : ℂ) - ∑ i, a i * ψ i x‖ ^ 2) /
      Fintype.card X ≤ ε ^ 2)
    (htest : ∀ i, ‖∑ x : X, (r x : ℂ) * ψ i x‖ ≤ η * Fintype.card X) :
    |∑ x : X, s x * r x| ≤ (ε + Fintype.card I * η) * Fintype.card X := by
  let p := fun x => ∑ i, a i * ψ i x
  have he := finite_l1_of_mean_square (fun x => (s x : ℂ) - p x) ε hε happrox
  have herror : ‖∑ x : X, ((s x : ℂ) - p x) * (r x : ℂ)‖ ≤ ε * Fintype.card X := by
    apply (norm_sum_le _ _).trans
    calc
      _ ≤ ∑ x : X, ‖(s x : ℂ) - p x‖ := by
        apply sum_le_sum
        intro x hx
        rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
        exact mul_le_of_le_one_right (norm_nonneg _) (hr x)
      _ ≤ _ := he
  have hpoly : ‖∑ i : I, a i * ∑ x : X, (r x : ℂ) * ψ i x‖ ≤
      Fintype.card I * (η * Fintype.card X) := by
    apply (norm_sum_le _ _).trans
    calc
      _ ≤ ∑ _i : I, η * Fintype.card X := by
        apply sum_le_sum
        intro i hi
        rw [norm_mul]
        calc
          _ ≤ 1 * (η * Fintype.card X) := mul_le_mul (ha i) (htest i) (norm_nonneg _) zero_le_one
          _ = _ := one_mul _
      _ = _ := by simp
  have heq : ((∑ x : X, s x * r x : ℝ) : ℂ) =
      (∑ x : X, ((s x : ℂ) - p x) * (r x : ℂ)) +
        ∑ i : I, a i * ∑ x : X, (r x : ℂ) * ψ i x := by
    simp only [mul_sum]
    rw [sum_comm]
    rw [← sum_add_distrib]
    push_cast
    apply sum_congr rfl
    intro x hx
    dsimp [p]
    have hreorder : (∑ i : I, a i * ((r x : ℂ) * ψ i x)) =
        (∑ i : I, a i * ψ i x) * (r x : ℂ) := by
      rw [sum_mul]
      apply sum_congr rfl
      intro i hi
      ring
    rw [hreorder]
    ring
  have hnorm := norm_add_le
    (∑ x : X, ((s x : ℂ) - p x) * (r x : ℂ))
    (∑ i : I, a i * ∑ x : X, (r x : ℂ) * ψ i x)
  rw [← heq, Complex.norm_real, Real.norm_eq_abs] at hnorm
  nlinarith

end Erdos335.IntermediateScale
