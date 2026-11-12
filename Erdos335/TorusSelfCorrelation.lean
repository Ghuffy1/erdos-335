import Erdos335.TorusFourierIntegral

/-!
# Positive Fourier coefficients from the self-correlation of a polynomial
-/

set_option autoImplicit false

open MeasureTheory
open scoped BigOperators ComplexConjugate

noncomputable section

local instance torusCorrelationMeasureSpace : MeasureSpace UnitAddCircle :=
  ⟨AddCircle.haarAddCircle⟩
local instance torusCorrelationProbability : IsProbabilityMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (IsProbabilityMeasure AddCircle.haarAddCircle)

namespace Erdos335.IntermediateScale

theorem fourier_add_points (n : ℤ) (x y : UnitAddCircle) :
    fourier n (x + y) = fourier n x * fourier n y := by
  simp only [fourier_apply, zsmul_add, AddCircle.toCircle_add, Circle.coe_mul]

theorem mFourier_add_points {I : Type*} [Fintype I]
    (w : I → ℤ) (x y : UnitAddTorus I) :
    UnitAddTorus.mFourier w (x + y) = UnitAddTorus.mFourier w x * UnitAddTorus.mFourier w y := by
  simp only [UnitAddTorus.mFourier, ContinuousMap.coe_mk, Pi.add_apply,
    fourier_add_points, Finset.prod_mul_distrib]

theorem mFourier_sub_indices {I : Type*} [Fintype I]
    (u v : I → ℤ) (x : UnitAddTorus I) :
    UnitAddTorus.mFourier (u - v) x =
      UnitAddTorus.mFourier u x * conj (UnitAddTorus.mFourier v x) := by
  rw [sub_eq_add_neg, UnitAddTorus.mFourier_add, UnitAddTorus.mFourier_neg]

theorem torus_polynomial_self_correlation {I : Type*} [Fintype I]
    (S : Finset (I → ℤ)) (c : (I → ℤ) → ℂ) (x : UnitAddTorus I) :
    (∫ y : UnitAddTorus I,
      (∑ u ∈ S, c u * UnitAddTorus.mFourier u (x + y)) *
        conj (∑ v ∈ S, c v * UnitAddTorus.mFourier v y)) =
      ∑ w ∈ S, (‖c w‖ ^ 2 : ℝ) * UnitAddTorus.mFourier w x := by
  classical
  have hexpand (y : UnitAddTorus I) :
      (∑ u ∈ S, c u * UnitAddTorus.mFourier u (x + y)) *
        conj (∑ v ∈ S, c v * UnitAddTorus.mFourier v y) =
      ∑ u ∈ S, ∑ v ∈ S,
        (c u * conj (c v) * UnitAddTorus.mFourier u x) * UnitAddTorus.mFourier (u - v) y := by
    simp only [map_sum, map_mul, Finset.sum_mul, Finset.mul_sum]
    conv_lhs => rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro u hu
    apply Finset.sum_congr rfl
    intro v hv
    rw [mFourier_add_points, mFourier_sub_indices]
    ring
  have hi (u v : I → ℤ) : Integrable (fun y : UnitAddTorus I =>
      (c u * conj (c v) * UnitAddTorus.mFourier u x) * UnitAddTorus.mFourier (u - v) y)
      (volume : Measure (UnitAddTorus I)) :=
    (integrable_torus_monomial (u - v)).const_mul _
  simp_rw [hexpand]
  rw [integral_finsetSum S (fun u hu => integrable_finsetSum S fun v hv => hi u v)]
  apply Finset.sum_congr rfl
  intro u hu
  rw [integral_finsetSum S (fun v hv => hi u v)]
  simp only [integral_const_mul, integral_torus_monomial, sub_eq_zero]
  simp only [mul_ite, mul_one, mul_zero, Finset.sum_ite_eq, hu, ite_true]
  rw [Complex.mul_conj, Complex.normSq_eq_norm_sq]

end Erdos335.IntermediateScale

end
