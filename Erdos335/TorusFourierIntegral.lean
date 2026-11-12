import Erdos335.TorusPolynomialApproximation

/-!
# Haar integrals of the multivariate Fourier monomials
-/

set_option autoImplicit false

open MeasureTheory
open scoped BigOperators InnerProductSpace

noncomputable section

local instance torusIntegralMeasureSpace : MeasureSpace UnitAddCircle := ⟨AddCircle.haarAddCircle⟩
local instance torusIntegralProbability : IsProbabilityMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (IsProbabilityMeasure AddCircle.haarAddCircle)

namespace Erdos335.IntermediateScale

theorem integral_torus_monomial {I : Type*} [Fintype I] (n : I → ℤ) :
    (∫ x : UnitAddTorus I, UnitAddTorus.mFourier n x) = if n = 0 then 1 else 0 := by
  classical
  have h := (orthonormal_iff_ite.mp (UnitAddTorus.orthonormal_mFourier (d := I))) 0 n
  simpa [UnitAddTorus.mFourierLp, ContinuousMap.inner_toLp, UnitAddTorus.mFourier_zero,
    RCLike.inner_apply, eq_comm] using h

theorem integrable_torus_monomial {I : Type*} [Fintype I] (n : I → ℤ) :
    Integrable (UnitAddTorus.mFourier n) (volume : Measure (UnitAddTorus I)) := by
  exact (UnitAddTorus.mFourier n).continuous.integrable_of_hasCompactSupport
    (HasCompactSupport.of_compactSpace _)

theorem integral_torus_polynomial {I : Type*} [Fintype I]
    (S : Finset (I → ℤ)) (c : (I → ℤ) → ℂ) :
    (∫ x : UnitAddTorus I, ∑ n ∈ S, c n * UnitAddTorus.mFourier n x) =
      if (0 : I → ℤ) ∈ S then c 0 else 0 := by
  classical
  rw [integral_finset_sum S (fun n hn => (integrable_torus_monomial n).const_mul (c n))]
  simp [integral_const_mul, integral_torus_monomial]

theorem torus_polynomial_integral_error {I : Type*} [Fintype I]
    (F : C(UnitAddTorus I, ℂ)) (S : Finset (I → ℤ)) (c : (I → ℤ) → ℂ) (ε : ℝ)
    (h : ∀ x, ‖F x - ∑ n ∈ S, c n * UnitAddTorus.mFourier n x‖ ≤ ε) :
    ‖(∫ x : UnitAddTorus I, F x) - (if (0 : I → ℤ) ∈ S then c 0 else 0)‖ ≤ ε := by
  classical
  let P : C(UnitAddTorus I, ℂ) := ∑ n ∈ S, c n • UnitAddTorus.mFourier n
  have hP (x : UnitAddTorus I) : P x = ∑ n ∈ S, c n * UnitAddTorus.mFourier n x := by
    simp [P]
  have hFi : Integrable F (volume : Measure (UnitAddTorus I)) :=
    F.continuous.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have hPi : Integrable P (volume : Measure (UnitAddTorus I)) :=
    P.continuous.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have hb := norm_integral_le_of_norm_le_const (μ := (volume : Measure (UnitAddTorus I)))
    (f := fun x => F x - P x) (Filter.Eventually.of_forall fun x => by simpa only [hP] using h x)
  rw [integral_sub hFi hPi] at hb
  have hIntegralP : (∫ x : UnitAddTorus I, P x) = if (0 : I → ℤ) ∈ S then c 0 else 0 := by
    simpa only [hP] using integral_torus_polynomial S c
  rw [hIntegralP] at hb
  simpa using hb

theorem exists_torus_polynomial_with_constant {I : Type*} [Fintype I]
    (F : C(UnitAddTorus I, ℂ)) (hF : 0 < ‖∫ x : UnitAddTorus I, F x‖) :
    ∃ (S : Finset (I → ℤ)) (c : (I → ℤ) → ℂ), (0 : I → ℤ) ∈ S ∧
      ‖∫ x : UnitAddTorus I, F x‖ / 2 < ‖c 0‖ ∧
      ∀ x, ‖F x - ∑ n ∈ S, c n * UnitAddTorus.mFourier n x‖ <
        ‖∫ x : UnitAddTorus I, F x‖ / 4 := by
  classical
  obtain ⟨S, c, hc⟩ := exists_torus_polynomial_approximation F
    (‖∫ x : UnitAddTorus I, F x‖ / 4) (by positivity)
  have hb := torus_polynomial_integral_error F S c (‖∫ x : UnitAddTorus I, F x‖ / 4)
    (fun x => (hc x).le)
  have hzero : (0 : I → ℤ) ∈ S := by
    by_contra hzero
    simp only [hzero, ite_false, sub_zero] at hb
    linarith
  simp only [hzero, ite_true] at hb
  have ht := norm_add_le ((∫ x : UnitAddTorus I, F x) - c 0) (c 0)
  rw [sub_add_cancel] at ht
  refine ⟨S, c, hzero, ?_, hc⟩
  linarith

end Erdos335.IntermediateScale

end
