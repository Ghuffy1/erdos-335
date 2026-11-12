import Erdos335.TorusSelfCorrelation
import Erdos335.TorusPhaseBump

/-!
# Localization of a positive Fourier polynomial obtained from a bump
-/

set_option autoImplicit false

open MeasureTheory
open scoped BigOperators ComplexConjugate

noncomputable section

local instance torusBumpCorrelationMeasureSpace : MeasureSpace UnitAddCircle :=
  ⟨AddCircle.haarAddCircle⟩
local instance torusBumpCorrelationProbability : IsProbabilityMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (IsProbabilityMeasure AddCircle.haarAddCircle)

namespace Erdos335.IntermediateScale

theorem unit_mul_sub_one_triangle (z w : ℂ) (hz : ‖z‖ = 1) :
    ‖z - 1‖ ≤ ‖z * w - 1‖ + ‖w - 1‖ := by
  have heq : z - 1 = (z * w - 1) - z * (w - 1) := by ring
  rw [heq]
  calc
    _ ≤ ‖z * w - 1‖ + ‖z * (w - 1)‖ := norm_sub_le _ _
    _ = _ := by rw [norm_mul, hz, one_mul]

theorem torusPhaseBump_le {I : Type*} [Fintype I] (η : ℝ) (hη : 0 ≤ η)
    (x : UnitAddTorus I) : torusPhaseBump η x ≤ η := by
  change max 0 (η - ∑ i, ‖fourier (1 : ℤ) (x i) - 1‖) ≤ η
  exact max_le hη (sub_le_self _ (Finset.sum_nonneg fun i hi => norm_nonneg _))

theorem torusPhaseBump_product_zero {I : Type*} [Fintype I]
    (η : ℝ) (x y : UnitAddTorus I)
    (hfar : ∃ i, 2 * η ≤ ‖fourier (1 : ℤ) (x i) - 1‖) :
    torusPhaseBump η (x + y) * torusPhaseBump η y = 0 := by
  by_cases hx : torusPhaseBump η (x + y) = 0
  · simp only [hx, zero_mul]
  by_cases hy : torusPhaseBump η y = 0
  · simp only [hy, mul_zero]
  have hxpos : 0 < torusPhaseBump η (x + y) :=
    lt_of_le_of_ne (torusPhaseBump_nonneg η _) (Ne.symm hx)
  have hypos : 0 < torusPhaseBump η y :=
    lt_of_le_of_ne (torusPhaseBump_nonneg η _) (Ne.symm hy)
  obtain ⟨i, hi⟩ := hfar
  have hxsmall := torusPhaseBump_positive_phases η (x + y) hxpos i
  have hysmall := torusPhaseBump_positive_phases η y hypos i
  have hz : ‖fourier (1 : ℤ) (x i)‖ = 1 := by simp only [fourier_apply, Circle.norm_coe]
  have ht := unit_mul_sub_one_triangle (fourier (1 : ℤ) (x i)) (fourier (1 : ℤ) (y i)) hz
  rw [← fourier_add_points] at ht
  change ‖fourier (1 : ℤ) (x i) - 1‖ ≤
    ‖fourier (1 : ℤ) ((x + y) i) - 1‖ + ‖fourier (1 : ℤ) (y i) - 1‖ at ht
  exfalso
  linarith

theorem correlation_product_error (p q g h : ℂ) (η ε : ℝ)
    (hη : 0 ≤ η) (hε : 0 ≤ ε) (hg : ‖g‖ ≤ η) (hh : ‖h‖ ≤ η)
    (hp : ‖p - g‖ ≤ ε) (hq : ‖q - h‖ ≤ ε) (hzero : g * conj h = 0) :
    ‖p * conj q‖ ≤ ε * (2 * η + ε) := by
  have hqn : ‖q‖ ≤ η + ε := by
    have ht' := norm_add_le (q - h) h
    rw [sub_add_cancel] at ht'
    linarith
  have heq : p * conj q = (p - g) * conj q + g * conj (q - h) := by
    rw [map_sub]
    have ht : (p - g) * conj q + g * (conj q - conj h) = p * conj q - g * conj h := by ring
    rw [ht, hzero, sub_zero]
  rw [heq]
  calc
    _ ≤ ‖(p - g) * conj q‖ + ‖g * conj (q - h)‖ := norm_add_le _ _
    _ = ‖p - g‖ * ‖q‖ + ‖g‖ * ‖q - h‖ := by simp only [norm_mul, Complex.norm_conj]
    _ ≤ ε * (η + ε) + η * ε := by gcongr
    _ = ε * (2 * η + ε) := by ring

theorem torus_bump_correlation_small {I : Type*} [Fintype I]
    (η ε : ℝ) (hη : 0 ≤ η) (hε : 0 ≤ ε)
    (S : Finset (I → ℤ)) (c : (I → ℤ) → ℂ)
    (happrox : ∀ x : UnitAddTorus I,
      ‖(∑ w ∈ S, c w * UnitAddTorus.mFourier w x) - (torusPhaseBump η x : ℂ)‖ ≤ ε)
    (x : UnitAddTorus I) (hfar : ∃ i, 2 * η ≤ ‖fourier (1 : ℤ) (x i) - 1‖) :
    ‖∑ w ∈ S, (‖c w‖ ^ 2 : ℝ) * UnitAddTorus.mFourier w x‖ ≤ ε * (2 * η + ε) := by
  rw [← torus_polynomial_self_correlation S c x]
  have hb : ∀ y : UnitAddTorus I,
      ‖(∑ u ∈ S, c u * UnitAddTorus.mFourier u (x + y)) *
        conj (∑ v ∈ S, c v * UnitAddTorus.mFourier v y)‖ ≤ ε * (2 * η + ε) := by
    intro y
    apply correlation_product_error _ _ (torusPhaseBump η (x + y)) (torusPhaseBump η y)
      η ε hη hε
    · simpa only [Complex.norm_real, Real.norm_eq_abs,
        abs_of_nonneg (torusPhaseBump_nonneg η _)] using torusPhaseBump_le η hη (x + y)
    · simpa only [Complex.norm_real, Real.norm_eq_abs,
        abs_of_nonneg (torusPhaseBump_nonneg η _)] using torusPhaseBump_le η hη y
    · exact happrox (x + y)
    · exact happrox y
    · simpa only [Complex.conj_ofReal, ← Complex.ofReal_mul, Complex.ofReal_eq_zero] using
        torusPhaseBump_product_zero η x y hfar
  have ht := norm_integral_le_of_norm_le_const (μ := (volume : Measure (UnitAddTorus I)))
    (Filter.Eventually.of_forall hb)
  simpa using ht

end Erdos335.IntermediateScale

end
