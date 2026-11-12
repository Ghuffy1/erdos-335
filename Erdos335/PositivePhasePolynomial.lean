import Erdos335.TorusBumpCorrelation

/-!
# A localized finite Fourier polynomial with nonnegative coefficients
-/

set_option autoImplicit false

open MeasureTheory
open scoped BigOperators

noncomputable section

local instance positivePhaseMeasureSpace : MeasureSpace UnitAddCircle := ⟨AddCircle.haarAddCircle⟩
local instance positivePhaseProbability : IsProbabilityMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (IsProbabilityMeasure AddCircle.haarAddCircle)

namespace Erdos335.IntermediateScale

theorem exists_positive_phase_polynomial {I : Type*} [Fintype I] (η : ℝ) (hη : 0 < η) :
    ∃ (S : Finset (I → ℤ)) (q : (I → ℤ) → ℝ),
      (0 : I → ℤ) ∈ S ∧ (∀ w, 0 ≤ q w) ∧ 0 < q 0 ∧
      ∀ x : UnitAddTorus I, (∃ i, η ≤ ‖fourier (1 : ℤ) (x i) - 1‖) →
        ‖∑ w ∈ S, (q w : ℂ) * UnitAddTorus.mFourier w x‖ < q 0 / 4 := by
  classical
  let G := torusPhaseBump (I := I) (η / 2)
  let F : C(UnitAddTorus I, ℂ) := ⟨fun x => (G x : ℂ), by fun_prop⟩
  let v : ℝ := ∫ x : UnitAddTorus I, G x
  have hv : 0 < v := torusPhaseBump_integral_pos _ (by positivity)
  have hF : ‖∫ x : UnitAddTorus I, F x‖ = v := by
    change ‖∫ x : UnitAddTorus I, (G x : ℂ)‖ = v
    rw [integral_complex_ofReal, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hv]
  let ε := min 1 (min (v / 4) (v ^ 2 / (32 * (η + 1))))
  have hε : 0 < ε := by dsimp [ε]; positivity
  have hε1 : ε ≤ 1 := min_le_left _ _
  have hεv : ε ≤ v / 4 := (min_le_right _ _).trans (min_le_left _ _)
  have hεsmall : ε ≤ v ^ 2 / (32 * (η + 1)) :=
    (min_le_right _ _).trans (min_le_right _ _)
  obtain ⟨S, c, happrox⟩ := exists_torus_polynomial_approximation F ε hε
  have herr := torus_polynomial_integral_error F S c ε (fun x => (happrox x).le)
  have hzero : (0 : I → ℤ) ∈ S := by
    by_contra hz
    simp only [hz, ite_false, sub_zero, hF] at herr
    have heps : ε ≤ v / 4 := by simpa only [hF] using hεv
    linarith
  simp only [hzero, ite_true] at herr
  have hc0 : v / 2 < ‖c 0‖ := by
    have ht := norm_add_le ((∫ x : UnitAddTorus I, F x) - c 0) (c 0)
    rw [sub_add_cancel, hF] at ht
    have heps : ε ≤ v / 4 := by simpa only [hF] using hεv
    linarith
  let q : (I → ℤ) → ℝ := fun w => ‖c w‖ ^ 2
  have hq0 : 0 < q 0 := by dsimp [q]; exact sq_pos_of_pos (by linarith)
  have herror : ε * (η + ε) < q 0 / 4 := by
    have hden : 0 < 32 * (η + 1) := by positivity
    have hmul := (le_div_iff₀ hden).mp hεsmall
    have hle : ε * (η + ε) ≤ ε * (η + 1) := by gcongr
    dsimp [q]
    nlinarith [sq_nonneg (‖c 0‖ - v / 2)]
  refine ⟨S, q, hzero, fun w => sq_nonneg _, hq0, ?_⟩
  intro x hx
  have hb := torus_bump_correlation_small (η / 2) ε (by positivity) hε.le S c
    (fun y => by simpa only [F, ContinuousMap.coe_mk, G, norm_sub_rev] using (happrox y).le)
    x (by simpa only [show 2 * (η / 2) = η by ring] using hx)
  exact hb.trans_lt (by simpa only [show 2 * (η / 2) = η by ring] using herror)

end Erdos335.IntermediateScale

end
