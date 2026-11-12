import Erdos335.TorusFourierIntegral
import Erdos335.TorusPhaseBump
import Erdos335.TorusIntegerOrbit
import Erdos335.PolynomialOrbitHitting

/-!
# Finite Fourier tests for a simultaneous approximate period
-/

set_option autoImplicit false

open MeasureTheory
open scoped BigOperators

noncomputable section

local instance torusPhaseTestMeasureSpace : MeasureSpace UnitAddCircle := ⟨AddCircle.haarAddCircle⟩
local instance torusPhaseTestProbability : IsProbabilityMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (IsProbabilityMeasure AddCircle.haarAddCircle)

namespace Erdos335.IntermediateScale

theorem exists_torus_phase_test {I : Type*} [Fintype I] (η : ℝ) (hη : 0 < η) :
    ∃ (S : Finset (I → ℤ)) (K : ℝ), 0 < K ∧
      ∀ (α : I → ℝ) (a L : ℕ) (κ : ℝ), 0 < L → 0 < κ → K < (L : ℝ) * κ →
        (∀ w ∈ S, w ≠ 0 → κ ≤ ‖unitCharacter (∑ i, (w i : ℝ) * α i) - 1‖) →
        ∃ m < L, ∀ i, ‖unitCharacter (((a + m : ℕ) : ℝ) * α i) - 1‖ < η := by
  classical
  let F : C(UnitAddTorus I, ℂ) :=
    ⟨fun x => (torusPhaseBump η x : ℂ), by fun_prop⟩
  let v : ℝ := ∫ x : UnitAddTorus I, torusPhaseBump η x
  have hv : 0 < v := torusPhaseBump_integral_pos η hη
  have hF : ‖∫ x : UnitAddTorus I, F x‖ = v := by
    change ‖∫ x : UnitAddTorus I, (torusPhaseBump η x : ℂ)‖ = v
    rw [integral_complex_ofReal, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hv]
  obtain ⟨S, c, hzero, hc, happrox⟩ := exists_torus_polynomial_with_constant F (by rw [hF]; exact hv)
  rw [hF] at hc
  have happrox' (x : UnitAddTorus I) :
      ‖F x - ∑ w ∈ S, c w * UnitAddTorus.mFourier w x‖ < v / 4 := by
    simpa only [hF] using happrox x
  let mass : ℝ := ∑ w ∈ S, ‖c w‖
  have hmass : 0 ≤ mass := Finset.sum_nonneg fun w hw => norm_nonneg _
  let K : ℝ := 8 * mass / v + 1
  have hK : 0 < K := by dsimp [K]; positivity
  refine ⟨S, K, hK, ?_⟩
  intro α a L κ hL hκ hlarge hsep
  have hden : 0 < (L : ℝ) * κ := mul_pos (by exact_mod_cast hL) hκ
  have herror : mass * (2 / ((L : ℝ) * κ)) < v / 4 := by
    have hb : 8 * mass < v * ((L : ℝ) * κ) := by
      have ht := (div_lt_iff₀ hv).mp (show 8 * mass / v < (L : ℝ) * κ by
        dsimp [K] at hlarge
        linarith)
      nlinarith
    apply (lt_div_iff₀ (by norm_num : (0 : ℝ) < 4)).mpr
    have ht := (div_lt_iff₀ hden).mpr (show 8 * mass < v * ((L : ℝ) * κ) from hb)
    convert ht using 1 <;> ring
  let i₀ : ↥S := ⟨0, hzero⟩
  let β : ↥S → ℝ := fun w => ∑ i, (w.val i : ℝ) * α i
  have hβzero : β i₀ = 0 := by simp [β, i₀]
  have hβsep (w : ↥S) (hw : w ≠ i₀) : κ ≤ ‖unitCharacter (β w) - 1‖ := by
    apply hsep w.val w.property
    intro he
    apply hw
    exact Subtype.ext he
  have hmass' : (∑ w : ↥S, ‖c w.val‖) = mass := by
    dsimp [mass]
    exact Finset.sum_attach S (fun w => ‖c w‖)
  obtain ⟨m, hm, hvalue⟩ := exists_large_orbit_polynomial_value
    (fun w : ↥S => c w.val) β i₀ a L hL κ (v / 4) hκ hβzero hβsep (by
      rw [hmass']
      change v / 4 + mass * (2 / ((L : ℝ) * κ)) < ‖c 0‖
      linarith)
  have hpoly : (∑ w : ↥S, c w.val * unitCharacter (((a + m : ℕ) : ℝ) * β w)) =
      ∑ w ∈ S, c w * UnitAddTorus.mFourier w (integerTorusOrbit α (a + m)) := by
    simp only [mFourier_integerTorusOrbit, β]
    rw [Finset.univ_eq_attach]
    exact Finset.sum_attach S
      (fun w => c w * unitCharacter (((a + m : ℕ) : ℝ) * ∑ i, (w i : ℝ) * α i))
  rw [hpoly] at hvalue
  have hbump : 0 < torusPhaseBump η (integerTorusOrbit α (a + m)) := by
    have herrorF := happrox' (integerTorusOrbit α (a + m))
    have heq : ‖(∑ w ∈ S, c w * UnitAddTorus.mFourier w (integerTorusOrbit α (a + m))) -
        F (integerTorusOrbit α (a + m))‖ =
        ‖F (integerTorusOrbit α (a + m)) -
          ∑ w ∈ S, c w * UnitAddTorus.mFourier w (integerTorusOrbit α (a + m))‖ := norm_sub_rev _ _
    have hn : ‖F (integerTorusOrbit α (a + m))‖ =
        torusPhaseBump η (integerTorusOrbit α (a + m)) := by
      change ‖(torusPhaseBump η (integerTorusOrbit α (a + m)) : ℂ)‖ = _
      rw [Complex.norm_real, Real.norm_eq_abs,
        abs_of_nonneg (torusPhaseBump_nonneg η _)]
    have htri := norm_add_le
      (F (integerTorusOrbit α (a + m)))
      ((∑ w ∈ S, c w * UnitAddTorus.mFourier w (integerTorusOrbit α (a + m))) -
        F (integerTorusOrbit α (a + m)))
    rw [add_sub_cancel, heq, hn] at htri
    linarith
  refine ⟨m, hm, ?_⟩
  intro i
  simpa only [fourier_integerTorusOrbit] using torusPhaseBump_positive_phases η _ hbump i

end Erdos335.IntermediateScale

end
