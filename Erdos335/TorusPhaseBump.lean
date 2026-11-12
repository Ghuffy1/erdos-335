import Erdos335.TorusPolynomialApproximation
import Mathlib.MeasureTheory.Integral.Bochner.Set

/-!
# A continuous positive bump around the identity of a finite torus
-/

set_option autoImplicit false

open MeasureTheory
open scoped BigOperators

noncomputable section

local instance torusBumpMeasureSpace : MeasureSpace UnitAddCircle := ⟨AddCircle.haarAddCircle⟩
local instance torusBumpHaar : Measure.IsAddHaarMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (Measure.IsAddHaarMeasure AddCircle.haarAddCircle)
local instance torusBumpProbability : IsProbabilityMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (IsProbabilityMeasure AddCircle.haarAddCircle)

namespace Erdos335.IntermediateScale

def torusPhaseBump {I : Type*} [Fintype I] (η : ℝ) : C(UnitAddTorus I, ℝ) :=
  ⟨fun x => max 0 (η - ∑ i, ‖fourier (1 : ℤ) (x i) - 1‖), by fun_prop⟩

theorem torusPhaseBump_nonneg {I : Type*} [Fintype I] (η : ℝ) (x : UnitAddTorus I) :
    0 ≤ torusPhaseBump η x := le_max_left _ _

theorem torusPhaseBump_zero {I : Type*} [Fintype I] (η : ℝ) (hη : 0 ≤ η) :
    torusPhaseBump (I := I) η 0 = η := by
  simp [torusPhaseBump, hη]

theorem torusPhaseBump_positive_phases {I : Type*} [Fintype I]
    (η : ℝ) (x : UnitAddTorus I) (h : 0 < torusPhaseBump η x) :
    ∀ i, ‖fourier (1 : ℤ) (x i) - 1‖ < η := by
  have hsum : (∑ i, ‖fourier (1 : ℤ) (x i) - 1‖) < η := by
    change 0 < max 0 (η - ∑ i, ‖fourier (1 : ℤ) (x i) - 1‖) at h
    rcases lt_max_iff.mp h with hz | hp
    · exact (lt_irrefl _ hz).elim
    · linarith
  intro i
  exact (Finset.single_le_sum (fun j hj => norm_nonneg (fourier (1 : ℤ) (x j) - 1))
    (Finset.mem_univ i)).trans_lt hsum

theorem torusPhaseBump_integral_pos {I : Type*} [Fintype I]
    (η : ℝ) (hη : 0 < η) : 0 < ∫ x : UnitAddTorus I, torusPhaseBump η x := by
  apply (torusPhaseBump (I := I) η).continuous.integral_pos_of_hasCompactSupport_nonneg_nonzero
    (HasCompactSupport.of_compactSpace _) (torusPhaseBump_nonneg η)
  exact (torusPhaseBump_zero η hη.le).trans_ne hη.ne'

end Erdos335.IntermediateScale

end
