import Erdos335.TorusPolynomialApproximation
import Erdos335.BlockFourierTransfer

/-!
# Fourier monomials along an integer orbit of a finite torus
-/

set_option autoImplicit false

open scoped BigOperators

namespace Erdos335.IntermediateScale

theorem unitCharacter_sum {I : Type*} (S : Finset I) (f : I → ℝ) :
    unitCharacter (∑ i ∈ S, f i) = ∏ i ∈ S, unitCharacter (f i) := by
  classical
  induction S using Finset.induction_on with
  | empty => simp [unitCharacter]
  | @insert i S hi ih => simp [hi, unitCharacter_add, ih]

theorem fourier_coe_eq_unitCharacter (n : ℤ) (x : ℝ) :
    fourier n (x : UnitAddCircle) = unitCharacter ((n : ℝ) * x) := by
  rw [fourier_coe_apply, unitCharacter]
  congr 1
  push_cast
  ring

noncomputable def integerTorusOrbit {I : Type*} (α : I → ℝ) (m : ℕ) : UnitAddTorus I :=
  fun i => (((m : ℝ) * α i : ℝ) : UnitAddCircle)

theorem mFourier_integerTorusOrbit {I : Type*} [Fintype I]
    (w : I → ℤ) (α : I → ℝ) (m : ℕ) :
    UnitAddTorus.mFourier w (integerTorusOrbit α m) =
      unitCharacter ((m : ℝ) * ∑ i, (w i : ℝ) * α i) := by
  rw [Finset.mul_sum, unitCharacter_sum]
  change (∏ i, fourier (w i) (((m : ℝ) * α i : ℝ) : UnitAddCircle)) = _
  apply Finset.prod_congr rfl
  intro i hi
  rw [fourier_coe_eq_unitCharacter]
  congr 1
  ring

theorem fourier_integerTorusOrbit {I : Type*} (α : I → ℝ) (m : ℕ) (i : I) :
    fourier (1 : ℤ) (integerTorusOrbit α m i) = unitCharacter ((m : ℝ) * α i) := by
  simpa [integerTorusOrbit] using fourier_coe_eq_unitCharacter 1 ((m : ℝ) * α i)

end Erdos335.IntermediateScale
