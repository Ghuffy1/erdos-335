import Erdos335.CircleFiniteFamilyApproximation
import Erdos335.SoftQuantizedTests

/-!
# A uniformly bounded table of one-dimensional cell polynomials
-/

set_option autoImplicit false

open scoped Topology BigOperators

namespace Erdos335.IntermediateScale

def circleCoordinate (b : Bool) (z : Circle) : ℝ :=
  if b then (z : ℂ).re else (z : ℂ).im

theorem circleCoordinate_continuous (b : Bool) : Continuous (circleCoordinate b) := by
  cases b <;> unfold circleCoordinate <;> simp only [Bool.false_eq_true, ite_false, ite_true] <;> fun_prop

theorem shiftedTest_continuous (N M : ℕ) (j : Fin M) : Continuous (shiftedTest N M j) := by
  unfold shiftedTest
  fun_prop

noncomputable def circleCell (N M : ℕ) (tag : Bool × Fin M × Fin (2 * N + 1)) : C(Circle, ℂ) :=
  ⟨fun z => (softQuantizedCell N M tag.2.2
      (shiftedTest N M tag.2.1 (circleCoordinate tag.1 z)) : ℝ),
    Complex.continuous_ofReal.comp ((softQuantizedCell_continuous N M tag.2.2).comp
      ((shiftedTest_continuous N M tag.2.1).comp (circleCoordinate_continuous tag.1)))⟩

theorem circleCell_norm_le_one (N M : ℕ) (tag : Bool × Fin M × Fin (2 * N + 1)) (z : Circle) :
    ‖circleCell N M tag z‖ ≤ 1 := by
  have h := softCell_bounds M tag.2.2.val
    ((N : ℝ) * (shiftedTest N M tag.2.1 (circleCoordinate tag.1 z) + 1))
  change ‖((softCell M tag.2.2.val
    ((N : ℝ) * (shiftedTest N M tag.2.1 (circleCoordinate tag.1 z) + 1)) : ℝ) : ℂ)‖ ≤ 1
  rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg h.1]
  exact h.2

theorem uniform_circleCell_polynomials (N M : ℕ) (ε : ℝ) (hε : 0 < ε) :
    ∃ (K : ℕ) (S : (Bool × Fin M × Fin (2 * N + 1)) → Finset ℤ)
      (w : (Bool × Fin M × Fin (2 * N + 1)) → ℤ → ℂ),
      0 < K ∧ (∀ tag, (S tag).card ≤ K) ∧
      (∀ tag n, n ∈ S tag → n.natAbs ≤ K ∧ ‖w tag n‖ ≤ K) ∧
      ∀ tag z, ‖circleCell N M tag z - ∑ n ∈ S tag, w tag n * (z : ℂ) ^ n‖ < ε := by
  exact finite_family_circle_approximation (circleCell N M) ε hε

end Erdos335.IntermediateScale
