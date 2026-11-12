import Erdos335.IntermediateFrequencySeparation
import Erdos335.PulledCharacterTests
import Mathlib.Analysis.SpecialFunctions.Complex.Circle

/-!
# Real-frequency descriptions of circle-valued integer characters
-/

set_option autoImplicit false

open scoped ComplexConjugate

namespace Erdos335.IntermediateScale

noncomputable def integerCircleCharacter (α : ℝ) : AddChar ℤ Circle where
  toFun n := Circle.exp (2 * Real.pi * (n : ℝ) * α)
  map_zero_eq_one' := by simp
  map_add_eq_mul' m n := by
    rw [← Circle.exp_add]
    congr 1
    push_cast
    ring

theorem integerCircleCharacter_coe (α : ℝ) (n : ℤ) :
    (integerCircleCharacter α n : ℂ) = unitCharacter ((n : ℝ) * α) := by
  change (Circle.exp (2 * Real.pi * (n : ℝ) * α) : ℂ) = _
  rw [Circle.coe_exp, unitCharacter]
  congr 1
  push_cast
  ring

theorem integerCircleCharacter_representation (χ : AddChar ℤ Circle) :
    ∃ α : ℝ, ∀ n : ℤ, (χ n : ℂ) = unitCharacter ((n : ℝ) * α) := by
  let α := Complex.arg (χ 1 : ℂ) / (2 * Real.pi)
  have hbase : χ 1 = Circle.exp (2 * Real.pi * α) := by
    have heq : 2 * Real.pi * α = Complex.arg (χ 1 : ℂ) := by
      dsimp [α]
      field_simp
    rw [heq, Circle.exp_arg]
  refine ⟨α, fun n => ?_⟩
  have hn : χ n = (χ 1) ^ n := by
    simpa using χ.map_zsmul_eq_zpow n (1 : ℤ)
  rw [hn, hbase, ← Circle.exp_intCast_mul]
  rw [Circle.coe_exp, unitCharacter]
  congr 1
  push_cast
  ring

theorem integer_character_inverse_test {X : Type*} [Fintype X]
    (φ : X → ℤ) (f : X → ℝ) (ε : ℝ)
    (h : ∀ χ : AddChar ℤ Circle,
      ‖∑ x : X, (f x : ℂ) * conj (χ (φ x) : ℂ)‖ ≤ ε) (α : ℝ) :
    ‖∑ x : X, (f x : ℂ) * unitCharacter ((φ x : ℝ) * α)‖ ≤ ε := by
  have hα := h ((integerCircleCharacter α)⁻¹)
  simpa only [AddChar.inv_apply', Circle.coe_inv_eq_conj, starRingEnd_self_apply,
    integerCircleCharacter_coe] using hα

end Erdos335.IntermediateScale
