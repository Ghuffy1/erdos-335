import Erdos335.IntegerCircleCharacters
import Erdos335.FiniteFourier

/-!
# Real frequencies for finite-group characters pulled back to the integers
-/

set_option autoImplicit false

open scoped ComplexConjugate

namespace Erdos335.IntermediateScale

theorem finite_character_integer_frequency
    {G : Type*} [AddCommGroup G] [Fintype G]
    (χ : AddChar G ℂ) (h : ℤ →+ G) :
    ∃ β : ℝ, ∀ n : ℤ, conj (χ (h n)) = unitCharacter ((n : ℝ) * β) := by
  let ψ : AddChar ℤ Circle :=
    (((AddChar.circleEquivComplex).symm χ).compAddMonoidHom h)⁻¹
  obtain ⟨β, hβ⟩ := integerCircleCharacter_representation ψ
  refine ⟨β, fun n => ?_⟩
  rw [← hβ n]
  simp only [ψ, AddChar.inv_apply', Circle.coe_inv_eq_conj, AddChar.compAddMonoidHom_apply]
  rfl

end Erdos335.IntermediateScale
