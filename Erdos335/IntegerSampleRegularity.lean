import Erdos335.FiniteCharacterRegularity
import Erdos335.IntegerCircleCharacters

/-!
# Real-frequency regularity on finite samples of the integers
-/

set_option autoImplicit false

open Finset
open scoped BigOperators Classical

universe u

namespace Erdos335.IntermediateScale

theorem integer_sample_regularity (ε : ℝ) (hε : 0 < ε) :
    ∃ L : ℕ, 0 < L ∧
      ∀ (X : Type u) [Fintype X] [Nonempty X] (φ : X → ℤ) (f : X → ℝ),
        (∀ x, f x ∈ Set.Icc (0 : ℝ) 1) →
        ∃ (s : X → ℝ) (α : Fin L → ℝ) (a : Fin L → ℂ),
          (∀ x, s x ∈ Set.Icc (0 : ℝ) 1) ∧
          (∑ x : X, s x) = ∑ x : X, f x ∧
          (∑ x : X, s x * (f x - s x)) = 0 ∧
          (∀ j, ‖a j‖ ≤ 1) ∧
          (∀ β : ℝ,
            ‖∑ x : X, ((f x - s x : ℝ) : ℂ) * unitCharacter ((φ x : ℝ) * β)‖ ≤
              ε * Fintype.card X) ∧
          (∑ x : X, ‖(s x : ℂ) - ∑ j, a j * unitCharacter ((φ x : ℝ) * α j)‖ ^ 2) /
            Fintype.card X ≤ ε ^ 2 := by
  obtain ⟨L, hL, hreg⟩ := finite_character_regularity.{u, 0} ε hε
  refine ⟨L, hL, ?_⟩
  intro X _ _ φ f hf
  obtain ⟨s, ψ, a, hs, hsum, horth, ha, htest, happrox⟩ := hreg X ℤ φ f hf
  choose α hα using (fun j => integerCircleCharacter_representation (ψ j))
  refine ⟨s, α, a, hs, hsum, horth, ha, ?_, ?_⟩
  · intro β
    exact integer_character_inverse_test φ (fun x => f x - s x) _ htest β
  · simpa only [hα] using happrox

end Erdos335.IntermediateScale
