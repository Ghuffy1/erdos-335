import Erdos335.FiniteConditionalAverages

/-!
# Energy increase under finite partition refinement
-/

set_option autoImplicit false

open Finset
open scoped BigOperators Classical

namespace Erdos335.IntermediateScale

variable {G K L : Type*} [Fintype G] [Fintype K] [Fintype L]
  [DecidableEq K] [DecidableEq L]

omit [Fintype K] in
theorem refinement_residual_orthogonal (π : G → K) (ρ : G → L) (σ : L → K)
    (hπ : ∀ x, π x = σ (ρ x)) (f : G → ℝ) :
    ∑ x : G, finiteConditionalMean π f x * (f x - finiteConditionalMean ρ f x) = 0 := by
  have h := finiteConditionalMean_orthogonal ρ f (fun l => finiteFiberMean π f (σ l))
  simpa only [finiteConditionalMean, hπ] using h

theorem refinement_increment_orthogonal (π : G → K) (ρ : G → L) (σ : L → K)
    (hπ : ∀ x, π x = σ (ρ x)) (f : G → ℝ) :
    ∑ x : G, finiteConditionalMean π f x *
      (finiteConditionalMean ρ f x - finiteConditionalMean π f x) = 0 := by
  have hsmall := finiteConditionalMean_orthogonal π f (finiteFiberMean π f)
  have hlarge := refinement_residual_orthogonal π ρ σ hπ f
  change (∑ x : G, finiteConditionalMean π f x * (f x - finiteConditionalMean π f x)) = 0 at hsmall
  calc
    _ = (∑ x : G, finiteConditionalMean π f x * (f x - finiteConditionalMean π f x)) -
        ∑ x : G, finiteConditionalMean π f x * (f x - finiteConditionalMean ρ f x) := by
      rw [← sum_sub_distrib]
      apply sum_congr rfl
      intro x hx
      ring
    _ = 0 := by rw [hsmall, hlarge]; ring

theorem refinement_energy_identity (π : G → K) (ρ : G → L) (σ : L → K)
    (hπ : ∀ x, π x = σ (ρ x)) (f : G → ℝ) :
    (∑ x : G, finiteConditionalMean ρ f x ^ 2) =
      (∑ x : G, finiteConditionalMean π f x ^ 2) +
      ∑ x : G, (finiteConditionalMean ρ f x - finiteConditionalMean π f x) ^ 2 := by
  have h := refinement_increment_orthogonal π ρ σ hπ f
  calc
    _ = ∑ x : G, (finiteConditionalMean π f x ^ 2 +
        (finiteConditionalMean ρ f x - finiteConditionalMean π f x) ^ 2 +
        2 * (finiteConditionalMean π f x *
          (finiteConditionalMean ρ f x - finiteConditionalMean π f x))) := by
      apply sum_congr rfl
      intro x hx
      ring
    _ = _ := by rw [sum_add_distrib, sum_add_distrib, ← mul_sum, h]; ring

theorem refinement_energy_mono (π : G → K) (ρ : G → L) (σ : L → K)
    (hπ : ∀ x, π x = σ (ρ x)) (f : G → ℝ) :
    (∑ x : G, finiteConditionalMean π f x ^ 2) ≤
      ∑ x : G, finiteConditionalMean ρ f x ^ 2 := by
  rw [refinement_energy_identity π ρ σ hπ f]
  exact le_add_of_nonneg_right (sum_nonneg fun _ _ => sq_nonneg _)

end Erdos335.IntermediateScale
