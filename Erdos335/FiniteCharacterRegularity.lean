import Erdos335.ConditionalCharacterApproximation
import Erdos335.CharacterRegularityParameters

/-!
# Uniform character regularity on finite samples

The sample map may take values in an infinite group. In particular, integer
intervals can be tested against all circle-valued characters of the integers.
-/

set_option autoImplicit false

open Finset
open scoped BigOperators Classical ComplexConjugate

universe u v

namespace Erdos335.IntermediateScale

theorem finite_character_regularity (ε : ℝ) (hε : 0 < ε) :
    ∃ L : ℕ, 0 < L ∧
      ∀ (X : Type u) (G : Type v) [Fintype X] [Nonempty X] [AddCommGroup G]
        (φ : X → G) (f : X → ℝ),
        (∀ x, f x ∈ Set.Icc (0 : ℝ) 1) →
        ∃ (s : X → ℝ) (ψ : Fin L → AddChar G Circle) (a : Fin L → ℂ),
          (∀ x, s x ∈ Set.Icc (0 : ℝ) 1) ∧
          (∑ x : X, s x) = ∑ x : X, f x ∧
          (∑ x : X, s x * (f x - s x)) = 0 ∧
          (∀ j, ‖a j‖ ≤ 1) ∧
          (∀ χ : AddChar G Circle,
            ‖∑ x : X, ((f x - s x : ℝ) : ℂ) * conj (χ (φ x) : ℂ)‖ ≤
              ε * Fintype.card X) ∧
          (∑ x : X, ‖(s x : ℂ) - ∑ j, a j * (ψ j (φ x) : ℂ)‖ ^ 2) /
            Fintype.card X ≤ ε ^ 2 := by
  obtain ⟨τ, N, D, M, hτ, hτε, hN, hM, hthreshold, hD, hbudget⟩ :=
    exists_continuous_model_parameters ε hε
  obtain ⟨K, η, T, w, hK, hη, hη1, hpolybudget, hT, hw, happrox⟩ :=
    exists_cell_polynomial_parameters N M D (ε / 2) (by positivity)
  let L := (2 * N + 1) ^ D * K ^ D * K ^ D
  refine ⟨L, by dsimp [L]; positivity, ?_⟩
  intro X G _ _ _ φ f hf
  obtain ⟨S, hcard, hS, hboundary, htests⟩ := boundary_avoiding_test_regularity
    f hf (pulledCharacterTests φ) (pulledCharacterTests_bound φ)
    τ N D M hN hM hthreshold hD
  obtain ⟨ψ, a, ha, herror⟩ := conditional_character_approximation
    φ f hf N M D K hN hM hK S hcard hS hboundary (ε / 2) η
    (by positivity) hη.le hη1 hbudget hpolybudget T w hT hw happrox
  let s := finiteConditionalMean (testPartition N S) f
  refine ⟨s, ψ, a, finiteConditionalMean_bounds _ f hf,
    finiteConditionalMean_sum _ f, ?_, ha, ?_, ?_⟩
  · exact finiteConditionalMean_orthogonal (testPartition N S) f
      (finiteFiberMean (testPartition N S) f)
  · intro χ
    apply (pulled_character_sum_norm_le φ (fun x => f x - s x) χ τ htests).trans
    have hcardpos : (0 : ℝ) ≤ Fintype.card X := Nat.cast_nonneg _
    nlinarith
  · change (∑ x : X, ‖(finiteConditionalMean (testPartition N S) f x : ℂ) -
        ∑ j, a j * (ψ j (φ x) : ℂ)‖ ^ 2) / Fintype.card X ≤ ε ^ 2
    nlinarith

end Erdos335.IntermediateScale
