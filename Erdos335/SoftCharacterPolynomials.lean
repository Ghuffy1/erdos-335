import Erdos335.WeightedPolynomialProducts
import Erdos335.WeightedProductApproximation
import Erdos335.SoftPartitionApproximation

/-!
# Bounded character polynomial approximants for continuous finite-factor models
-/

set_option autoImplicit false

open Finset
open scoped BigOperators Classical

namespace Erdos335.IntermediateScale

variable {G I : Type*} [AddCommGroup G] [Fintype I]

noncomputable def softCharacterModel (N M : ℕ) (tags : I → Bool × Fin M)
    (χ : I → AddChar G Circle) (c : (I → Fin (2 * N + 1)) → ℝ) (x : G) : ℝ :=
  softPartitionModel N M c (fun i => shiftedTest N M (tags i).2
    (circleCoordinate (tags i).1 (χ i x)))

theorem softCharacterModel_eq (N M : ℕ) (tags : I → Bool × Fin M)
    (χ : I → AddChar G Circle) (c : (I → Fin (2 * N + 1)) → ℝ) (x : G) :
    (softCharacterModel N M tags χ c x : ℂ) =
      ∑ r : I → Fin (2 * N + 1), (c r : ℂ) *
        ∏ i : I, circleCell N M ((tags i).1, (tags i).2, r i) (χ i x) := by
  simp [softCharacterModel, softPartitionModel, softPattern, circleCell]

theorem softCharacterModel_polynomial_approximation
    (N M K : ℕ) (hK : 0 < K) (tags : I → Bool × Fin M)
    (χ : I → AddChar G Circle) (c : (I → Fin (2 * N + 1)) → ℝ)
    (hc : ∀ r, c r ∈ Set.Icc (0 : ℝ) 1)
    (η : ℝ) (hη : 0 ≤ η) (hη1 : η ≤ 1)
    (S : (Bool × Fin M × Fin (2 * N + 1)) → Finset ℤ)
    (w : (Bool × Fin M × Fin (2 * N + 1)) → ℤ → ℂ)
    (hS : ∀ tag, (S tag).card ≤ K)
    (hw : ∀ tag n, n ∈ S tag → ‖w tag n‖ ≤ K)
    (happrox : ∀ tag z, ‖circleCell N M tag z - ∑ n ∈ S tag, w tag n * (z : ℂ) ^ n‖ ≤ η) :
    ∃ (ψ : Fin (Fintype.card (I → Fin (2 * N + 1)) * K ^ Fintype.card I * K ^ Fintype.card I) →
        AddChar G ℂ)
      (a : Fin (Fintype.card (I → Fin (2 * N + 1)) * K ^ Fintype.card I * K ^ Fintype.card I) → ℂ),
      (∀ j, ‖a j‖ ≤ 1) ∧ ∀ x,
      ‖(softCharacterModel N M tags χ c x : ℂ) - ∑ j, a j * ψ j x‖ ≤
        Fintype.card (I → Fin (2 * N + 1)) * (Fintype.card I * η * 2 ^ Fintype.card I) := by
  let R := I → Fin (2 * N + 1)
  let tag := fun (r : R) (i : I) => ((tags i).1, (tags i).2, r i)
  let A := fun (r : R) (i : I) => S (tag r i)
  let W := fun (r : R) (i : I) => w (tag r i)
  let C := fun r : R => (c r : ℂ)
  have hC (r : R) : ‖C r‖ ≤ 1 := by
    simpa only [C, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (hc r).1] using (hc r).2
  obtain ⟨ψ, a, ha, heq⟩ := pad_weighted_polynomial_products χ A W C K
    (Fintype.card R * K ^ Fintype.card I * K ^ Fintype.card I) hK hC
    (fun r i => hS (tag r i)) (fun r i n hn => hw (tag r i) n hn) (by rfl)
  refine ⟨ψ, a, ha, ?_⟩
  intro x
  rw [heq, softCharacterModel_eq]
  apply weighted_product_approximation
    (fun r i => circleCell N M (tag r i) (χ i x))
    (fun r i => ∑ n ∈ A r i, W r i n * ((χ i x : Circle) : ℂ) ^ n)
    C η hη hη1
  · exact fun r i => circleCell_norm_le_one N M (tag r i) (χ i x)
  · exact hC
  · exact fun r i => happrox (tag r i) (χ i x)

end Erdos335.IntermediateScale
