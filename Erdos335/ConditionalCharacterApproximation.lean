import Erdos335.PulledCharacterTests
import Erdos335.BoundedSoftCharacterPolynomials
import Erdos335.FiniteRegularityContinuousModel
import Erdos335.FiniteL2PolynomialError

/-!
# Character polynomial approximation of boundary-regular conditional means
-/

set_option autoImplicit false

open Finset
open scoped BigOperators Classical

namespace Erdos335.IntermediateScale

theorem conditional_character_approximation
    {X G : Type*} [Fintype X] [Nonempty X] [AddCommGroup G]
    (φ : X → G) (f : X → ℝ) (hf : ∀ x, f x ∈ Set.Icc (0 : ℝ) 1)
    (N M D K : ℕ) (hN : 2 ≤ N) (hM : 0 < M) (hK : 0 < K)
    (S : Finset (X → ℝ)) (hcard : S.card ≤ D)
    (hS : ∀ v ∈ S, ∃ u ∈ pulledCharacterTests φ,
      ∃ j : Fin M, v = fun x => shiftedTest N M j (u x))
    (hboundary : ∀ u ∈ S,
      M * (univ.filter (fun x : X => nearQuantizationBoundary N M (u x))).card ≤ Fintype.card X)
    (δ η : ℝ) (hδ : 0 ≤ δ) (hη : 0 ≤ η) (hη1 : η ≤ 1)
    (hbudget : (D : ℝ) * (((2 * N + 1 : ℕ) : ℝ) ^ D + 1) ^ 2 ≤ δ ^ 2 * M)
    (hpolybudget : ((2 * N + 1 : ℕ) : ℝ) ^ D * (D * η * 2 ^ D) ≤ δ)
    (T : (Bool × Fin M × Fin (2 * N + 1)) → Finset ℤ)
    (w : (Bool × Fin M × Fin (2 * N + 1)) → ℤ → ℂ)
    (hT : ∀ tag, (T tag).card ≤ K)
    (hw : ∀ tag n, n ∈ T tag → ‖w tag n‖ ≤ K)
    (happrox : ∀ tag z, ‖circleCell N M tag z - ∑ n ∈ T tag, w tag n * (z : ℂ) ^ n‖ ≤ η) :
    ∃ (ψ : Fin ((2 * N + 1) ^ D * K ^ D * K ^ D) → AddChar G Circle)
      (a : Fin ((2 * N + 1) ^ D * K ^ D * K ^ D) → ℂ),
      (∀ j, ‖a j‖ ≤ 1) ∧
      (∑ x : X, ‖(finiteConditionalMean (testPartition N S) f x : ℂ) -
        ∑ j, a j * (ψ j (φ x) : ℂ)‖ ^ 2) / Fintype.card X ≤ 4 * δ ^ 2 := by
  obtain ⟨χ, tags, hcoordinates⟩ := selected_character_factor φ N M S hS
  let c := finiteFiberMean (testPartition N S) f
  have hc : ∀ r, c r ∈ Set.Icc (0 : ℝ) 1 := finiteFiberMean_bounds _ f hf
  have hcard' : Fintype.card S ≤ D := by simpa only [Fintype.card_coe] using hcard
  obtain ⟨ψ, a, ha, hpoly⟩ := bounded_softCharacter_polynomial_approximation
    N M D K hK hcard' tags χ c hc η hη hη1 T w hT hw happrox
  have hbounded : ∀ u ∈ S, ∀ x, |u x| ≤ 1 := by
    intro v hv x
    obtain ⟨u, hu, j, rfl⟩ := hS v hv
    exact shiftedTest_bound N M hN hM j (u x) (pulledCharacterTests_bound φ u hu x)
  have hsoft := finite_factor_soft_model_error_of_card_bound
    f hf N M D hM S hcard hbounded hboundary δ hbudget
  have hmodel (x : X) : softCharacterModel N M tags χ c (φ x) =
      softPartitionModel N M c (fun v : S => v.val x) := by
    unfold softCharacterModel
    congr 1
    funext v
    exact (hcoordinates v x).symm
  have herror := finite_l2_uniform_triangle
    (finiteConditionalMean (testPartition N S) f)
    (fun x => softPartitionModel N M c (fun v : S => v.val x))
    (fun x => ∑ j, a j * (ψ j (φ x) : ℂ)) δ δ hδ hsoft
    (fun x => by simpa only [hmodel] using (hpoly (φ x)).trans hpolybudget)
  refine ⟨ψ, a, ha, ?_⟩
  nlinarith

end Erdos335.IntermediateScale
