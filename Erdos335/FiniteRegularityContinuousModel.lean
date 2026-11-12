import Erdos335.SoftConditionalApproximation
import Erdos335.BoundaryAvoidingRegularity

/-!
# A continuous model for the selected quantized factor
-/

set_option autoImplicit false

open Finset
open scoped BigOperators Classical

namespace Erdos335.IntermediateScale

theorem finite_factor_soft_model_error
    {G : Type*} [Fintype G] [Nonempty G]
    (f : G → ℝ) (hf : ∀ x, f x ∈ Set.Icc (0 : ℝ) 1)
    (N M : ℕ) (hM : 0 < M) (S : Finset (G → ℝ))
    (hS : ∀ u ∈ S, ∀ x, |u x| ≤ 1)
    (hboundary : ∀ u ∈ S,
      M * (univ.filter (fun x : G => nearQuantizationBoundary N M (u x))).card ≤ Fintype.card G) :
    (∑ x : G, (softPartitionModel N M (finiteFiberMean (testPartition N S) f)
        (fun u : S => u.val x) - finiteConditionalMean (testPartition N S) f x) ^ 2) /
      Fintype.card G ≤
      (S.card : ℝ) / M * (((2 * N + 1 : ℕ) : ℝ) ^ S.card + 1) ^ 2 := by
  have hmodel := softPartitionModel_normalized_error N M hM
    (finiteFiberMean (testPartition N S) f)
    (finiteFiberMean_bounds (testPartition N S) f hf)
    (fun x u => u.val x) (fun x u => hS u.val u.property x)
    (fun u => hboundary u.val u.property)
  have hlabel (x : G) : (fun u : S => quantizedIndex N (u.val x)) = testPartition N S x := rfl
  simp_rw [hlabel] at hmodel
  simp only [Fintype.card_eq_nat_card, Nat.card_fun, Nat.card_fin, Nat.card_eq_finsetCard,
    Nat.cast_pow] at hmodel
  simp only [Nat.card_eq_fintype_card] at hmodel
  unfold finiteConditionalMean
  exact hmodel

theorem finite_factor_soft_model_error_of_card_bound
    {G : Type*} [Fintype G] [Nonempty G]
    (f : G → ℝ) (hf : ∀ x, f x ∈ Set.Icc (0 : ℝ) 1)
    (N M D : ℕ) (hM : 0 < M) (S : Finset (G → ℝ)) (hcard : S.card ≤ D)
    (hS : ∀ u ∈ S, ∀ x, |u x| ≤ 1)
    (hboundary : ∀ u ∈ S,
      M * (univ.filter (fun x : G => nearQuantizationBoundary N M (u x))).card ≤ Fintype.card G)
    (δ : ℝ) (hbudget : (D : ℝ) * (((2 * N + 1 : ℕ) : ℝ) ^ D + 1) ^ 2 ≤ δ ^ 2 * M) :
    (∑ x : G, (softPartitionModel N M (finiteFiberMean (testPartition N S) f)
        (fun u : S => u.val x) - finiteConditionalMean (testPartition N S) f x) ^ 2) /
      Fintype.card G ≤ δ ^ 2 := by
  have hMr : (0 : ℝ) < M := by exact_mod_cast hM
  have hc : (S.card : ℝ) ≤ D := by exact_mod_cast hcard
  have hp : (((2 * N + 1 : ℕ) : ℝ) ^ S.card) ≤ ((2 * N + 1 : ℕ) : ℝ) ^ D :=
    pow_le_pow_right₀ (by exact_mod_cast (show 1 ≤ 2 * N + 1 by omega)) hcard
  apply (finite_factor_soft_model_error f hf N M hM S hS hboundary).trans
  calc
    _ ≤ (D : ℝ) / M * (((2 * N + 1 : ℕ) : ℝ) ^ D + 1) ^ 2 := by gcongr
    _ = ((D : ℝ) * (((2 * N + 1 : ℕ) : ℝ) ^ D + 1) ^ 2) / M := by ring
    _ ≤ δ ^ 2 := (div_le_iff₀ hMr).mpr hbudget

end Erdos335.IntermediateScale
