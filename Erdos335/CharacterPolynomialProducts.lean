import Erdos335.CircleCellPolynomials
import Erdos335.IndexedPolynomialPadding

/-!
# Expanding products of one-dimensional character polynomials
-/

set_option autoImplicit false

open Finset
open scoped BigOperators Classical

namespace Erdos335.IntermediateScale

variable {G I : Type*} [AddCommGroup G] [Fintype I]

noncomputable def productCharacter (χ : I → AddChar G Circle) (n : I → ℤ) : AddChar G ℂ :=
  Circle.coeHom.compAddChar (∏ i : I, (χ i) ^ (n i))

theorem productCharacter_apply (χ : I → AddChar G Circle) (n : I → ℤ) (x : G) :
    productCharacter χ n x = ∏ i : I, ((χ i x : Circle) : ℂ) ^ (n i) := by
  change Circle.coeHom ((∏ i : I, (χ i) ^ n i) x) = _
  rw [AddChar.prod_apply, map_prod]
  apply prod_congr rfl
  intro i hi
  change (((χ i) ^ n i) x : ℂ) = _
  rw [AddChar.zpow_apply, Circle.coe_zpow]

theorem character_polynomial_product (χ : I → AddChar G Circle)
    (S : I → Finset ℤ) (w : I → ℤ → ℂ) (x : G) :
    (∏ i : I, ∑ n ∈ S i, w i n * ((χ i x : Circle) : ℂ) ^ n) =
      ∑ t : (∀ i, S i), (∏ i : I, w i (t i)) * productCharacter χ (fun i => (t i).val) x := by
  have hsum (i : I) : (∑ n ∈ S i, w i n * ((χ i x : Circle) : ℂ) ^ n) =
      ∑ n : S i, w i n * ((χ i x : Circle) : ℂ) ^ (n.val) :=
    (Finset.sum_coe_sort (S i) _).symm
  simp_rw [hsum]
  rw [Fintype.prod_sum]
  apply sum_congr rfl
  intro t ht
  rw [prod_mul_distrib, productCharacter_apply]

theorem polynomial_product_card_bound (S : I → Finset ℤ) (K : ℕ)
    (hS : ∀ i, (S i).card ≤ K) : Fintype.card (∀ i, S i) ≤ K ^ Fintype.card I := by
  rw [Fintype.card_pi]
  calc
    _ = ∏ i : I, (S i).card := by simp only [Fintype.card_coe]
    _ ≤ ∏ _i : I, K := prod_le_prod fun i _ => hS i
    _ = _ := by simp

theorem polynomial_product_coefficient_bound (S : I → Finset ℤ) (w : I → ℤ → ℂ)
    (K : ℕ) (hw : ∀ i n, n ∈ S i → ‖w i n‖ ≤ K) (t : ∀ i, S i) :
    ‖∏ i : I, w i (t i)‖ ≤ (K : ℝ) ^ Fintype.card I := by
  rw [norm_prod]
  calc
    _ ≤ ∏ _i : I, (K : ℝ) := prod_le_prod₀ (fun _ _ => norm_nonneg _) (fun i _ => hw i (t i) (t i).property)
    _ = _ := by simp

end Erdos335.IntermediateScale
