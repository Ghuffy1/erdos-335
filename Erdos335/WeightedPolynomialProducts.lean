import Erdos335.CharacterPolynomialProducts

/-!
# Bounded indexed expansion of a finite weighted polynomial model
-/

set_option autoImplicit false

open Finset
open scoped BigOperators Classical

namespace Erdos335.IntermediateScale

variable {G I R : Type*} [AddCommGroup G] [Fintype I] [Fintype R]

theorem weighted_polynomial_product_expansion (χ : I → AddChar G Circle)
    (S : R → I → Finset ℤ) (w : R → I → ℤ → ℂ) (c : R → ℂ) (x : G) :
    (∑ r : R, c r * ∏ i : I, ∑ n ∈ S r i, w r i n * ((χ i x : Circle) : ℂ) ^ n) =
      ∑ t : (Σ r : R, ∀ i, S r i),
        (c t.1 * ∏ i : I, w t.1 i (t.2 i)) * productCharacter χ (fun i => (t.2 i).val) x := by
  rw [Fintype.sum_sigma]
  apply sum_congr rfl
  intro r hr
  rw [character_polynomial_product, mul_sum]
  apply sum_congr rfl
  intro t ht
  ring

theorem weighted_polynomial_product_card_bound (S : R → I → Finset ℤ) (K : ℕ)
    (hS : ∀ r i, (S r i).card ≤ K) :
    Fintype.card (Σ r : R, ∀ i, S r i) ≤ Fintype.card R * K ^ Fintype.card I := by
  rw [Fintype.card_sigma]
  calc
    _ ≤ ∑ _r : R, K ^ Fintype.card I :=
      sum_le_sum fun r _ => polynomial_product_card_bound (S r) K (hS r)
    _ = _ := by simp

theorem weighted_polynomial_product_coefficient_bound
    (S : R → I → Finset ℤ) (w : R → I → ℤ → ℂ) (c : R → ℂ)
    (K : ℕ) (hc : ∀ r, ‖c r‖ ≤ 1) (hw : ∀ r i n, n ∈ S r i → ‖w r i n‖ ≤ K)
    (t : Σ r : R, ∀ i, S r i) :
    ‖c t.1 * ∏ i : I, w t.1 i (t.2 i)‖ ≤ (K : ℝ) ^ Fintype.card I := by
  rw [norm_mul]
  calc
    _ ≤ 1 * ((K : ℝ) ^ Fintype.card I) :=
      mul_le_mul (hc t.1) (polynomial_product_coefficient_bound (S t.1) (w t.1) K (hw t.1) t.2)
        (norm_nonneg _) zero_le_one
    _ = _ := one_mul _

theorem pad_weighted_polynomial_products
    (χ : I → AddChar G Circle) (S : R → I → Finset ℤ)
    (w : R → I → ℤ → ℂ) (c : R → ℂ) (K M : ℕ) (hK : 0 < K)
    (hc : ∀ r, ‖c r‖ ≤ 1) (hS : ∀ r i, (S r i).card ≤ K)
    (hw : ∀ r i n, n ∈ S r i → ‖w r i n‖ ≤ K)
    (hM : Fintype.card R * K ^ Fintype.card I * K ^ Fintype.card I ≤ M) :
    ∃ (ψ : Fin M → AddChar G ℂ) (a : Fin M → ℂ), (∀ j, ‖a j‖ ≤ 1) ∧
      ∀ x, (∑ j : Fin M, a j * ψ j x) =
        ∑ r : R, c r * ∏ i : I, ∑ n ∈ S r i, w r i n * ((χ i x : Circle) : ℂ) ^ n := by
  let T := Σ r : R, ∀ i, S r i
  let ψ : T → AddChar G ℂ := fun t => productCharacter χ (fun i => (t.2 i).val)
  let a : T → ℂ := fun t => c t.1 * ∏ i : I, w t.1 i (t.2 i)
  have hbound (t : T) : ‖a t‖ ≤ (K ^ Fintype.card I : ℕ) := by
    simpa only [Nat.cast_pow] using weighted_polynomial_product_coefficient_bound S w c K hc hw t
  have hcount : Fintype.card T * K ^ Fintype.card I ≤ M :=
    (Nat.mul_le_mul_right _ (weighted_polynomial_product_card_bound S K hS)).trans hM
  obtain ⟨φ, b, hb, heq⟩ := split_and_pad_character_sum ψ a (K ^ Fintype.card I) M
    (pow_pos hK _) hbound hcount
  refine ⟨φ, b, hb, ?_⟩
  intro x
  rw [heq]
  exact (weighted_polynomial_product_expansion χ S w c x).symm

end Erdos335.IntermediateScale
