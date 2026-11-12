import Erdos335.SoftUnitCharacterPolynomials

/-!
# Uniform complexity bounds for character approximations of finite factors
-/

set_option autoImplicit false

open Finset
open scoped BigOperators Classical

namespace Erdos335.IntermediateScale

theorem quantized_label_card {I : Type*} [Fintype I] (N : ℕ) :
    Fintype.card (I → Fin (2 * N + 1)) = (2 * N + 1) ^ Fintype.card I := by
  simp only [Fintype.card_eq_nat_card, Nat.card_fun, Nat.card_fin]

theorem bounded_softCharacter_polynomial_approximation
    {G I : Type*} [AddCommGroup G] [Fintype I]
    (N M D K : ℕ) (hK : 0 < K) (hcard : Fintype.card I ≤ D)
    (tags : I → Bool × Fin M) (χ : I → AddChar G Circle)
    (c : (I → Fin (2 * N + 1)) → ℝ) (hc : ∀ r, c r ∈ Set.Icc (0 : ℝ) 1)
    (η : ℝ) (hη : 0 ≤ η) (hη1 : η ≤ 1)
    (S : (Bool × Fin M × Fin (2 * N + 1)) → Finset ℤ)
    (w : (Bool × Fin M × Fin (2 * N + 1)) → ℤ → ℂ)
    (hS : ∀ tag, (S tag).card ≤ K)
    (hw : ∀ tag n, n ∈ S tag → ‖w tag n‖ ≤ K)
    (happrox : ∀ tag z, ‖circleCell N M tag z - ∑ n ∈ S tag, w tag n * (z : ℂ) ^ n‖ ≤ η) :
    ∃ (ψ : Fin ((2 * N + 1) ^ D * K ^ D * K ^ D) → AddChar G Circle)
      (a : Fin ((2 * N + 1) ^ D * K ^ D * K ^ D) → ℂ),
      (∀ j, ‖a j‖ ≤ 1) ∧ ∀ x,
      ‖(softCharacterModel N M tags χ c x : ℂ) - ∑ j, a j * (ψ j x : ℂ)‖ ≤
        ((2 * N + 1 : ℕ) : ℝ) ^ D * (D * η * 2 ^ D) := by
  obtain ⟨ψ, a, ha, hpoly⟩ := softCharacterModel_unit_polynomial_approximation
    N M K hK tags χ c hc η hη hη1 S w hS hw happrox
  have hcN : Fintype.card (I → Fin (2 * N + 1)) ≤ (2 * N + 1) ^ D := by
    rw [quantized_label_card]
    exact Nat.pow_le_pow_right (by omega) hcard
  have hcK : K ^ Fintype.card I ≤ K ^ D := Nat.pow_le_pow_right hK hcard
  have hlength : Fintype.card (Fin (Fintype.card (I → Fin (2 * N + 1)) *
      K ^ Fintype.card I * K ^ Fintype.card I)) ≤ (2 * N + 1) ^ D * K ^ D * K ^ D := by
    rw [Fintype.card_fin]
    exact Nat.mul_le_mul (Nat.mul_le_mul hcN hcK) hcK
  obtain ⟨ψ', a', ha', heq⟩ := pad_circle_character_sum ψ a ha
    ((2 * N + 1) ^ D * K ^ D * K ^ D) hlength
  refine ⟨ψ', a', ha', fun x => ?_⟩
  rw [heq]
  apply (hpoly x).trans
  have hcNr : (Fintype.card (I → Fin (2 * N + 1)) : ℝ) ≤ ((2 * N + 1 : ℕ) : ℝ) ^ D := by
    exact_mod_cast hcN
  have hcIr : (Fintype.card I : ℝ) ≤ D := by exact_mod_cast hcard
  have hc2 : (2 : ℝ) ^ Fintype.card I ≤ 2 ^ D := pow_le_pow_right₀ (by norm_num) hcard
  gcongr

end Erdos335.IntermediateScale
