import Erdos335.FiniteSpectralApproximation

/-!
# Padding indexed character sums with uniformly bounded coefficients
-/

set_option autoImplicit false

open Finset
open scoped BigOperators Classical

namespace Erdos335.IntermediateScale

theorem pad_indexed_character_sum {G I : Type*} [AddCommGroup G] [Fintype I]
    (χ : I → AddChar G ℂ) (w : I → ℂ) (hw : ∀ i, ‖w i‖ ≤ 1)
    (M : ℕ) (hM : Fintype.card I ≤ M) :
    ∃ (ψ : Fin M → AddChar G ℂ) (a : Fin M → ℂ),
      (∀ j, ‖a j‖ ≤ 1) ∧ ∀ x, (∑ j : Fin M, a j * ψ j x) = ∑ i : I, w i * χ i x := by
  obtain ⟨e⟩ := Function.Embedding.nonempty_of_card_le
    (show Fintype.card I ≤ Fintype.card (Fin M) by simpa using hM)
  let ψ : Fin M → AddChar G ℂ := Function.extend e χ (fun _ => 0)
  let a : Fin M → ℂ := Function.extend e w (fun _ => 0)
  have hψ (i : I) : ψ (e i) = χ i := e.injective.extend_apply _ _ i
  have ha (i : I) : a (e i) = w i := e.injective.extend_apply _ _ i
  have hzero (j : Fin M) (hj : j ∉ Set.range e) : a j = 0 := Function.extend_apply' _ _ j hj
  refine ⟨ψ, a, ?_, ?_⟩
  · intro j
    by_cases hj : j ∈ Set.range e
    · obtain ⟨i, rfl⟩ := hj
      rw [ha]
      exact hw i
    · rw [hzero j hj, norm_zero]
      norm_num
  · intro x
    symm
    apply Fintype.sum_of_injective e e.injective
    · intro j hj
      rw [hzero j hj, zero_mul]
    · intro i
      rw [ha, hψ]

theorem split_and_pad_character_sum {G I : Type*} [AddCommGroup G] [Fintype I]
    (χ : I → AddChar G ℂ) (w : I → ℂ) (B M : ℕ) (hB : 0 < B)
    (hw : ∀ i, ‖w i‖ ≤ B) (hM : Fintype.card I * B ≤ M) :
    ∃ (ψ : Fin M → AddChar G ℂ) (a : Fin M → ℂ),
      (∀ j, ‖a j‖ ≤ 1) ∧ ∀ x, (∑ j : Fin M, a j * ψ j x) = ∑ i : I, w i * χ i x := by
  let χ' : I × Fin B → AddChar G ℂ := fun p => χ p.1
  let w' : I × Fin B → ℂ := fun p => w p.1 / (B : ℂ)
  have hBpos : (0 : ℝ) < B := by exact_mod_cast hB
  have hBn : (B : ℂ) ≠ 0 := by exact_mod_cast hB.ne'
  have hw' (p : I × Fin B) : ‖w' p‖ ≤ 1 := by
    dsimp [w']
    rw [norm_div, Complex.norm_natCast]
    exact (div_le_one hBpos).mpr (hw p.1)
  have hcard : Fintype.card (I × Fin B) ≤ M := by
    simpa only [Fintype.card_prod, Fintype.card_fin] using hM
  obtain ⟨ψ, a, ha, hsum⟩ := pad_indexed_character_sum χ' w' hw' M hcard
  refine ⟨ψ, a, ha, ?_⟩
  intro x
  rw [hsum]
  rw [Fintype.sum_prod_type]
  apply sum_congr rfl
  intro i hi
  simp only [χ', w', sum_const, card_univ, Fintype.card_fin, nsmul_eq_mul]
  field_simp

end Erdos335.IntermediateScale
