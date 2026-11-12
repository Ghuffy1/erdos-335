import Erdos335.FiniteFourierConvolution
import Mathlib.Data.Fintype.EquivFin

/-!
# Uniform finite spectral polynomials

A fixed number of characters suffices to approximate normalized convolution
to any prescribed mean-square accuracy. The coefficients stay in the unit
disk, uniformly in the finite ambient group.
-/

set_option autoImplicit false

open Finset RCLike
open scoped BigOperators

namespace Erdos335.FiniteFourier

variable {G : Type*} [AddCommGroup G] [Fintype G]

theorem coefficient_norm_le_one (f : G → ℂ) (hf : ∀ x, ‖f x‖ ≤ 1) (χ : AddChar G ℂ) :
    ‖coefficient f χ‖ ≤ 1 := by
  have hterm : ‖coefficient f χ‖ ^ 2 ≤ ∑ η : AddChar G ℂ, ‖coefficient f η‖ ^ 2 :=
    Finset.single_le_sum (f := fun η => ‖coefficient f η‖ ^ 2)
      (fun _ _ => sq_nonneg _) (Finset.mem_univ χ)
  rw [parseval] at hterm
  have hbound := hterm.trans (normalized_energy_le_one f hf)
  nlinarith [norm_nonneg (coefficient f χ)]

omit [Fintype G] in
theorem pad_character_polynomial (S : Finset (AddChar G ℂ)) (a : AddChar G ℂ → ℂ)
    (ha : ∀ χ ∈ S, ‖a χ‖ ≤ 1) (M : ℕ) (hM : S.card ≤ M) :
    ∃ (χ : Fin M → AddChar G ℂ) (w : Fin M → ℂ),
      (∀ j, ‖w j‖ ≤ 1) ∧
      (∑ j : Fin M, w j • (χ j : G → ℂ)) = ∑ η ∈ S, a η • (η : G → ℂ) := by
  classical
  obtain ⟨e⟩ := Function.Embedding.nonempty_of_card_le
    (show Fintype.card S ≤ Fintype.card (Fin M) by simpa using hM)
  let χ : Fin M → AddChar G ℂ := Function.extend e (fun η : S => η.val) (fun _ => 0)
  let w : Fin M → ℂ := Function.extend e (fun η : S => a η.val) (fun _ => 0)
  have hχ (η : S) : χ (e η) = η.val := e.injective.extend_apply _ _ η
  have hw (η : S) : w (e η) = a η.val := e.injective.extend_apply _ _ η
  have hzero (j : Fin M) (hj : j ∉ Set.range e) : w j = 0 := by
    exact Function.extend_apply' _ _ j hj
  refine ⟨χ, w, ?_, ?_⟩
  · intro j
    by_cases hj : j ∈ Set.range e
    · obtain ⟨η, rfl⟩ := hj
      rw [hw]
      exact ha η.val η.property
    · rw [hzero j hj, norm_zero]
      norm_num
  · have heq := Fintype.sum_of_injective e e.injective
      (fun η : S => a η.val • (η.val : G → ℂ))
      (fun j : Fin M => w j • (χ j : G → ℂ))
      (fun j hj => by rw [hzero j hj, zero_smul])
      (fun η => by rw [hw, hχ])
    rw [← heq]
    exact Finset.sum_coe_sort S (fun η => a η • (η : G → ℂ))

theorem exists_uniform_spectral_polynomial (f g : G → ℂ)
    (hf : ∀ x, ‖f x‖ ≤ 1) (hg : ∀ x, ‖g x‖ ≤ 1)
    (ε : ℝ) (hε : 0 < ε) (M : ℕ) (hM : 1 / ε ^ 2 ≤ (M : ℝ)) :
    ∃ (χ : Fin M → AddChar G ℂ) (w : Fin M → ℂ),
      (∀ j, ‖w j‖ ≤ 1) ∧
      (Fintype.card G : ℝ)⁻¹ *
        ∑ x : G, ‖convolution f g x - ∑ j : Fin M, w j * χ j x‖ ^ 2 ≤ ε ^ 2 := by
  have hcard : (largeSpectrum f ε).card ≤ M := by
    exact_mod_cast (largeSpectrum_card_bound f hf ε hε).trans hM
  have hcoef (η : AddChar G ℂ) : ‖coefficient (convolution f g) η‖ ≤ 1 := by
    rw [coefficient_convolution, norm_mul]
    calc
      ‖coefficient f η‖ * ‖coefficient g η‖ ≤ 1 * 1 :=
        mul_le_mul (coefficient_norm_le_one f hf η) (coefficient_norm_le_one g hg η)
          (norm_nonneg _) (by norm_num)
      _ = 1 := by norm_num
  obtain ⟨χ, w, hw, hpoly⟩ := pad_character_polynomial (largeSpectrum f ε)
    (coefficient (convolution f g)) (fun η _ => hcoef η) M hcard
  have heq (x : G) : (∑ j : Fin M, w j * χ j x) =
      truncation (convolution f g) (largeSpectrum f ε) x := by
    simpa only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, truncation] using congrFun hpoly x
  refine ⟨χ, w, hw, ?_⟩
  simp_rw [heq]
  exact (convolution_truncation_energy_bound f g ε hε).trans
    (by simpa only [mul_one] using
      mul_le_mul_of_nonneg_left (normalized_energy_le_one g hg) (sq_nonneg ε))

end Erdos335.FiniteFourier
