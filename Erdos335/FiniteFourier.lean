import Mathlib.Analysis.Fourier.FiniteAbelian.PontryaginDuality
import Mathlib.Tactic

/-!
# Normalized finite Fourier coefficients

The character basis and its orthogonality are supplied by Mathlib.
The normalization here agrees with the counting probabilities used in the
Loeb models.
-/

set_option autoImplicit false

open Finset RCLike
open scoped BigOperators ComplexConjugate

namespace Erdos335.FiniteFourier

variable {G : Type*} [AddCommGroup G] [Fintype G]

noncomputable def coefficient (f : G → ℂ) (χ : AddChar G ℂ) : ℂ :=
  RCLike.wInner RCLike.cWeight (χ : G → ℂ) f

omit [AddCommGroup G] in
theorem wInner_sum_right {ι : Type*} (s : Finset ι) (w : G → ℝ)
    (f : G → ℂ) (g : ι → G → ℂ) :
    RCLike.wInner (𝕜 := ℂ) w f (∑ i ∈ s, g i) =
      ∑ i ∈ s, RCLike.wInner (𝕜 := ℂ) w f (g i) := by
  simp only [RCLike.wInner, Finset.sum_apply, inner_sum, smul_sum]
  exact sum_comm

theorem coefficient_eq_basis_repr (f : G → ℂ) (χ : AddChar G ℂ) :
    coefficient f χ = (AddChar.complexBasis G).repr f χ := by
  classical
  let b := AddChar.complexBasis G
  have hsum : ∑ η : AddChar G ℂ, b.repr f η • (η : G → ℂ) = f := by
    simpa only [b, AddChar.complexBasis_apply] using b.sum_repr f
  conv_lhs => rw [← hsum]
  unfold coefficient
  rw [show (∑ η : AddChar G ℂ, b.repr f η • (η : G → ℂ)) =
      ∑ η ∈ (Finset.univ : Finset (AddChar G ℂ)), b.repr f η • (η : G → ℂ) by simp]
  rw [wInner_sum_right]
  simp [RCLike.wInner_smul_right, AddChar.wInner_cWeight_eq_boole, smul_eq_mul, b]

theorem expansion (f : G → ℂ) :
    ∑ χ : AddChar G ℂ, coefficient f χ • (χ : G → ℂ) = f := by
  simpa only [coefficient_eq_basis_repr, AddChar.complexBasis_apply] using
    (AddChar.complexBasis G).sum_repr f

theorem inner_eq_sum_coefficients (f g : G → ℂ) :
    RCLike.wInner (𝕜 := ℂ) RCLike.cWeight f g =
      ∑ χ : AddChar G ℂ, conj (coefficient f χ) * coefficient g χ := by
  classical
  conv_lhs => rw [← expansion g]
  rw [show (∑ χ : AddChar G ℂ, coefficient g χ • (χ : G → ℂ)) =
      ∑ χ ∈ (Finset.univ : Finset (AddChar G ℂ)), coefficient g χ • (χ : G → ℂ) by simp]
  rw [wInner_sum_right]
  apply Finset.sum_congr rfl
  intro χ _
  rw [RCLike.wInner_smul_right]
  have hconj := RCLike.conj_wInner_symm (𝕜 := ℂ) RCLike.cWeight (χ : G → ℂ) f
  change coefficient g χ * RCLike.wInner RCLike.cWeight f (χ : G → ℂ) = _
  rw [← hconj]
  exact mul_comm _ _

theorem parseval (f : G → ℂ) :
    (∑ χ : AddChar G ℂ, ‖coefficient f χ‖ ^ 2) =
      (Fintype.card G : ℝ)⁻¹ * ∑ x : G, ‖f x‖ ^ 2 := by
  have h := inner_eq_sum_coefficients f f
  simp only [RCLike.wInner, RCLike.cWeight, Function.const_apply,
    RCLike.inner_apply, RCLike.conj_mul, RCLike.mul_conj,
    RCLike.real_smul_eq_coe_mul, ← RCLike.ofReal_pow, ← RCLike.ofReal_mul,
    ← RCLike.ofReal_sum] at h
  have hr := RCLike.ofReal_inj.mp h
  simpa only [← Finset.mul_sum] using hr.symm

theorem coefficient_add (f g : G → ℂ) (χ : AddChar G ℂ) :
    coefficient (f + g) χ = coefficient f χ + coefficient g χ :=
  RCLike.wInner_add_right _ _ _ _

theorem coefficient_sub (f g : G → ℂ) (χ : AddChar G ℂ) :
    coefficient (f - g) χ = coefficient f χ - coefficient g χ :=
  RCLike.wInner_sub_right _ _ _ _

noncomputable def truncation (f : G → ℂ) (S : Finset (AddChar G ℂ)) : G → ℂ :=
  ∑ χ ∈ S, coefficient f χ • (χ : G → ℂ)

theorem coefficient_truncation (f : G → ℂ) (S : Finset (AddChar G ℂ)) (χ : AddChar G ℂ) :
    coefficient (truncation f S) χ = if χ ∈ S then coefficient f χ else 0 := by
  classical
  unfold coefficient truncation
  rw [wInner_sum_right]
  simp [RCLike.wInner_smul_right, AddChar.wInner_cWeight_eq_boole, smul_eq_mul, coefficient]

noncomputable def largeSpectrum (f : G → ℂ) (ε : ℝ) : Finset (AddChar G ℂ) := by
  classical
  exact Finset.univ.filter (fun χ => ε ≤ ‖coefficient f χ‖)

theorem largeSpectrum_card_mul_sq_le (f : G → ℂ) (ε : ℝ) (hε : 0 ≤ ε) :
    ((largeSpectrum f ε).card : ℝ) * ε ^ 2 ≤
      (Fintype.card G : ℝ)⁻¹ * ∑ x : G, ‖f x‖ ^ 2 := by
  classical
  have hfirst : ((largeSpectrum f ε).card : ℝ) * ε ^ 2 ≤
      ∑ χ ∈ largeSpectrum f ε, ‖coefficient f χ‖ ^ 2 := by
    calc
      ((largeSpectrum f ε).card : ℝ) * ε ^ 2 = ∑ _χ ∈ largeSpectrum f ε, ε ^ 2 := by simp
      _ ≤ _ := by
        apply Finset.sum_le_sum
        intro χ hχ
        have hbound : ε ≤ ‖coefficient f χ‖ := (Finset.mem_filter.mp hχ).2
        nlinarith [norm_nonneg (coefficient f χ)]
  have hsecond : (∑ χ ∈ largeSpectrum f ε, ‖coefficient f χ‖ ^ 2) ≤
      ∑ χ : AddChar G ℂ, ‖coefficient f χ‖ ^ 2 :=
    Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _) (fun _ _ _ => sq_nonneg _)
  exact hfirst.trans (hsecond.trans_eq (parseval f))

theorem normalized_energy_le_one (f : G → ℂ) (hf : ∀ x, ‖f x‖ ≤ 1) :
    (Fintype.card G : ℝ)⁻¹ * ∑ x : G, ‖f x‖ ^ 2 ≤ 1 := by
  have hsum : (∑ x : G, ‖f x‖ ^ 2) ≤ Fintype.card G := by
    calc
      (∑ x : G, ‖f x‖ ^ 2) ≤ ∑ _x : G, (1 : ℝ) := by
        apply Finset.sum_le_sum
        intro x _
        have := hf x
        nlinarith [norm_nonneg (f x)]
      _ = _ := by simp
  have hcard : (0 : ℝ) < Fintype.card G := by exact_mod_cast Fintype.card_pos
  calc
    (Fintype.card G : ℝ)⁻¹ * ∑ x : G, ‖f x‖ ^ 2 ≤
        (Fintype.card G : ℝ)⁻¹ * Fintype.card G :=
      mul_le_mul_of_nonneg_left hsum (inv_nonneg.mpr hcard.le)
    _ = 1 := inv_mul_cancel₀ hcard.ne'

theorem largeSpectrum_card_bound (f : G → ℂ) (hf : ∀ x, ‖f x‖ ≤ 1)
    (ε : ℝ) (hε : 0 < ε) : ((largeSpectrum f ε).card : ℝ) ≤ 1 / ε ^ 2 := by
  exact (le_div_iff₀ (sq_pos_of_pos hε)).mpr
    ((largeSpectrum_card_mul_sq_le f ε hε.le).trans (normalized_energy_le_one f hf))

end Erdos335.FiniteFourier
