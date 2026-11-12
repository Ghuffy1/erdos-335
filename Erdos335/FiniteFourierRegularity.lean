import Erdos335.FiniteRegularityParameters
import Erdos335.FiniteFourierConvolution

/-!
# Quantized character factors with Fourier-uniform residual
-/

set_option autoImplicit false

open Finset RCLike
open scoped BigOperators Classical ComplexConjugate

namespace Erdos335.IntermediateScale

variable {G : Type*} [AddCommGroup G] [Fintype G]

def realCharacterTests : Set (G → ℝ) :=
  Set.range (fun χ : AddChar G ℂ => fun x => (χ x).re) ∪
    Set.range (fun χ : AddChar G ℂ => fun x => (χ x).im)

theorem realCharacterTests_bound (u : G → ℝ) (hu : u ∈ realCharacterTests) (x : G) :
    |u x| ≤ 1 := by
  rcases hu with ⟨χ, rfl⟩ | ⟨χ, rfl⟩
  · exact (Complex.abs_re_le_norm _).trans_eq (χ.norm_apply x)
  · exact (Complex.abs_im_le_norm _).trans_eq (χ.norm_apply x)

theorem coefficient_real_formula (f : G → ℝ) (χ : AddChar G ℂ) :
    FiniteFourier.coefficient (fun x => (f x : ℂ)) χ =
      ((Fintype.card G : ℝ)⁻¹ : ℂ) *
        ((∑ x : G, f x * (χ x).re : ℝ) - Complex.I * (∑ x : G, f x * (χ x).im : ℝ)) := by
  have hsum : (∑ x : G, (f x : ℂ) * conj (χ x)) =
      ((∑ x : G, f x * (χ x).re : ℝ) : ℂ) -
        Complex.I * ((∑ x : G, f x * (χ x).im : ℝ) : ℂ) := by
    apply Complex.ext <;> simp
  unfold FiniteFourier.coefficient RCLike.wInner
  simp only [RCLike.cWeight, Function.const_apply, RCLike.inner_apply,
    RCLike.real_smul_eq_coe_mul, ← Finset.mul_sum]
  rw [hsum]
  push_cast
  rfl

theorem coefficient_norm_le_of_real_tests (f : G → ℝ) (χ : AddChar G ℂ) (ε : ℝ)
    (hre : |∑ x : G, f x * (χ x).re| ≤ ε * Fintype.card G)
    (him : |∑ x : G, f x * (χ x).im| ≤ ε * Fintype.card G) :
    ‖FiniteFourier.coefficient (fun x => (f x : ℂ)) χ‖ ≤ 2 * ε := by
  have hG : (0 : ℝ) < Fintype.card G := by exact_mod_cast Fintype.card_pos
  simp only [coefficient_real_formula, Complex.ofReal_natCast,
    norm_mul, norm_inv, Complex.norm_natCast]
  have hnorm : ‖((∑ x : G, f x * (χ x).re : ℝ) : ℂ) -
      Complex.I * ((∑ x : G, f x * (χ x).im : ℝ) : ℂ)‖ ≤
      |∑ x : G, f x * (χ x).re| + |∑ x : G, f x * (χ x).im| := by
    simpa [Complex.mul_re, Complex.mul_im] using
      Complex.norm_le_abs_re_add_abs_im
        (((∑ x : G, f x * (χ x).re : ℝ) : ℂ) -
          Complex.I * ((∑ x : G, f x * (χ x).im : ℝ) : ℂ))
  calc
    _ ≤ (Fintype.card G : ℝ)⁻¹ *
        (|∑ x : G, f x * (χ x).re| + |∑ x : G, f x * (χ x).im|) := by gcongr
    _ ≤ (Fintype.card G : ℝ)⁻¹ * (ε * Fintype.card G + ε * Fintype.card G) := by gcongr
    _ = 2 * ε := by field_simp; ring

theorem finite_fourier_uniform_partition (f : G → ℝ)
    (hf : ∀ x, f x ∈ Set.Icc (0 : ℝ) 1) (ε : ℝ) (hε : 0 < ε) :
    ∃ (N D : ℕ) (S : Finset (G → ℝ)), 0 < N ∧
      (S : Set (G → ℝ)) ⊆ realCharacterTests ∧ S.card ≤ D ∧
      ∀ χ : AddChar G ℂ,
        ‖FiniteFourier.coefficient
          (fun x => ((f x - finiteConditionalMean (testPartition N S) f x : ℝ) : ℂ)) χ‖ ≤ ε := by
  obtain ⟨N, D, hN, hthreshold, hD⟩ := exists_finite_regularity_parameters (ε / 2) (by positivity)
  obtain ⟨S, hS, hcard, htests⟩ := finite_test_regularity f hf realCharacterTests
    realCharacterTests_bound (ε / 2) N D hN (hthreshold.trans (by linarith)) hD
  refine ⟨N, D, S, hN, hS, hcard, ?_⟩
  intro χ
  have hre := htests (fun x => (χ x).re) (Or.inl ⟨χ, rfl⟩)
  have him := htests (fun x => (χ x).im) (Or.inr ⟨χ, rfl⟩)
  have hbound := coefficient_norm_le_of_real_tests
    (fun x => f x - finiteConditionalMean (testPartition N S) f x) χ (ε / 2) hre him
  linarith

end Erdos335.IntermediateScale
