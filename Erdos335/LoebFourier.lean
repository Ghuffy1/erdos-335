import Erdos335.LoebSpectralApproximation

/-!
# Fourier coefficients on a finite-group Loeb model

Internal characters have their expected standard parts. Fourier coefficients
of bounded internal functions transfer to Loeb integrals, and convolution
multiplies these coefficients.
-/

set_option autoImplicit false

open Filter Set Topology MeasureTheory
open scoped BigOperators ComplexConjugate

namespace Erdos335.Loeb

theorem boundedComplexFunction_conj_character
    {X : ℕ → Type*} [∀ n, AddCommGroup (X n)]
    (U : Ultrafilter ℕ) (χ : ∀ n, AddChar (X n) Circle)
    (hχ : ∀ n x, ‖conj (χ n x : ℂ)‖ ≤ 1)
    (x : (U : Filter ℕ).Product X) :
    boundedComplexFunction U (fun n y => conj (χ n y : ℂ)) 1 hχ x =
      conj ((ultralimitAddHom U (fun n => (χ n).toAddMonoidHom) x).toMul : ℂ) := by
  induction x using Quotient.inductionOn with
  | h x =>
    have hcontinuous : Continuous (fun z : Additive Circle => conj (z.toMul : ℂ)) :=
      continuous_star.comp continuous_subtype_val
    exact tendsto_nhds_unique (tendsto_boundedComplexFunction U _ 1 hχ x)
      ((hcontinuous.tendsto _).comp (tendsto_ultralimitFunction U (fun n => (χ n).toAddMonoidHom) x))

theorem tendsto_internal_fourier_coefficients
    {X : ℕ → Type*} [∀ n, AddCommGroup (X n)] [∀ n, Fintype (X n)]
    (U : Ultrafilter ℕ) (hU : (U : Filter ℕ) ≤ atTop)
    (f : ∀ n, X n → ℂ) (hf : ∀ n x, ‖f n x‖ ≤ 1)
    (χ : ∀ n, AddChar (X n) Circle) :
    Tendsto (fun n => FiniteFourier.coefficient (f n) (Circle.coeHom.compAddChar (χ n)))
      (U : Filter ℕ)
      (𝓝 (∫ x, boundedComplexFunction U f 1 hf x *
        conj ((ultralimitAddHom U (fun n => (χ n).toAddMonoidHom) x).toMul : ℂ)
          ∂loebMeasure U hU)) := by
  let c : ∀ n, X n → ℂ := fun n x => conj (χ n x : ℂ)
  have hc (n : ℕ) (x : X n) : ‖c n x‖ ≤ 1 := by simp [c]
  have hp (n : ℕ) (x : X n) : ‖f n x * c n x‖ ≤ 1 := by
    rw [norm_mul]
    exact (mul_le_mul (hf n x) (hc n x) (norm_nonneg _) (by norm_num)).trans_eq (one_mul 1)
  have hlim := tendsto_boundedComplexFunction_averages U hU
    (fun n x => f n x * c n x) 1 hp
  have hproduct := boundedComplexFunction_mul U f c 1 1 1 hf hc hp
  have hvalue : boundedComplexFunction U (fun n x => f n x * c n x) 1 hp =
      fun x => boundedComplexFunction U f 1 hf x *
        conj ((ultralimitAddHom U (fun n => (χ n).toAddMonoidHom) x).toMul : ℂ) := by
    funext x
    rw [congrFun hproduct x]
    rw [boundedComplexFunction_conj_character U χ hc x]
  rw [hvalue] at hlim
  have havg (n : ℕ) :
      FiniteFourier.coefficient (f n) (Circle.coeHom.compAddChar (χ n)) =
        (Nat.card (X n) : ℝ)⁻¹ • ∑ x : X n, f n x * c n x := by
    rw [FiniteFourier.coefficient_eq_expect, Fintype.expect_eq_sum_div_card, Nat.card_eq_fintype_card]
    change (∑ x : X n, f n x * conj (χ n x : ℂ)) / (Fintype.card (X n) : ℂ) =
      (Fintype.card (X n) : ℝ)⁻¹ • ∑ x : X n, f n x * conj (χ n x : ℂ)
    simp only [div_eq_mul_inv, RCLike.real_smul_eq_coe_mul, RCLike.ofReal_inv,
      RCLike.ofReal_natCast, mul_comm]
  simpa only [havg] using hlim

theorem internal_fourier_convolution
    {X : ℕ → Type*} [∀ n, AddCommGroup (X n)] [∀ n, Fintype (X n)]
    (U : Ultrafilter ℕ) (hU : (U : Filter ℕ) ≤ atTop)
    (f g : ∀ n, X n → ℂ) (hf : ∀ n x, ‖f n x‖ ≤ 1) (hg : ∀ n x, ‖g n x‖ ≤ 1)
    (χ : ∀ n, AddChar (X n) Circle) :
    (∫ x, (∫ t, boundedComplexFunction U f 1 hf t *
      boundedComplexFunction U g 1 hg (x - t) ∂loebMeasure U hU) *
        conj ((ultralimitAddHom U (fun n => (χ n).toAddMonoidHom) x).toMul : ℂ)
          ∂loebMeasure U hU) =
      (∫ x, boundedComplexFunction U f 1 hf x *
        conj ((ultralimitAddHom U (fun n => (χ n).toAddMonoidHom) x).toMul : ℂ) ∂loebMeasure U hU) *
      (∫ x, boundedComplexFunction U g 1 hg x *
        conj ((ultralimitAddHom U (fun n => (χ n).toAddMonoidHom) x).toMul : ℂ) ∂loebMeasure U hU) := by
  have hfconv (n : ℕ) (x : X n) : ‖FiniteFourier.convolution (f n) (g n) x‖ ≤ 1 :=
    normalized_convolution_norm_le_one (f n) (g n) (hf n) (hg n) x
  have hleft := tendsto_internal_fourier_coefficients U hU
    (fun n => FiniteFourier.convolution (f n) (g n)) hfconv χ
  have hright := (tendsto_internal_fourier_coefficients U hU f hf χ).mul
    (tendsto_internal_fourier_coefficients U hU g hg χ)
  simp_rw [FiniteFourier.coefficient_convolution] at hleft
  have hvalue := tendsto_nhds_unique hleft hright
  simpa only [boundedComplex_convolution_eq U hU f g hf hg] using hvalue

end Erdos335.Loeb
