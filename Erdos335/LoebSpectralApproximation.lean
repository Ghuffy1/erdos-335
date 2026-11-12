import Erdos335.FiniteSpectralApproximation
import Erdos335.LoebPolynomial
import Erdos335.LoebConvolution

/-!
# Finite-rank approximations to Loeb convolution

Uniform finite Fourier approximation passes to the counting Loeb measure.
The resulting approximants are finite polynomials in internal characters.
-/

set_option autoImplicit false

open Filter Set Topology MeasureTheory
open scoped BigOperators

namespace Erdos335.Loeb

theorem normalized_convolution_norm_le_one
    {G : Type*} [AddCommGroup G] [Fintype G]
    (f g : G → ℂ) (hf : ∀ x, ‖f x‖ ≤ 1) (hg : ∀ x, ‖g x‖ ≤ 1) (x : G) :
    ‖FiniteFourier.convolution f g x‖ ≤ 1 := by
  have hsum : (∑ y : G, ‖f y * g (x - y)‖) ≤ Fintype.card G := by
    calc
      (∑ y : G, ‖f y * g (x - y)‖) ≤ ∑ _y : G, (1 : ℝ) := by
        apply Finset.sum_le_sum
        intro y _
        rw [norm_mul]
        exact (mul_le_mul (hf y) (hg (x - y)) (norm_nonneg _) (by norm_num)).trans_eq (one_mul 1)
      _ = _ := by simp
  have hcard : (0 : ℝ) < Fintype.card G := by exact_mod_cast Fintype.card_pos
  calc
    ‖FiniteFourier.convolution f g x‖ ≤ 𝔼 y, ‖f y * g (x - y)‖ := RCLike.norm_expect_le (K := ℂ)
    _ = (∑ y : G, ‖f y * g (x - y)‖) / Fintype.card G := Fintype.expect_eq_sum_div_card _
    _ ≤ 1 := (div_le_one hcard).mpr hsum

theorem boundedComplex_convolution_eq
    {X : ℕ → Type*} [∀ n, AddCommGroup (X n)] [∀ n, Fintype (X n)]
    (U : Ultrafilter ℕ) (hU : (U : Filter ℕ) ≤ atTop)
    (f g : ∀ n, X n → ℂ) (hf : ∀ n x, ‖f n x‖ ≤ 1) (hg : ∀ n x, ‖g n x‖ ≤ 1)
    (x : (U : Filter ℕ).Product X) :
    boundedComplexFunction U (fun n => FiniteFourier.convolution (f n) (g n)) 1
        (fun n y => normalized_convolution_norm_le_one (f n) (g n) (hf n) (hg n) y) x =
      ∫ t, boundedComplexFunction U f 1 hf t * boundedComplexFunction U g 1 hg (x - t)
        ∂loebMeasure U hU := by
  induction x using Quotient.inductionOn with
  | h a =>
    change _ = ∫ t, boundedComplexFunction U f 1 hf t *
      boundedComplexFunction U g 1 hg (productProjection (U : Filter ℕ) a - t)
        ∂loebMeasure U hU
    apply tendsto_nhds_unique (tendsto_boundedComplexFunction U _ _ _ a)
    have hlim := tendsto_coordinate_convolution U hU f g 1 1 hf hg a
    simpa only [FiniteFourier.convolution, Fintype.expect_eq_sum_div_card,
      Nat.card_eq_fintype_card, div_eq_mul_inv, RCLike.real_smul_eq_coe_mul,
      RCLike.ofReal_inv, RCLike.ofReal_natCast, mul_comm] using hlim

theorem exists_loeb_convolution_polynomial
    {X : ℕ → Type*} [∀ n, AddCommGroup (X n)] [∀ n, Fintype (X n)]
    (U : Ultrafilter ℕ) (hU : (U : Filter ℕ) ≤ atTop)
    (f g : ∀ n, X n → ℂ) (hf : ∀ n x, ‖f n x‖ ≤ 1) (hg : ∀ n x, ‖g n x‖ ≤ 1)
    (ε : ℝ) (hε : 0 < ε) (M : ℕ) (hM : 1 / ε ^ 2 ≤ (M : ℝ)) :
    ∃ (χ : ∀ n, Fin M → AddChar (X n) Circle) (c : Fin M → ℂ),
      (∀ j, ‖c j‖ ≤ 1) ∧
      (∫ x, ‖(∫ t, boundedComplexFunction U f 1 hf t *
        boundedComplexFunction U g 1 hg (x - t) ∂loebMeasure U hU) -
          ∑ j : Fin M, c j *
            ((ultralimitAddHom U (fun n => (χ n j).toAddMonoidHom) x).toMul : ℂ)‖ ^ 2
          ∂loebMeasure U hU) ≤ ε ^ 2 := by
  classical
  choose χ w hw herr using fun n =>
    FiniteFourier.exists_uniform_spectral_polynomial (f n) (g n) (hf n) (hg n) ε hε M hM
  let ψ (n : ℕ) (j : Fin M) : AddChar (X n) Circle :=
    AddChar.circleEquivComplex.symm (χ n j)
  have hψ (n : ℕ) (j : Fin M) (x : X n) : (ψ n j x : ℂ) = χ n j x := by
    change (AddChar.circleEquivComplex (ψ n j)) x = _
    rw [AddChar.circleEquivComplex.apply_symm_apply]
  let P (n : ℕ) (x : X n) : ℂ := ∑ j : Fin M, w n j * (ψ n j x : ℂ)
  have hP : ∀ n x, ‖P n x‖ ≤ (M : ℝ) := by
    intro n x
    simpa only [P, Fintype.card_fin, mul_one] using
      character_polynomial_norm_le (w n) (ψ n) 1 (hw n) x
  obtain ⟨c, hc, hstandard⟩ := exists_character_polynomial_standardPart U w ψ 1 hw
  have hstandard' : boundedComplexFunction U P (M : ℝ) hP =
      fun x => ∑ j : Fin M, c j *
        ((ultralimitAddHom U (fun n => (ψ n j).toAddMonoidHom) x).toMul : ℂ) := by
    have hold : ∀ n x, ‖P n x‖ ≤ Fintype.card (Fin M) * (1 : ℝ) :=
      fun n x => character_polynomial_norm_le (w n) (ψ n) 1 (hw n) x
    rw [← boundedComplexFunction_independent_bound U P _ _ hold hP]
    exact hstandard
  have hevent : ∀ᶠ n in U, (Nat.card (X n) : ℝ)⁻¹ *
      ∑ x : X n, ‖FiniteFourier.convolution (f n) (g n) x - P n x‖ ^ 2 ≤ ε ^ 2 := by
    apply Filter.Eventually.of_forall
    intro n
    simpa only [P, hψ, Nat.card_eq_fintype_card] using herr n
  have hbound := loeb_sqDistance_le_of_eventually U hU
    (fun n => FiniteFourier.convolution (f n) (g n)) P 1 (M : ℝ)
    (fun n x => normalized_convolution_norm_le_one (f n) (g n) (hf n) (hg n) x) hP
    (ε ^ 2) hevent
  rw [hstandard'] at hbound
  simp_rw [boundedComplex_convolution_eq U hU f g hf hg] at hbound
  exact ⟨ψ, c, hc, hbound⟩

end Erdos335.Loeb
