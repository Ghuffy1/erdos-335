import Erdos335.ConditionalFourier
import Erdos335.LoebFourier
import Erdos335.LoebPositiveInputs
import Erdos335.LoebInternalCharacters
import Erdos335.CompactFourierUniqueness
import Erdos335.CompactConvolutionL2

/-!
# Identifying convolution on the compact factor

Fourier multiplication on the finite-group model and on the compact factor
gives the same coefficients. The internal characters separate points, so
their dense span identifies the two square-integrable functions.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Filter Set Topology MeasureTheory
open scoped ENNReal ComplexConjugate

noncomputable section

namespace Erdos335.Loeb

variable {X : ℕ → Type*} [∀ n, AddCommGroup (X n)] [∀ n, Fintype (X n)]

local instance projectionLoebMeasurableSpace (U : Ultrafilter ℕ) : MeasurableSpace ((U : Filter ℕ).Product X) :=
  loebMeasurableSpace U
local instance projectionCircleMeasurableSpace : MeasurableSpace (Additive Circle) := borel (Additive Circle)
local instance projectionCircleBorelSpace : BorelSpace (Additive Circle) := ⟨rfl⟩

theorem loeb_convolution_projection
    (U : Ultrafilter ℕ) (hU : (U : Filter ℕ) ≤ atTop)
    (f g : ∀ n, X n → ℝ) (hf : ∀ n x, |f n x| ≤ 1) (hg : ∀ n x, |g n x| ≤ 1)
    (F : ℕ → ∀ n, X n →+ Additive Circle)
    [CompactSpace (countableUltralimitHom U F).range]
    (a b : (countableUltralimitHom U F).range → ℝ)
    (Q : (countableUltralimitHom U F).range → ℂ)
    (ha : StronglyMeasurable a) (hb : StronglyMeasurable b) (hQ : StronglyMeasurable Q)
    (hbound : ∀ y, a y ∈ Icc (0 : ℝ) 1 ∧ b y ∈ Icc (0 : ℝ) 1)
    (hA : (loebMeasure U hU)[boundedRealFunction U f 1 hf |
        (inferInstance : MeasurableSpace (countableUltralimitHom U F).range).comap
          (countableUltralimitHom U F).rangeRestrict] =ᵐ[loebMeasure U hU]
        a ∘ (countableUltralimitHom U F).rangeRestrict)
    (hB : (loebMeasure U hU)[boundedRealFunction U g 1 hg |
        (inferInstance : MeasurableSpace (countableUltralimitHom U F).range).comap
          (countableUltralimitHom U F).rangeRestrict] =ᵐ[loebMeasure U hU]
        b ∘ (countableUltralimitHom U F).rangeRestrict)
    (hrep : (fun x => ∫ t, (boundedRealFunction U f 1 hf t : ℂ) *
        (boundedRealFunction U g 1 hg (x - t) : ℂ) ∂loebMeasure U hU) =ᵐ[loebMeasure U hU]
          Q ∘ (countableUltralimitHom U F).rangeRestrict) :
    Q =ᵐ[Measure.map (countableUltralimitHom U F).rangeRestrict (loebMeasure U hU)]
      (fun x => ∫ t, (a t : ℂ) * (b (x - t) : ℂ)
        ∂Measure.map (countableUltralimitHom U F).rangeRestrict (loebMeasure U hU)) := by
  letI : MetricSpace (ℕ → Additive Circle) := PiCountable.metricSpace
  let q := (countableUltralimitHom U F).rangeRestrict
  let μ := loebMeasure (X := X) U hU
  let ν := Measure.map q μ
  let H : (U : Filter ℕ).Product X → ℂ := fun x =>
    ∫ t, (boundedRealFunction U f 1 hf t : ℂ) * (boundedRealFunction U g 1 hg (x - t) : ℂ) ∂μ
  let af : (countableUltralimitHom U F).range → ℂ := fun y => (a y : ℂ)
  let bf : (countableUltralimitHom U F).range → ℂ := fun y => (b y : ℂ)
  let K : (countableUltralimitHom U F).range → ℂ := fun x => ∫ t, af t * bf (x - t) ∂ν
  have hq : Measurable q := (measurable_countableUltralimitHom U F).subtype_mk
  letI : IsProbabilityMeasure μ := isProbabilityMeasure_loebMeasure U hU
  letI : IsProbabilityMeasure ν := ⟨by
    change (Measure.map q μ) univ = 1
    rw [Measure.map_apply hq MeasurableSet.univ]
    simp⟩
  letI : Measure.IsAddHaarMeasure ν := countableUltralimitHom_haar U hU F
  have haf : StronglyMeasurable af := Complex.continuous_ofReal.comp_stronglyMeasurable ha
  have hbf : StronglyMeasurable bf := Complex.continuous_ofReal.comp_stronglyMeasurable hb
  have hafbound (y) : ‖af y‖ ≤ 1 := by
    simpa [af, abs_of_nonneg (hbound y).1.1] using (hbound y).1.2
  have hbfbound (y) : ‖bf y‖ ≤ 1 := by
    simpa [bf, abs_of_nonneg (hbound y).2.1] using (hbound y).2.2
  have hafint : Integrable af ν := Integrable.of_bound haf.aestronglyMeasurable 1 (ae_of_all ν hafbound)
  have hbfint : Integrable bf ν := Integrable.of_bound hbf.aestronglyMeasurable 1 (ae_of_all ν hbfbound)
  have hKmem : MemLp K 2 ν := probability_convolution_memLp_two ν af bf
    haf.aestronglyMeasurable hbf.aestronglyMeasurable hafbound hbfbound
  let fc : ∀ n, X n → ℂ := fun n x => (f n x : ℂ)
  let gc : ∀ n, X n → ℂ := fun n x => (g n x : ℂ)
  have hfc (n) (x : X n) : ‖fc n x‖ ≤ 1 := by
    simpa only [fc, Complex.norm_real, Real.norm_eq_abs] using hf n x
  have hgc (n) (x : X n) : ‖gc n x‖ ≤ 1 := by
    simpa only [gc, Complex.norm_real, Real.norm_eq_abs] using hg n x
  have hfstd (x) : boundedComplexFunction U fc 1 hfc x = (boundedRealFunction U f 1 hf x : ℂ) :=
    boundedComplexFunction_ofReal U f 1 hf hfc x
  have hgstd (x) : boundedComplexFunction U gc 1 hgc x = (boundedRealFunction U g 1 hg x : ℂ) :=
    boundedComplexFunction_ofReal U g 1 hg hgc x
  have hc (n) (x : X n) : ‖FiniteFourier.convolution (fc n) (gc n) x‖ ≤ 1 :=
    normalized_convolution_norm_le_one (fc n) (gc n) (hfc n) (hgc n) x
  have hHstd : H = boundedComplexFunction U (fun n => FiniteFourier.convolution (fc n) (gc n)) 1 hc := by
    funext x
    symm
    rw [boundedComplex_convolution_eq U hU fc gc hfc hgc]
    simp only [H, μ, hfstd, hgstd]
  have hHmem : MemLp H 2 μ := by
    rw [hHstd]
    exact MemLp.of_bound (measurable_boundedComplexFunction U _ _ _).aestronglyMeasurable
      1 (ae_of_all μ (boundedComplexFunction_bound U _ _ _))
  have hQmem : MemLp Q 2 ν := factor_memLp_two_of_ae_eq μ q hq H hHmem Q hQ hrep
  apply ae_eq_of_separating_multiplicative_integrals ν (internalCharacterFunctions U F)
    (one_mem_internalCharacterFunctions U F)
    (fun p hp r hr => mul_mem_internalCharacterFunctions U F p r hp hr)
    (star_mem_internalCharacterFunctions U F) (internalCharacterFunctions_separate U F)
    Q K hQmem hKmem
  intro p hp
  have hpbound (y) : ‖p y‖ ≤ 1 := (internalCharacterFunctions_norm U F p hp y).le
  obtain ⟨ψ, hψ⟩ := internalCharacterFunctions_addChar U F p hp
  have hψmeas : Measurable (fun y => (ψ y : ℂ)) := by
    simpa only [hψ] using p.continuous.measurable
  have hcompact := integral_convolution_character ν ψ hψmeas af bf hafint hbfint
  simp only [hψ] at hcompact
  have htestQ := integral_factor_conjugate_test μ q hq H Q hQ hrep p p.continuous.stronglyMeasurable
  have htestA := integral_conditional_conjugate_test μ q hq (boundedRealFunction U f 1 hf)
    (integrable_boundedRealFunction U hU f 1 hf) a ha hA p p.continuous.stronglyMeasurable hpbound
  have htestB := integral_conditional_conjugate_test μ q hq (boundedRealFunction U g 1 hg)
    (integrable_boundedRealFunction U hU g 1 hg) b hb hB p p.continuous.stronglyMeasurable hpbound
  obtain ⟨χ, hχ⟩ := hp
  have hloeb := internal_fourier_convolution U hU fc gc hfc hgc χ
  have hproduct : (∫ x, H x * conj (p (q x)) ∂μ) =
      (∫ x, (boundedRealFunction U f 1 hf x : ℂ) * conj (p (q x)) ∂μ) *
      (∫ x, (boundedRealFunction U g 1 hg x : ℂ) * conj (p (q x)) ∂μ) := by
    simpa only [H, q, μ, hfstd, hgstd, hχ] using hloeb
  calc
    (∫ x, Q x * conj (p x) ∂ν) = ∫ x, H x * conj (p (q x)) ∂μ := htestQ
    _ = (∫ x, (boundedRealFunction U f 1 hf x : ℂ) * conj (p (q x)) ∂μ) *
        (∫ x, (boundedRealFunction U g 1 hg x : ℂ) * conj (p (q x)) ∂μ) := hproduct
    _ = (∫ x, af x * conj (p x) ∂ν) * (∫ x, bf x * conj (p x) ∂ν) := by rw [htestA, htestB]
    _ = ∫ x, K x * conj (p x) ∂ν := hcompact.symm

end Erdos335.Loeb

end
