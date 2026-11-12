import Erdos335.LoebConvolutionProjection
import Erdos335.LoebConvolutionRepresentation

/-!
# Compact positive convolution models for internal functions

This is the internal-function case of Griesmer's compact convolution
reduction. Both inputs descend through conditional expectation, their
positive supports are retained almost everywhere, and their convolution is
the pullback of the compact Haar convolution.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Filter Set Topology MeasureTheory

noncomputable section

namespace Erdos335.Loeb

variable {X : ℕ → Type*} [∀ n, AddCommGroup (X n)] [∀ n, Fintype (X n)]

local instance modelLoebMeasurableSpace (U : Ultrafilter ℕ) : MeasurableSpace ((U : Filter ℕ).Product X) :=
  loebMeasurableSpace U
local instance modelCircleMeasurableSpace : MeasurableSpace (Additive Circle) := borel (Additive Circle)
local instance modelCircleBorelSpace : BorelSpace (Additive Circle) := ⟨rfl⟩

theorem exists_compact_positive_convolution_model
    (U : Ultrafilter ℕ) (hU : (U : Filter ℕ) ≤ atTop)
    (f g : ∀ n, X n → ℝ) (hf : ∀ n x, |f n x| ≤ 1) (hg : ∀ n x, |g n x| ≤ 1)
    (hfpos : ∀ n x, f n x ∈ Icc (0 : ℝ) 1)
    (hgpos : ∀ n x, g n x ∈ Icc (0 : ℝ) 1) :
    ∃ F : ℕ → ∀ n, X n →+ Additive Circle,
      ∃ a b : (countableUltralimitHom U F).range → ℝ,
        IsCompact ((countableUltralimitHom U F).range : Set (ℕ → Additive Circle)) ∧
        Measure.IsAddHaarMeasure
          (Measure.map (countableUltralimitHom U F).rangeRestrict (loebMeasure U hU)) ∧
        StronglyMeasurable a ∧ StronglyMeasurable b ∧
        (∀ y, a y ∈ Icc (0 : ℝ) 1 ∧ b y ∈ Icc (0 : ℝ) 1) ∧
        (∀ᵐ x ∂loebMeasure U hU,
          (0 < boundedRealFunction U f 1 hf x → 0 < a ((countableUltralimitHom U F).rangeRestrict x)) ∧
          (0 < boundedRealFunction U g 1 hg x → 0 < b ((countableUltralimitHom U F).rangeRestrict x))) ∧
        (∫ y, a y ∂Measure.map (countableUltralimitHom U F).rangeRestrict (loebMeasure U hU)) =
            ∫ x, boundedRealFunction U f 1 hf x ∂loebMeasure U hU ∧
        (∫ y, b y ∂Measure.map (countableUltralimitHom U F).rangeRestrict (loebMeasure U hU)) =
            ∫ x, boundedRealFunction U g 1 hg x ∂loebMeasure U hU ∧
        (fun x => ∫ t, boundedRealFunction U f 1 hf t *
          boundedRealFunction U g 1 hg (x - t) ∂loebMeasure U hU) =ᵐ[loebMeasure U hU]
            (fun x => ∫ t, a t * b ((countableUltralimitHom U F).rangeRestrict x - t)
              ∂Measure.map (countableUltralimitHom U F).rangeRestrict (loebMeasure U hU)) := by
  let μ := loebMeasure (X := X) U hU
  letI : IsProbabilityMeasure μ := isProbabilityMeasure_loebMeasure U hU
  have hfc (n : ℕ) (x : X n) : ‖(f n x : ℂ)‖ ≤ 1 := by
    simpa only [Complex.norm_real, Real.norm_eq_abs] using hf n x
  have hgc (n : ℕ) (x : X n) : ‖(g n x : ℂ)‖ ≤ 1 := by
    simpa only [Complex.norm_real, Real.norm_eq_abs] using hg n x
  obtain ⟨F, Q, hQ, hcompact, hhaar, hrepC⟩ :=
    exists_compact_convolution_factor U hU (fun n x => (f n x : ℂ))
      (fun n x => (g n x : ℂ)) hfc hgc
  letI : CompactSpace (countableUltralimitHom U F).range := isCompact_iff_compactSpace.mp hcompact
  let q := (countableUltralimitHom U F).rangeRestrict
  let ν := Measure.map q μ
  have hq : Measurable q := (measurable_countableUltralimitHom U F).subtype_mk
  obtain ⟨a, ha, harange, hA, hasupport, hamass⟩ :=
    exists_unitInterval_conditional_factor μ q hq (boundedRealFunction U f 1 hf)
      (integrable_boundedRealFunction U hU f 1 hf)
      (ae_of_all μ (boundedRealFunction_mem_Icc U f 1 0 1 hf hfpos))
  obtain ⟨b, hb, hbrange, hB, hbsupport, hbmass⟩ :=
    exists_unitInterval_conditional_factor μ q hq (boundedRealFunction U g 1 hg)
      (integrable_boundedRealFunction U hU g 1 hg)
      (ae_of_all μ (boundedRealFunction_mem_Icc U g 1 0 1 hg hgpos))
  have hrep : (fun x => ∫ t, (boundedRealFunction U f 1 hf t : ℂ) *
      (boundedRealFunction U g 1 hg (x - t) : ℂ) ∂μ) =ᵐ[μ] Q ∘ q := by
    filter_upwards [hrepC] with x hx
    simpa only [boundedComplexFunction_ofReal U f 1 hf hfc,
      boundedComplexFunction_ofReal U g 1 hg hgc] using hx
  have hprojection := loeb_convolution_projection U hU f g hf hg F a b Q ha hb hQ
    (fun y => ⟨harange y, hbrange y⟩) hA hB hrep
  have hpull := ae_of_ae_map hq.aemeasurable hprojection
  refine ⟨F, a, b, hcompact, hhaar, ha, hb,
    (fun y => ⟨harange y, hbrange y⟩), ?_, hamass, hbmass, ?_⟩
  · filter_upwards [hasupport, hbsupport] with x ha hb
    exact ⟨ha, hb⟩
  · filter_upwards [hrep, hpull] with x hr hp
    have he := hr.trans hp
    change (∫ t, (boundedRealFunction U f 1 hf t : ℂ) *
      (boundedRealFunction U g 1 hg (x - t) : ℂ) ∂μ) =
        ∫ t, (a t : ℂ) * (b (q x - t) : ℂ) ∂ν at he
    simp_rw [← Complex.ofReal_mul, integral_complex_ofReal] at he
    exact Complex.ofReal_injective he

end Erdos335.Loeb

end
