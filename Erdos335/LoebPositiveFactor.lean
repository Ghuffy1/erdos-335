import Erdos335.LoebConvolutionRepresentation
import Erdos335.LoebConditionalFactor
import Erdos335.LoebPositiveInputs

/-!
# Positive input functions on a common compact factor

Both conditional input functions take values in the unit interval and retain
their masses and positive supports. The same compact factor carries the
original Loeb convolution. Identifying that last representative with the
convolution of the conditional input functions requires a further argument.
-/

set_option autoImplicit false

open Filter Set Topology MeasureTheory

noncomputable section

namespace Erdos335.Loeb

local instance : MeasurableSpace (Additive Circle) := borel (Additive Circle)
local instance : BorelSpace (Additive Circle) := ⟨rfl⟩

theorem exists_compact_real_convolution_factor
    {X : ℕ → Type*} [∀ n, AddCommGroup (X n)] [∀ n, Fintype (X n)]
    (U : Ultrafilter ℕ) (hU : (U : Filter ℕ) ≤ atTop)
    (f g : ∀ n, X n → ℝ) (hf : ∀ n x, |f n x| ≤ 1) (hg : ∀ n x, |g n x| ≤ 1) :
    ∃ F : ℕ → ∀ n, X n →+ Additive Circle,
      ∃ H : (countableUltralimitHom U F).range → ℝ,
        StronglyMeasurable H ∧
        IsCompact ((countableUltralimitHom U F).range : Set (ℕ → Additive Circle)) ∧
        Measure.IsAddHaarMeasure
          (@Measure.map _ _ (loebMeasurableSpace U) _
            (countableUltralimitHom U F).rangeRestrict (loebMeasure U hU)) ∧
        (fun x => ∫ t, boundedRealFunction U f 1 hf t *
          boundedRealFunction U g 1 hg (x - t) ∂loebMeasure U hU) =ᵐ[loebMeasure U hU]
            H ∘ (countableUltralimitHom U F).rangeRestrict := by
  have hfc (n : ℕ) (x : X n) : ‖(f n x : ℂ)‖ ≤ 1 := by
    simpa only [Complex.norm_real, Real.norm_eq_abs] using hf n x
  have hgc (n : ℕ) (x : X n) : ‖(g n x : ℂ)‖ ≤ 1 := by
    simpa only [Complex.norm_real, Real.norm_eq_abs] using hg n x
  obtain ⟨F, Q, hQ, hcompact, hhaar, heq⟩ :=
    exists_compact_convolution_factor U hU (fun n x => (f n x : ℂ))
      (fun n x => (g n x : ℂ)) hfc hgc
  refine ⟨F, (fun y => (Q y).re), Complex.continuous_re.comp_stronglyMeasurable hQ,
    hcompact, hhaar, ?_⟩
  filter_upwards [heq] with x hx
  have hr := congrArg Complex.re hx
  rw [boundedReal_complex_convolution U hU f g 1 1 hf hg hfc hgc x] at hr
  simpa only [Complex.ofReal_re, Function.comp_apply] using hr

theorem exists_compact_positive_input_factor
    {X : ℕ → Type*} [∀ n, AddCommGroup (X n)] [∀ n, Fintype (X n)]
    (U : Ultrafilter ℕ) (hU : (U : Filter ℕ) ≤ atTop)
    (f g : ∀ n, X n → ℝ) (hf : ∀ n x, |f n x| ≤ 1) (hg : ∀ n x, |g n x| ≤ 1)
    (hfpos : ∀ n x, f n x ∈ Icc (0 : ℝ) 1)
    (hgpos : ∀ n x, g n x ∈ Icc (0 : ℝ) 1) :
    ∃ F : ℕ → ∀ n, X n →+ Additive Circle,
      ∃ a b H : (countableUltralimitHom U F).range → ℝ,
        IsCompact ((countableUltralimitHom U F).range : Set (ℕ → Additive Circle)) ∧
        Measure.IsAddHaarMeasure
          (@Measure.map _ _ (loebMeasurableSpace U) _
            (countableUltralimitHom U F).rangeRestrict (loebMeasure U hU)) ∧
        StronglyMeasurable a ∧ StronglyMeasurable b ∧ StronglyMeasurable H ∧
        (∀ y, a y ∈ Icc (0 : ℝ) 1 ∧ b y ∈ Icc (0 : ℝ) 1) ∧
        (∀ᵐ x ∂loebMeasure U hU,
          (0 < boundedRealFunction U f 1 hf x → 0 < a ((countableUltralimitHom U F).rangeRestrict x)) ∧
          (0 < boundedRealFunction U g 1 hg x → 0 < b ((countableUltralimitHom U F).rangeRestrict x))) ∧
        (∫ y, a y ∂@Measure.map _ _ (loebMeasurableSpace U) _
          (countableUltralimitHom U F).rangeRestrict (loebMeasure U hU)) =
            ∫ x, boundedRealFunction U f 1 hf x ∂loebMeasure U hU ∧
        (∫ y, b y ∂@Measure.map _ _ (loebMeasurableSpace U) _
          (countableUltralimitHom U F).rangeRestrict (loebMeasure U hU)) =
            ∫ x, boundedRealFunction U g 1 hg x ∂loebMeasure U hU ∧
        (fun x => ∫ t, boundedRealFunction U f 1 hf t *
          boundedRealFunction U g 1 hg (x - t) ∂loebMeasure U hU) =ᵐ[loebMeasure U hU]
            H ∘ (countableUltralimitHom U F).rangeRestrict := by
  let : MeasurableSpace ((U : Filter ℕ).Product X) := loebMeasurableSpace U
  let μ := loebMeasure (X := X) U hU
  letI : IsProbabilityMeasure μ := isProbabilityMeasure_loebMeasure U hU
  obtain ⟨F, H, hH, hcompact, hhaar, heq⟩ :=
    exists_compact_real_convolution_factor U hU f g hf hg
  let q := (countableUltralimitHom U F).rangeRestrict
  have hq : Measurable q := (measurable_countableUltralimitHom U F).subtype_mk
  obtain ⟨a, ha, harange, _, hasupport, hamass⟩ :=
    exists_unitInterval_conditional_factor μ q hq (boundedRealFunction U f 1 hf)
      (integrable_boundedRealFunction U hU f 1 hf)
      (ae_of_all μ (boundedRealFunction_mem_Icc U f 1 0 1 hf hfpos))
  obtain ⟨b, hb, hbrange, _, hbsupport, hbmass⟩ :=
    exists_unitInterval_conditional_factor μ q hq (boundedRealFunction U g 1 hg)
      (integrable_boundedRealFunction U hU g 1 hg)
      (ae_of_all μ (boundedRealFunction_mem_Icc U g 1 0 1 hg hgpos))
  refine ⟨F, a, b, H, hcompact, hhaar, ha, hb, hH,
    (fun y => ⟨harange y, hbrange y⟩), ?_, hamass, hbmass, heq⟩
  filter_upwards [hasupport, hbsupport] with x ha hb
  exact ⟨ha, hb⟩

end Erdos335.Loeb

end
