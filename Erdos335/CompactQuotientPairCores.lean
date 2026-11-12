import Erdos335.CompactStabilizerQuotient
import Erdos335.CompactSigmaProfileCores
import Erdos335.CompactProfilePeriods
import Erdos335.QuotientSetAlgebra

/-!
# Compatible compact cores for a quotient pair

Invariant measurable representatives and positive convolution cores give
quotient inputs whose lifted sum is exactly the sum of the chosen cores.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Filter Set MeasureTheory
open scoped Pointwise ENNReal

noncomputable section

namespace Erdos335.Loeb

theorem exists_quotient_pair_cores
    {G K : Type*} [AddCommGroup G] [AddCommGroup K]
    [TopologicalSpace G] [TopologicalSpace K] [IsTopologicalAddGroup G]
    [CompactSpace G] [T2Space G] [T2Space K]
    [MeasurableSpace G] [MeasurableSpace K] [BorelSpace G] [BorelSpace K]
    [MeasurableAdd₂ G] [MeasurableNeg G]
    (μ : Measure G) [IsFiniteMeasure μ] [μ.InnerRegularCompactLTTop]
    [μ.IsAddLeftInvariant] [μ.IsNegInvariant] [μ.IsOpenPosMeasure]
    (φ : G →+ K) (hφ : Continuous φ)
    (A B : Set G) (hAm : MeasurableSet A) (hBm : MeasurableSet B)
    (hAperiod : ∀ h ∈ φ.ker, h +ᵥ A =ᵐ[μ] A)
    (hBperiod : ∀ h ∈ φ.ker, h +ᵥ B =ᵐ[μ] B) :
    ∃ P Q : Set G, IsSigmaCompact P ∧ IsSigmaCompact Q ∧
      MeasurableSet P ∧ MeasurableSet Q ∧ P ⊆ A ∧ Q ⊆ B ∧
      μ P = μ A ∧ μ Q = μ B ∧
      φ ⁻¹' (φ '' P) =ᵐ[μ] A ∧ φ ⁻¹' (φ '' Q) =ᵐ[μ] B ∧
      φ ⁻¹' ((φ '' P) + (φ '' Q)) = P + Q := by
  have hclosed : IsClosed (φ.ker : Set G) := by
    change IsClosed (φ ⁻¹' ({0} : Set K))
    exact isClosed_singleton.preimage hφ
  have : CompactSpace φ.ker := isCompact_iff_compactSpace.mp hclosed.isCompact
  have : MeasurableAdd₂ φ.ker := ⟨by
    exact ((measurable_subtype_coe.comp measurable_fst).add
      (measurable_subtype_coe.comp measurable_snd)).subtype_mk⟩
  obtain ⟨ν, hνprob, hνhaar⟩ := exists_compact_addHaar_probability φ.ker
  have : IsProbabilityMeasure ν := hνprob
  have : Measure.IsAddHaarMeasure ν := hνhaar
  obtain ⟨A₀, hA₀m, hA₀ae, hA₀period⟩ := exists_exact_invariant_ae_set μ ν φ.ker.subtype
    continuous_subtype_val.measurable A hAm (fun h => hAperiod h h.property)
  obtain ⟨B₀, hB₀m, hB₀ae, hB₀period⟩ := exists_exact_invariant_ae_set μ ν φ.ker.subtype
    continuous_subtype_val.measurable B hBm (fun h => hBperiod h h.property)
  let A₁ := A ∩ A₀
  let B₁ := B ∩ B₀
  have hA₁m : MeasurableSet A₁ := hAm.inter hA₀m
  have hB₁m : MeasurableSet B₁ := hBm.inter hB₀m
  have hA₁ae : A₁ =ᵐ[μ] A := by
    filter_upwards [hA₀ae] with x hx
    change (x ∈ A ∧ x ∈ A₀) = (x ∈ A)
    rw [hx]
    simp
  have hB₁ae : B₁ =ᵐ[μ] B := by
    filter_upwards [hB₀ae] with x hx
    change (x ∈ B ∧ x ∈ B₀) = (x ∈ B)
    rw [hx]
    simp
  obtain ⟨P, D, hPsc, hDsc, hPm, hDm, hPA₁, hDnegB₁, hPmass, hDmass, hregular⟩ :=
    exists_sigmaCompact_positive_intersection_cores μ A₁ (-B₁) hA₁m hB₁m.neg
  let Q := -D
  have hQsc : IsSigmaCompact Q := by
    simpa only [image_neg_eq_neg] using hDsc.image continuous_neg
  have hQm : MeasurableSet Q := hDm.neg
  have hQB₁ : Q ⊆ B₁ := by
    intro q hq
    have h := hDnegB₁ hq
    change -(-q) ∈ B₁ at h
    simpa only [neg_neg] using h
  have hPA : P ⊆ A := hPA₁.trans inter_subset_left
  have hQB : Q ⊆ B := hQB₁.trans inter_subset_left
  have hPA₀ : P ⊆ A₀ := hPA₁.trans inter_subset_right
  have hQB₀ : Q ⊆ B₀ := hQB₁.trans inter_subset_right
  have hPmassA : μ P = μ A := hPmass.trans (measure_congr hA₁ae)
  have hQmassB : μ Q = μ B := by
    change μ (-D) = μ B
    rw [Measure.measure_neg, hDmass, Measure.measure_neg, measure_congr hB₁ae]
  have hPpreM : MeasurableSet (φ ⁻¹' (φ '' P)) :=
    (measurableSet_of_sigmaCompact _ (hPsc.image hφ)).preimage hφ.measurable
  have hQpreM : MeasurableSet (φ ⁻¹' (φ '' Q)) :=
    (measurableSet_of_sigmaCompact _ (hQsc.image hφ)).preimage hφ.measurable
  have hPpreA₀ : φ ⁻¹' (φ '' P) ⊆ A₀ :=
    preimage_image_subset_of_ker_invariant φ P A₀ hPA₀
      (fun h hh => hA₀period ⟨h, hh⟩)
  have hQpreB₀ : φ ⁻¹' (φ '' Q) ⊆ B₀ :=
    preimage_image_subset_of_ker_invariant φ Q B₀ hQB₀
      (fun h hh => hB₀period ⟨h, hh⟩)
  have hPpreAe : φ ⁻¹' (φ '' P) =ᵐ[μ] A := by
    apply Filter.EventuallyEq.trans _ hA₀ae
    apply ae_eq_of_subset_of_measure_ge hPpreA₀ _ hPpreM.nullMeasurableSet
      (measure_ne_top μ A₀)
    rw [measure_congr hA₀ae, ← hPmassA]
    exact measure_mono (subset_preimage_image φ P)
  have hQpreAe : φ ⁻¹' (φ '' Q) =ᵐ[μ] B := by
    apply Filter.EventuallyEq.trans _ hB₀ae
    apply ae_eq_of_subset_of_measure_ge hQpreB₀ _ hQpreM.nullMeasurableSet
      (measure_ne_top μ B₀)
    rw [measure_congr hB₀ae, ← hQmassB]
    exact measure_mono (subset_preimage_image φ Q)
  have hA₁period : ∀ h ∈ φ.ker, h +ᵥ A₁ =ᵐ[μ] A₁ := by
    intro h hh
    exact ((vadd_set_ae_eq h).2 hA₁ae).trans ((hAperiod h hh).trans hA₁ae.symm)
  have hPQperiod : ∀ h ∈ φ.ker, h +ᵥ (P + Q) = P + Q := by
    intro h hh
    change h +ᵥ (P + (-D)) = P + (-D)
    rw [hregular]
    exact positive_intersection_support_periodic μ A₁ (-B₁) φ.ker hA₁period h hh
  exact ⟨P, Q, hPsc, hQsc, hPm, hQm, hPA, hQB, hPmassA, hQmassB,
    hPpreAe, hQpreAe, preimage_image_add_eq_of_ker_invariant φ P Q hPQperiod⟩

end Erdos335.Loeb

end
