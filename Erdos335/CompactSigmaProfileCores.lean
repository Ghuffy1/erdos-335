import Erdos335.CompactProfileRegularization
import Erdos335.CompactSigmaRepresentatives

/-!
# Sigma-compact cores realizing the positive intersection profile
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Filter Set MeasureTheory
open scoped Pointwise ENNReal

noncomputable section

namespace Erdos335.Loeb

theorem exists_sigmaCompact_positive_intersection_cores
    {G : Type*} [AddCommGroup G] [TopologicalSpace G] [IsTopologicalAddGroup G]
    [T2Space G] [MeasurableSpace G] [BorelSpace G] [MeasurableAdd₂ G] [MeasurableNeg G]
    (μ : Measure G) [IsFiniteMeasure μ] [μ.InnerRegularCompactLTTop]
    [μ.IsAddLeftInvariant] [μ.IsNegInvariant] [μ.IsOpenPosMeasure]
    (A B : Set G) (hA : MeasurableSet A) (hB : MeasurableSet B) :
    ∃ C D : Set G, IsSigmaCompact C ∧ IsSigmaCompact D ∧
      MeasurableSet C ∧ MeasurableSet D ∧ C ⊆ A ∧ D ⊆ B ∧ μ C = μ A ∧ μ D = μ B ∧
      C + (-D) = {e | 0 < compactIntersectionProfile μ A B e} := by
  obtain ⟨A₀, B₀, hA₀m, hB₀m, hA₀A, hB₀B, hA₀mass, hB₀mass, hregular⟩ :=
    exists_full_measure_positive_intersection_cores μ A B hA hB
  obtain ⟨C, hCA₀, hCsc, hCm, hCmass⟩ := exists_full_measure_sigmaCompact_subset μ A₀ hA₀m
  obtain ⟨D, hDB₀, hDsc, hDm, hDmass⟩ := exists_full_measure_sigmaCompact_subset μ B₀ hB₀m
  have hCA := hCA₀.trans hA₀A
  have hDB := hDB₀.trans hB₀B
  have hCeq : μ C = μ A := hCmass.trans hA₀mass
  have hDeq : μ D = μ B := hDmass.trans hB₀mass
  have hA₀ae : A₀ =ᵐ[μ] A := ae_eq_of_subset_of_measure_ge hA₀A hA₀mass.ge
    hA₀m.nullMeasurableSet (measure_ne_top μ A)
  have hB₀ae : B₀ =ᵐ[μ] B := ae_eq_of_subset_of_measure_ge hB₀B hB₀mass.ge
    hB₀m.nullMeasurableSet (measure_ne_top μ B)
  have hCae : C =ᵐ[μ] A := ae_eq_of_subset_of_measure_ge hCA hCeq.ge
    hCm.nullMeasurableSet (measure_ne_top μ A)
  have hDae : D =ᵐ[μ] B := ae_eq_of_subset_of_measure_ge hDB hDeq.ge
    hDm.nullMeasurableSet (measure_ne_top μ B)
  refine ⟨C, D, hCsc, hDsc, hCm, hDm, hCA, hDB, hCeq, hDeq, ?_⟩
  apply subset_antisymm
  · intro e he
    have hsub : C + (-D) ⊆ A₀ + (-B₀) := add_subset_add hCA₀ (neg_subset_neg.mpr hDB₀)
    have hpos := hsub he
    rw [hregular] at hpos
    change 0 < compactIntersectionProfile μ A₀ B₀ e at hpos
    rwa [compactIntersectionProfile_congr_ae μ A₀ A B₀ B hA₀ae hB₀ae] at hpos
  · intro e he
    apply compactIntersectionProfile_positive_support_subset μ C D
    change 0 < compactIntersectionProfile μ C D e
    rwa [compactIntersectionProfile_congr_ae μ C A D B hCae hDae]

end Erdos335.Loeb

end
