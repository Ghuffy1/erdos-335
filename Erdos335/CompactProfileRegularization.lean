import Erdos335.CompactIntersectionProfile
import Erdos335.CompactIndicatorRegularization

/-!
# Full-measure cores with positive intersection profiles

This supplies the translate-intersection regularization in Griesmer's
Lemma 5.21 by applying the existing local-density construction to A and -B.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Filter Set Topology MeasureTheory
open scoped Pointwise ENNReal

noncomputable section

namespace Erdos335.Loeb

variable {G : Type*} [AddCommGroup G] [TopologicalSpace G] [IsTopologicalAddGroup G]
variable [T2Space G] [MeasurableSpace G] [BorelSpace G]
variable [MeasurableAdd₂ G] [MeasurableNeg G]

omit [T2Space G] [MeasurableAdd₂ G] [MeasurableNeg G] in
theorem compactIntersectionProfile_congr_ae
    (μ : Measure G) [μ.IsAddLeftInvariant]
    (A A' B B' : Set G) (hA : A =ᵐ[μ] A') (hB : B =ᵐ[μ] B') (e : G) :
    compactIntersectionProfile μ A B e = compactIntersectionProfile μ A' B' e := by
  have hshift := (measurePreserving_add_left μ (-e)).quasiMeasurePreserving.ae hB
  apply congrArg ENNReal.toReal
  apply measure_congr
  rw [vadd_set_eq_neg_preimage B e, vadd_set_eq_neg_preimage B' e]
  filter_upwards [hA, hshift] with x hx hxe
  change (x ∈ A ∧ -e + x ∈ B) = (x ∈ A' ∧ -e + x ∈ B')
  rw [hx, hxe]

theorem exists_full_measure_positive_intersection_cores
    (μ : Measure G) [IsFiniteMeasure μ] [μ.InnerRegularCompactLTTop]
    [μ.IsAddLeftInvariant] [μ.IsNegInvariant] [μ.IsOpenPosMeasure]
    (A B : Set G) (hA : MeasurableSet A) (hB : MeasurableSet B) :
    ∃ A' B' : Set G, MeasurableSet A' ∧ MeasurableSet B' ∧
      A' ⊆ A ∧ B' ⊆ B ∧ μ A' = μ A ∧ μ B' = μ B ∧
      A' + (-B') = {e | 0 < compactIntersectionProfile μ A' B' e} := by
  classical
  obtain ⟨A', C', hA'm, hC'm, hA'A, hC'B, hA'mass, hC'mass, hpos⟩ :=
    exists_full_measure_indicator_representatives μ A (-B) hA hB.neg
  let B' := -C'
  have hB'm : MeasurableSet B' := hC'm.neg
  have hB'B : B' ⊆ B := by
    intro b hb
    have h := hC'B hb
    change -(-b) ∈ B at h
    simpa only [neg_neg] using h
  have hB'mass : μ B' = μ B := by
    dsimp [B']
    rw [Measure.measure_neg, hC'mass, Measure.measure_neg]
  have hAae : A' =ᵐ[μ] A := ae_eq_of_subset_of_measure_ge hA'A hA'mass.ge
    hA'm.nullMeasurableSet (measure_ne_top μ A)
  have hBae : B' =ᵐ[μ] B := ae_eq_of_subset_of_measure_ge hB'B hB'mass.ge
    hB'm.nullMeasurableSet (measure_ne_top μ B)
  refine ⟨A', B', hA'm, hB'm, hA'A, hB'B, hA'mass, hB'mass, ?_⟩
  apply subset_antisymm
  · rintro e ⟨a, ha, c, hc, rfl⟩
    have hc' : c ∈ C' := by simpa only [B', neg_neg] using hc
    have hpositive := hpos a ha c hc'
    rw [indicator_convolution_eq_intersectionProfile μ A B hA hB] at hpositive
    change 0 < compactIntersectionProfile μ A' B' (a + c)
    rwa [compactIntersectionProfile_congr_ae μ A' A B' B hAae hBae]
  · exact compactIntersectionProfile_positive_support_subset μ A' B'

end Erdos335.Loeb

end
