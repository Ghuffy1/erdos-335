import Erdos335.CompactDysonStep
import Erdos335.CompactProfileRegularization
import Erdos335.LoebIrreducibleCore
import Erdos335.LoebCompactEqualityReduction
import Erdos335.LoebEnvelopeStabilizer
import Erdos335.LoebTranslationStructure

/-!
# A shrinking parameter without a regularization hypothesis

Full-measure compact cores have positive overlap at every represented
difference. Irreducibility transfers aperiodicity to their pullbacks.
The shrinking parameter for the cores has the same overlap measure for
the original inputs.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Filter Set Topology MeasureTheory
open scoped Pointwise ENNReal

noncomputable section

namespace Erdos335.Loeb

local instance compactShrinkingLoebSpace (U : Ultrafilter ℕ) (q : ℕ → ℕ+) :
    MeasurableSpace ((U : Filter ℕ).Product (fun n => ZMod (q n : ℕ))) := loebMeasurableSpace U

theorem exists_shrinking_parameter_in_irreducible_compact_factor
    (U : Ultrafilter ℕ) (hU : (U : Filter ℕ) ≤ atTop) (q : ℕ → ℕ+)
    {K : Type*} [AddCommGroup K] [TopologicalSpace K] [IsTopologicalAddGroup K]
    [CompactSpace K] [T2Space K] [PolishSpace K]
    [MeasurableSpace K] [BorelSpace K] [MeasurableAdd₂ K] [MeasurableNeg K]
    (φ : (U : Filter ℕ).Product (fun n => ZMod (q n : ℕ)) →+ K)
    (hφ : Measurable φ) (hsurj : Function.Surjective φ)
    (C D : Set K) (hCm : MeasurableSet C) (hDm : MeasurableSet D) (hCDm : MeasurableSet (C + D))
    (hCpos : 0 < Measure.map φ (loebMeasure U hU) C)
    (hDpos : 0 < Measure.map φ (loebMeasure U hU) D)
    (htotal : (Measure.map φ (loebMeasure U hU) C).toReal +
      (Measure.map φ (loebMeasure U hU) D).toReal ≤ 1)
    (hirr : MeasureIrreducible (loebMeasure U hU) (internalInnerMeasure U hU) (φ ⁻¹' C) (φ ⁻¹' D))
    (hnoAE : ∀ H : AddSubgroup ((U : Filter ℕ).Product (fun n => ZMod (q n : ℕ))),
      MeasurableSet (H : Set ((U : Filter ℕ).Product (fun n => ZMod (q n : ℕ)))) →
      0 < loebMeasure (X := fun n => ZMod (q n : ℕ)) U hU (H : Set _) →
      ¬ ∀ t ∈ H, t +ᵥ ((φ ⁻¹' C) + (φ ⁻¹' D)) =ᵐ[loebMeasure U hU] (φ ⁻¹' C) + (φ ⁻¹' D)) :
    ∃ e : K, 0 < (Measure.map φ (loebMeasure U hU) (dysonGroupRight C D e)).toReal ∧
      (Measure.map φ (loebMeasure U hU) (dysonGroupRight C D e)).toReal ≤
        (1 - (Measure.map φ (loebMeasure U hU) D).toReal) *
          (Measure.map φ (loebMeasure U hU) D).toReal := by
  let G := (U : Filter ℕ).Product (fun n => ZMod (q n : ℕ))
  let μ := loebMeasure (X := fun n => ZMod (q n : ℕ)) U hU
  let ν := Measure.map φ μ
  have : IsProbabilityMeasure μ := isProbabilityMeasure_loebMeasure U hU
  have : IsProbabilityMeasure ν := ⟨by
    change Measure.map φ μ univ = 1
    rw [Measure.map_apply hφ MeasurableSet.univ]
    simp⟩
  have : Measure.IsAddHaarMeasure ν := loebMeasure_map_hom_isAddHaarMeasure U hU φ hφ hsurj
  have : ν.IsNegInvariant := loebMeasure_map_hom_isNegInvariant U hU q φ hφ
  obtain ⟨C₀, D₀, hC₀m, hD₀m, hC₀C, hD₀D, hC₀mass, hD₀mass, hregular⟩ :=
    exists_full_measure_positive_intersection_cores ν C D hCm hDm
  let A := φ ⁻¹' C
  let B := φ ⁻¹' D
  let P := φ ⁻¹' C₀
  let Q := φ ⁻¹' D₀
  have hAm : MeasurableSet A := hCm.preimage hφ
  have hBm : MeasurableSet B := hDm.preimage hφ
  have hPm : MeasurableSet P := hC₀m.preimage hφ
  have hQm : MeasurableSet Q := hD₀m.preimage hφ
  have hSm : MeasurableSet (A + B) := by
    rw [← preimage_add_of_surjective_addHom φ hsurj C D]
    exact hCDm.preimage hφ
  have hPA : P ⊆ A := preimage_mono hC₀C
  have hQB : Q ⊆ B := preimage_mono hD₀D
  have hPmass : μ P = μ A := by
    change μ (φ ⁻¹' C₀) = μ (φ ⁻¹' C)
    rw [← Measure.map_apply hφ hC₀m, ← Measure.map_apply hφ hCm]
    exact hC₀mass
  have hQmass : μ Q = μ B := by
    change μ (φ ⁻¹' D₀) = μ (φ ⁻¹' D)
    rw [← Measure.map_apply hφ hD₀m, ← Measure.map_apply hφ hDm]
    exact hD₀mass
  have hinner : internalInnerMeasure U hU (P + Q) = μ (A + B) :=
    (hirr P Q hPm hQm hPA hQB hPmass hQmass).trans (internalInnerMeasure_eq U hU _ hSm)
  obtain ⟨_, hPQae⟩ := measurable_of_subset_full_inner U hU (P + Q) (A + B)
    (add_subset_add hPA hQB) hSm hinner
  have hnotexact : ¬ ∃ H : AddSubgroup G, MeasurableSet (H : Set G) ∧ 0 < μ (H : Set G) ∧
      (P + Q) + (H : Set G) = P + Q := by
    rintro ⟨H, hHm, hHpos, hp⟩
    apply hnoAE H hHm hHpos
    intro t ht
    have hfix : t +ᵥ (P + Q) = P + Q := subgroup_le_stabilizer_of_add_eq H (P + Q) hp ht
    have h := loeb_vadd_congr_ae U hU (A + B) (P + Q) t hPQae.symm
    rw [hfix] at h
    exact h.trans hPQae
  have hC₀pos : 0 < ν C₀ := hC₀mass.symm ▸ hCpos
  have hD₀pos : 0 < ν D₀ := hD₀mass.symm ▸ hDpos
  have htotal₀ : (ν C₀).toReal + (ν D₀).toReal ≤ 1 := by rwa [hC₀mass, hD₀mass]
  obtain ⟨e, hepos, hebound⟩ := exists_shrinking_step_in_loeb_compact_quotient U hU q φ hφ hsurj
    C₀ D₀ hC₀m hD₀m hC₀pos hD₀pos htotal₀ hregular hnotexact
  have hCae : C₀ =ᵐ[ν] C := ae_eq_of_subset_of_measure_ge hC₀C hC₀mass.symm.le
    hC₀m.nullMeasurableSet (measure_ne_top ν C)
  have hDae : D₀ =ᵐ[ν] D := ae_eq_of_subset_of_measure_ge hD₀D hD₀mass.symm.le
    hD₀m.nullMeasurableSet (measure_ne_top ν D)
  have hstep : (ν (dysonGroupRight C₀ D₀ e)).toReal = (ν (dysonGroupRight C D e)).toReal := by
    rw [← compactIntersectionProfile_eq_dysonMeasure ν C₀ D₀ e,
      ← compactIntersectionProfile_eq_dysonMeasure ν C D e]
    exact compactIntersectionProfile_congr_ae ν C₀ C D₀ D hCae hDae e
  rw [hstep] at hepos hebound
  rw [hD₀mass] at hebound
  exact ⟨e, hepos, hebound⟩

end Erdos335.Loeb

end
