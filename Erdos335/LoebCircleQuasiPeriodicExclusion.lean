import Erdos335.LoebCircleSubgroupMeasure
import Erdos335.LoebEqualityPeriod
import Erdos335.QuasiPeriodicSets

/-!
# Proper circle pullbacks exclude a quasi-periodic background
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter MeasureTheory
open scoped Pointwise ENNReal

noncomputable section

namespace Erdos335.Loeb

local instance circleQuasiExclusionLoebSpace (U : Ultrafilter ℕ) (q : ℕ → ℕ+) :
    MeasurableSpace ((U : Filter ℕ).Product (fun n => ZMod (q n : ℕ))) := loebMeasurableSpace U

theorem circle_pullback_quasiPeriodic_background_empty
    (U : Ultrafilter ℕ) (hU : (U : Filter ℕ) ≤ atTop) (q : ℕ → ℕ+)
    (φ : (U : Filter ℕ).Product (fun n => ZMod (q n : ℕ)) →+ AddCircle (1 : ℝ))
    (hφ : Measurable φ) (hsurj : Function.Surjective φ)
    (H : AddSubgroup ((U : Filter ℕ).Product (fun n => ZMod (q n : ℕ))))
    (hH : MeasurableSet (H : Set ((U : Filter ℕ).Product (fun n => ZMod (q n : ℕ)))))
    (hHpos : 0 < loebMeasure U hU (H : Set ((U : Filter ℕ).Product (fun n => ZMod (q n : ℕ)))))
    (C : Set (AddCircle (1 : ℝ))) (hC : MeasurableSet C) (hClt : (volume C).toReal < 1)
    (p : QuasiPeriodicDecomposition (loebMeasure U hU) H (φ ⁻¹' C)) :
    ¬ p.background.Nonempty := by
  have : Fact (0 < (1 : ℝ)) := ⟨zero_lt_one⟩
  let μ := loebMeasure (X := fun n => ZMod (q n : ℕ)) U hU
  have : IsProbabilityMeasure μ := isProbabilityMeasure_loebMeasure U hU
  rintro ⟨a, ha⟩
  have hfull := loeb_measure_section_eq_of_essential_period U hU H p.background
    p.background_measurable p.background_periodic a ha
  have hsubset : p.background ⊆ φ ⁻¹' C := subset_union_left.trans p.partition.ge
  have hle : μ (H : Set _) ≤ μ (φ ⁻¹' C ∩ (a +ᵥ (H : Set _))) := by
    rw [← hfull]
    exact measure_mono (inter_subset_inter_left _ hsubset)
  rw [loeb_circle_coset_intersection_measure U hU q φ hφ hsurj H hH hHpos C hC a] at hle
  have hreal := ENNReal.toReal_mono
    (ENNReal.mul_ne_top (measure_ne_top μ _) (measure_ne_top volume _)) hle
  rw [ENNReal.toReal_mul] at hreal
  have hpositive : 0 < (μ (H : Set _)).toReal :=
    ENNReal.toReal_pos hHpos.ne' (measure_ne_top μ _)
  nlinarith

theorem not_quasiPeriodic_pair_of_proper_circle_pullbacks
    (U : Ultrafilter ℕ) (hU : (U : Filter ℕ) ≤ atTop) (q : ℕ → ℕ+)
    (φ : (U : Filter ℕ).Product (fun n => ZMod (q n : ℕ)) →+ AddCircle (1 : ℝ))
    (hφ : Measurable φ) (hsurj : Function.Surjective φ)
    (C D : Set (AddCircle (1 : ℝ))) (hC : MeasurableSet C) (hD : MeasurableSet D)
    (hClt : (volume C).toReal < 1) (hDlt : (volume D).toReal < 1) :
    ¬ Nonempty (QuasiPeriodicPairData (loebMeasure U hU) (internalInnerMeasure U hU)
      (φ ⁻¹' C) (φ ⁻¹' D)) := by
  rintro ⟨p⟩
  rcases p.nonempty_background with hleft | hright
  · exact circle_pullback_quasiPeriodic_background_empty U hU q φ hφ hsurj
      p.period p.period_measurable p.period_positive C hC hClt p.left hleft
  · exact circle_pullback_quasiPeriodic_background_empty U hU q φ hφ hsurj
      p.period p.period_measurable p.period_positive D hD hDlt p.right hright

end Erdos335.Loeb

end
