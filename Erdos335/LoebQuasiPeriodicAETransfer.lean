import Erdos335.LoebQuasiPeriodicRestriction
import Erdos335.LoebQuasiPeriodicCoreLift

/-!
# Transferring measurable quasi-periodic models through null changes

An irreducible equality pair that agrees almost everywhere with a
measurable quasi-periodic equality pair has a finite essential period or
a quasi-periodic decomposition. Empty restricted active pieces lead to
the periodic case.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Filter Set Topology MeasureTheory
open scoped Pointwise ENNReal

noncomputable section

namespace Erdos335.Loeb

theorem essential_periodic_subset_of_null_difference
    {G : Type*} [AddCommGroup G] [MeasurableSpace G]
    (μ : Measure G) (H : AddSubgroup G) (C P : Set G)
    (hCP : C ⊆ P) (hnull : μ (P \ C) = 0)
    (hperiod : μ ((P + (H : Set G)) \ P) = 0) :
    μ ((C + (H : Set G)) \ C) = 0 := by
  have hsub : ((C + (H : Set G)) \ C) ⊆
      ((P + (H : Set G)) \ P) ∪ (P \ C) := by
    rintro x ⟨hx, hxC⟩
    by_cases hxP : x ∈ P
    · exact Or.inr ⟨hxP, hxC⟩
    · exact Or.inl ⟨add_subset_add hCP Subset.rfl hx, hxP⟩
  apply measure_mono_null hsub
  apply nonpos_iff_eq_zero.mp
  calc
    μ (((P + (H : Set G)) \ P) ∪ (P \ C)) ≤
        μ ((P + (H : Set G)) \ P) + μ (P \ C) := measure_union_le _ _
    _ = 0 := by rw [hperiod, hnull, add_zero]

theorem QuasiPeriodicDecomposition.empty_active_restriction_period
    {G : Type*} [AddCommGroup G] [MeasurableSpace G]
    {μ : Measure G} {H : AddSubgroup G} {P : Set G}
    (p : QuasiPeriodicDecomposition μ H P) (C : Set G)
    (hCP : C ⊆ P) (hnull : μ (P \ C) = 0)
    (hempty : ¬ (p.active ∩ C).Nonempty) :
    μ ((C + (H : Set G)) \ C) = 0 := by
  have hCbg : C ⊆ p.background := by
    intro x hx
    have hxP := hCP hx
    rw [p.partition] at hxP
    exact hxP.elim id (fun ha => False.elim (hempty ⟨x, ha, hx⟩))
  apply essential_periodic_subset_of_null_difference μ H C p.background hCbg _ p.background_periodic
  exact measure_mono_null (sdiff_subset_sdiff_left (subset_union_left.trans p.partition.ge)) hnull

local instance quasiPeriodicTransferLoebSpace (U : Ultrafilter ℕ) (q : ℕ → ℕ+) :
    MeasurableSpace ((U : Filter ℕ).Product (fun n => ZMod (q n : ℕ))) := loebMeasurableSpace U

theorem loeb_irreducible_quasiPeriodic_ae_transfer
    (U : Ultrafilter ℕ) (hU : (U : Filter ℕ) ≤ atTop) (q : ℕ → ℕ+)
    (A B P Q : Set ((U : Filter ℕ).Product (fun n => ZMod (q n : ℕ))))
    (p : QuasiPeriodicPairData (loebMeasure U hU) (internalInnerMeasure U hU) P Q)
    (hAm : MeasurableSet A) (hBm : MeasurableSet B)
    (hApos : 0 < loebMeasure U hU A) (hBpos : 0 < loebMeasure U hU B)
    (hAP : A =ᵐ[loebMeasure U hU] P) (hBQ : B =ᵐ[loebMeasure U hU] Q)
    (hPQm : MeasurableSet (P + Q))
    (hirr : MeasureIrreducible (loebMeasure U hU) (internalInnerMeasure U hU) A B)
    (hfull : internalInnerMeasure U hU (A + B) = loebMeasure U hU A + loebMeasure U hU B)
    (hmodel : internalInnerMeasure U hU (P + Q) = loebMeasure U hU P + loebMeasure U hU Q) :
    (∃ H : AddSubgroup ((U : Filter ℕ).Product (fun n => ZMod (q n : ℕ))),
      MeasurableSet (H : Set ((U : Filter ℕ).Product (fun n => ZMod (q n : ℕ)))) ∧
      0 < loebMeasure (X := fun n => ZMod (q n : ℕ)) U hU (H : Set _) ∧
      (A + B) + (H : Set _) =ᵐ[loebMeasure U hU] A + B) ∨
      Nonempty (QuasiPeriodicPairData (loebMeasure U hU) (internalInnerMeasure U hU) A B) := by
  classical
  let G := (U : Filter ℕ).Product (fun n => ZMod (q n : ℕ))
  let μ := loebMeasure (X := fun n => ZMod (q n : ℕ)) U hU
  let C := A ∩ P
  let D := B ∩ Q
  have hPm : MeasurableSet P := p.left.partition.symm ▸
    (p.left.background_measurable.union p.left.active_measurable)
  have hQm : MeasurableSet Q := p.right.partition.symm ▸
    (p.right.background_measurable.union p.right.active_measurable)
  have hCm : MeasurableSet C := hAm.inter hPm
  have hDm : MeasurableSet D := hBm.inter hQm
  have hCA : C =ᵐ[μ] A := by
    filter_upwards [hAP] with x hx
    change (x ∈ A ∧ x ∈ P) = (x ∈ A)
    rw [← hx]
    exact and_self _
  have hDB : D =ᵐ[μ] B := by
    filter_upwards [hBQ] with x hx
    change (x ∈ B ∧ x ∈ Q) = (x ∈ B)
    rw [← hx]
    exact and_self _
  have hCP : C =ᵐ[μ] P := hCA.trans hAP
  have hDQ : D =ᵐ[μ] Q := hDB.trans hBQ
  have hCAmeasure : μ C = μ A := measure_congr hCA
  have hDBmeasure : μ D = μ B := measure_congr hDB
  have hcore : internalInnerMeasure U hU (C + D) = internalInnerMeasure U hU (A + B) :=
    hirr C D hCm hDm inter_subset_left inter_subset_left hCAmeasure hDBmeasure
  have hcoreFull : internalInnerMeasure U hU (C + D) = μ (P + Q) := by
    rw [hcore, hfull, ← internalInnerMeasure_eq U hU _ hPQm, hmodel,
      ← measure_congr hAP, ← measure_congr hBQ]
  obtain ⟨hCDm, hSumeq⟩ := measurable_of_subset_full_inner U hU (C + D) (P + Q)
    (add_subset_add inter_subset_right inter_subset_right) hPQm hcoreFull
  have hperiodic (hperiod : (C + D) + (p.period : Set G) =ᵐ[μ] C + D) :
      (∃ H : AddSubgroup G, MeasurableSet (H : Set G) ∧ 0 < μ (H : Set G) ∧
        (A + B) + (H : Set G) =ᵐ[μ] A + B) ∨
        Nonempty (QuasiPeriodicPairData μ (internalInnerMeasure U hU) A B) := by
    obtain ⟨K, hKm, hKpos, hcase⟩ := loeb_irreducible_extension_of_periodic_core U hU q
      p.period C D A B p.period_measurable p.period_positive hCm hDm hAm hBm hApos hBpos
      inter_subset_left inter_subset_left hCAmeasure.symm hDBmeasure.symm hirr hfull hperiod
    rcases hcase with hperiod | ⟨r, _, _⟩
    · exact Or.inl ⟨K, hKm, hKpos, hperiod⟩
    · exact Or.inr ⟨r⟩
  by_cases hleft : (p.left.active ∩ C).Nonempty
  · by_cases hright : (p.right.active ∩ D).Nonempty
    · obtain ⟨r, _, _, _⟩ := loeb_quasiPeriodic_full_restriction U hU q P Q C D p
        hCm hDm inter_subset_right inter_subset_right hCP hDQ hPQm hCDm hSumeq hleft hright
      exact loeb_irreducible_extension_of_quasiPeriodic_core U hU q C D A B r
        hAm hBm hApos hBpos inter_subset_left inter_subset_left hCAmeasure.symm hDBmeasure.symm
        hirr hCDm hfull
    · have hDperiod := p.right.empty_active_restriction_period D inter_subset_right
        (ae_le_set.mp hDQ.ge) hright
      exact hperiodic (loeb_sum_with_essentially_periodic_summand U hU q p.period
        p.period_measurable p.period_positive C D hDperiod).2
  · have hCperiod := p.left.empty_active_restriction_period C inter_subset_right
      (ae_le_set.mp hCP.ge) hleft
    apply hperiodic
    simpa only [add_comm D C] using (loeb_sum_with_essentially_periodic_summand U hU q p.period
      p.period_measurable p.period_positive D C hCperiod).2

end Erdos335.Loeb

end
