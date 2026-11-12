import Erdos335.LoebNonextendiblePeriods
import Erdos335.LoebCompactSumTransfer
import Erdos335.StabilizerPullback

/-!
# Input periods in a compact factor of a nonextendible Loeb pair
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Filter Set MeasureTheory
open scoped Pointwise

noncomputable section

namespace Erdos335.Loeb

local instance compactInputPeriodsLoebSpace (U : Ultrafilter ℕ) (q : ℕ → ℕ+) :
    MeasurableSpace ((U : Filter ℕ).Product (fun n => ZMod (q n : ℕ))) := loebMeasurableSpace U

theorem compact_factor_nonextendible_inputs_ae_period
    (U : Ultrafilter ℕ) (hU : (U : Filter ℕ) ≤ atTop) (q : ℕ → ℕ+)
    {K : Type*} [AddCommGroup K] [MeasurableSpace K] [MeasurableAdd₂ K]
    (φ : (U : Filter ℕ).Product (fun n => ZMod (q n : ℕ)) →+ K)
    (hφ : Measurable φ) (hsurj : Function.Surjective φ)
    (C D : Set K) (hC : MeasurableSet C) (hD : MeasurableSet D)
    (hne : MeasureNonextendible (loebMeasure U hU) (internalInnerMeasure U hU)
      (φ ⁻¹' C) (φ ⁻¹' D))
    (t : K) (hperiod : t +ᵥ (C + D) =ᵐ[Measure.map φ (loebMeasure U hU)] C + D) :
    (t +ᵥ C =ᵐ[Measure.map φ (loebMeasure U hU)] C) ∧
      (t +ᵥ D =ᵐ[Measure.map φ (loebMeasure U hU)] D) := by
  obtain ⟨e, rfl⟩ := hsurj t
  have hpre : φ ⁻¹' (φ e +ᵥ (C + D)) =ᵐ[loebMeasure U hU] φ ⁻¹' (C + D) :=
    ae_of_ae_map hφ.aemeasurable hperiod
  rw [preimage_vadd_addHom, preimage_add_of_surjective_addHom φ hsurj] at hpre
  obtain ⟨hleft, hright⟩ := loeb_nonextendible_inputs_ae_period U hU (φ ⁻¹' C) (φ ⁻¹' D)
    (hC.preimage hφ) (hD.preimage hφ) hne e hpre
  have hleftm : MeasurableSet (φ e +ᵥ C) := by
    rw [vadd_set_eq_neg_preimage]
    exact hC.preimage (measurable_const.add measurable_id)
  have hrightm : MeasurableSet (φ e +ᵥ D) := by
    rw [vadd_set_eq_neg_preimage]
    exact hD.preimage (measurable_const.add measurable_id)
  constructor
  · apply ae_map_set_eq_of_preimage (loebMeasure U hU) φ hφ (φ e +ᵥ C) C hleftm hC
    rw [preimage_vadd_addHom]
    exact hleft
  · apply ae_map_set_eq_of_preimage (loebMeasure U hU) φ hφ (φ e +ᵥ D) D hrightm hD
    rw [preimage_vadd_addHom]
    exact hright

end Erdos335.Loeb

end
