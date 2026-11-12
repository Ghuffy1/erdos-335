import Erdos335.IrreducibleInputPeriod
import Erdos335.LoebCompactSumTransfer
import Erdos335.StabilizerPullback

/-!
# Individual input periods in an irreducible compact factor
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter MeasureTheory
open scoped Pointwise

noncomputable section

namespace Erdos335.Loeb

local instance compactInputAperiodicityLoebSpace (U : Ultrafilter ℕ) (q : ℕ → ℕ+) :
    MeasurableSpace ((U : Filter ℕ).Product (fun n => ZMod (q n : ℕ))) := loebMeasurableSpace U

theorem compact_factor_irreducible_sum_ae_period_of_left
    (U : Ultrafilter ℕ) (hU : (U : Filter ℕ) ≤ atTop) (q : ℕ → ℕ+)
    {K : Type*} [AddCommGroup K] [MeasurableSpace K] [MeasurableAdd₂ K]
    (φ : (U : Filter ℕ).Product (fun n => ZMod (q n : ℕ)) →+ K)
    (hφ : Measurable φ) (hsurj : Function.Surjective φ)
    (C D : Set K) (hC : MeasurableSet C) (hD : MeasurableSet D)
    (hS : MeasurableSet (C + D))
    (hirr : MeasureIrreducible (loebMeasure U hU) (internalInnerMeasure U hU)
      (φ ⁻¹' C) (φ ⁻¹' D))
    (t : K) (hperiod : t +ᵥ C =ᵐ[Measure.map φ (loebMeasure U hU)] C) :
    t +ᵥ (C + D) =ᵐ[Measure.map φ (loebMeasure U hU)] C + D := by
  let G := (U : Filter ℕ).Product (fun n => ZMod (q n : ℕ))
  let μ := loebMeasure (X := fun n => ZMod (q n : ℕ)) U hU
  have : IsProbabilityMeasure μ := isProbabilityMeasure_loebMeasure U hU
  have : MeasurableAdd G := {
    measurable_const_add := measurable_add_left U hU
    measurable_add_const := fun c => by
      simpa only [add_comm] using measurable_add_left U hU c }
  have : μ.IsAddLeftInvariant := ⟨fun e => loebMeasure_map_add_left U hU e⟩
  obtain ⟨e, rfl⟩ := hsurj t
  have hpre : φ ⁻¹' (φ e +ᵥ C) =ᵐ[μ] φ ⁻¹' C :=
    ae_of_ae_map hφ.aemeasurable hperiod
  rw [preimage_vadd_addHom] at hpre
  have hSm : MeasurableSet ((φ ⁻¹' C) + (φ ⁻¹' D)) := by
    rw [← preimage_add_of_surjective_addHom φ hsurj C D]
    exact hS.preimage hφ
  have hresult := MeasureIrreducible.sum_ae_period_of_left μ (internalInnerMeasure U hU)
    (fun _ _ h => internalInnerMeasure_mono U hU h)
    (fun S hSm => internalInnerMeasure_eq U hU S hSm)
    (φ ⁻¹' C) (φ ⁻¹' D) (hC.preimage hφ) (hD.preimage hφ) hSm hirr e hpre
  have htranslate : MeasurableSet (φ e +ᵥ (C + D)) := by
    rw [vadd_set_eq_neg_preimage]
    exact hS.preimage (measurable_const.add measurable_id)
  apply ae_map_set_eq_of_preimage μ φ hφ _ _ htranslate hS
  rw [preimage_vadd_addHom, preimage_add_of_surjective_addHom φ hsurj C D]
  exact hresult

theorem compact_factor_left_aperiodic_of_sum_aperiodic
    (U : Ultrafilter ℕ) (hU : (U : Filter ℕ) ≤ atTop) (q : ℕ → ℕ+)
    {K : Type*} [AddCommGroup K] [MeasurableSpace K] [MeasurableAdd₂ K]
    (φ : (U : Filter ℕ).Product (fun n => ZMod (q n : ℕ)) →+ K)
    (hφ : Measurable φ) (hsurj : Function.Surjective φ)
    (C D : Set K) (hC : MeasurableSet C) (hD : MeasurableSet D)
    (hS : MeasurableSet (C + D))
    (hirr : MeasureIrreducible (loebMeasure U hU) (internalInnerMeasure U hU)
      (φ ⁻¹' C) (φ ⁻¹' D))
    (hperiod : ∀ t : K, t +ᵥ (C + D) =ᵐ[Measure.map φ (loebMeasure U hU)] C + D → t = 0) :
    ∀ t : K, t +ᵥ C =ᵐ[Measure.map φ (loebMeasure U hU)] C → t = 0 := by
  intro t ht
  exact hperiod t (compact_factor_irreducible_sum_ae_period_of_left U hU q φ hφ hsurj
    C D hC hD hS hirr t ht)

end Erdos335.Loeb

end
