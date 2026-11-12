import Erdos335.LoebInnerSplit
import Erdos335.LoebSolidAbsorption

/-!
# Absorption above a full-inner-measure periodic core

A measurable subset of an extension contributes no measure outside a
measurable core of full inner measure. For solid summands, this gives a
literal containment after saturation by the core's period.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Filter Set Topology MeasureTheory
open scoped ENNReal Pointwise

noncomputable section

namespace Erdos335.Loeb

variable {X : ℕ → Type*} [∀ n, AddCommGroup (X n)] [∀ n, Fintype (X n)]

local instance innerAbsorptionLoebSpace (U : Ultrafilter ℕ) :
    MeasurableSpace ((U : Filter ℕ).Product X) := loebMeasurableSpace U

theorem loeb_measure_sdiff_zero_of_full_inner
    (U : Ultrafilter ℕ) (hU : (U : Filter ℕ) ≤ atTop)
    (S C D : Set ((U : Filter ℕ).Product X))
    (hCm : MeasurableSet C) (hDm : MeasurableSet D)
    (hCS : C ⊆ S) (hDS : D ⊆ S)
    (hfull : internalInnerMeasure U hU S = loebMeasure U hU C) :
    loebMeasure U hU (D \ C) = 0 := by
  let μ := loebMeasure (X := X) U hU
  letI : IsProbabilityMeasure μ := isProbabilityMeasure_loebMeasure U hU
  have hsplit := internalInnerMeasure_eq_add_sdiff U hU S C hCm hCS
  have hinnerzero : internalInnerMeasure U hU (S \ C) = 0 := by
    apply le_antisymm
    · apply (ENNReal.add_le_add_iff_left (measure_ne_top μ C)).mp
      simpa only [add_zero] using hsplit.symm.le.trans hfull.le
    · exact bot_le
  have hle : μ (D \ C) ≤ internalInnerMeasure U hU (S \ C) := by
    rw [← internalInnerMeasure_eq U hU (D \ C) (hDm.diff hCm)]
    exact internalInnerMeasure_mono U hU (sdiff_subset_sdiff_left hDS)
  exact le_antisymm (hle.trans_eq hinnerzero) bot_le

theorem loeb_solid_extension_add_subset
    (U : Ultrafilter ℕ) (hU : (U : Filter ℕ) ≤ atTop)
    (H : AddSubgroup ((U : Filter ℕ).Product X))
    (A B C S : Set ((U : Filter ℕ).Product X))
    (hBm : MeasurableSet B) (hCm : MeasurableSet C)
    (hCS : C ⊆ S) (hAB : A + B ⊆ S)
    (hfull : internalInnerMeasure U hU S = loebMeasure U hU C)
    (hperiod : C + (H : Set ((U : Filter ℕ).Product X)) = C)
    (hsolid : ∀ b ∈ B,
      0 < loebMeasure U hU (B ∩ (b +ᵥ (H : Set ((U : Filter ℕ).Product X))))) :
    A + (B + (H : Set ((U : Filter ℕ).Product X))) ⊆ C := by
  rintro x ⟨a, ha, b, hb, rfl⟩
  have hDm : MeasurableSet ((fun y => a + y) '' B) := by
    have heq : (fun y => a + y) '' B = (fun y => -a + y) ⁻¹' B := by
      ext y
      constructor
      · rintro ⟨z, hz, rfl⟩
        simpa only [mem_preimage, neg_add_cancel_left] using hz
      · intro hy
        exact ⟨-a + y, hy, by simp⟩
    rw [heq]
    exact hBm.preimage (measurable_add_left U hU (-a))
  have hDS : (fun y => a + y) '' B ⊆ S := by
    rintro y ⟨z, hz, rfl⟩
    exact hAB (add_mem_add ha hz)
  have hzero := loeb_measure_sdiff_zero_of_full_inner U hU S C
    ((fun y => a + y) '' B) hCm hDm hCS hDS hfull
  exact loeb_solid_translate_absorption U hU H B C a hperiod hsolid hzero ⟨b, hb, rfl⟩

end Erdos335.Loeb

end
