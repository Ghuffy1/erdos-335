import Erdos335.LoebInnerAbsorption
import Erdos335.LoebFullSaturations
import Erdos335.LoebCompletionCoset
import Erdos335.LoebSparseCoset

/-!
# Lifting a periodic full-measure core

These lemmas isolate the full-inner-measure and completion steps used in
the periodic-core branch of Griesmer's Lemma 10.12.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Filter Set Topology MeasureTheory
open scoped ENNReal Pointwise

noncomputable section

namespace Erdos335.Loeb

local instance periodicCoreLoebSpace (U : Ultrafilter ℕ) (q : ℕ → ℕ+) :
    MeasurableSpace ((U : Filter ℕ).Product (fun n => ZMod (q n : ℕ))) := loebMeasurableSpace U

theorem loeb_essential_period_of_full_inner_subset
    (U : Ultrafilter ℕ) (hU : (U : Filter ℕ) ≤ atTop) (q : ℕ → ℕ+)
    (H : AddSubgroup ((U : Filter ℕ).Product (fun n => ZMod (q n : ℕ))))
    (S C : Set ((U : Filter ℕ).Product (fun n => ZMod (q n : ℕ))))
    (hSC : S ⊆ C) (hfull : internalInnerMeasure U hU S = loebMeasure U hU C)
    (hperiod : C + (H : Set _) = C) :
    S + (H : Set _) =ᵐ[loebMeasure U hU] S := by
  have hzero := loebMeasure_sdiff_eq_zero_of_full_inner U hU S C hSC hfull
  have hsaturated : S + (H : Set _) ⊆ C := by
    intro x hx
    rw [← hperiod]
    exact add_subset_add hSC (show (H : Set _) ⊆ H from Subset.rfl) hx
  have hzero' : loebMeasure U hU ((S + (H : Set _)) \ S) = 0 :=
    measure_mono_null (sdiff_subset_sdiff_left hsaturated) hzero
  have hback : S ⊆ S + (H : Set _) := by
    intro x hx
    exact ⟨x, hx, 0, H.zero_mem, add_zero x⟩
  exact (ae_le_set.mpr hzero').antisymm hback.eventuallySubset

theorem loeb_periodic_core_extensions_absorbed
    (U : Ultrafilter ℕ) (hU : (U : Filter ℕ) ≤ atTop) (q : ℕ → ℕ+)
    (H : AddSubgroup ((U : Filter ℕ).Product (fun n => ZMod (q n : ℕ))))
    (Acore Bcore A B : Set ((U : Filter ℕ).Product (fun n => ZMod (q n : ℕ))))
    (hHm : MeasurableSet (H : Set ((U : Filter ℕ).Product (fun n => ZMod (q n : ℕ)))))
    (hHpos : 0 < loebMeasure (X := fun n => ZMod (q n : ℕ)) U hU (H : Set _))
    (hAcorem : MeasurableSet Acore) (hBcorem : MeasurableSet Bcore)
    (hAsub : Acore ⊆ A) (hBsub : Bcore ⊆ B)
    (hAperiod : loebMeasure U hU ((Acore + (H : Set _)) \ Acore) = 0)
    (hBperiod : loebMeasure U hU ((Bcore + (H : Set _)) \ Bcore) = 0)
    (hfull : internalInnerMeasure U hU (A + B) = loebMeasure U hU (Acore + Bcore)) :
    A + (Bcore + (H : Set _)) ⊆ Acore + Bcore ∧
      (Acore + (H : Set _)) + B ⊆ Acore + Bcore := by
  let G := (U : Filter ℕ).Product (fun n => ZMod (q n : ℕ))
  let μ := loebMeasure (X := fun n => ZMod (q n : ℕ)) U hU
  letI : IsProbabilityMeasure μ := isProbabilityMeasure_loebMeasure U hU
  have hAmass := loeb_measure_saturation_eq_of_essential_period U hU H Acore hAcorem hAperiod
  have hBmass := loeb_measure_saturation_eq_of_essential_period U hU H Bcore hBcorem hBperiod
  have hdeficit : μ (Acore + (H : Set G)) + μ (Bcore + (H : Set G)) <
      μ Acore + μ Bcore + μ (H : Set G) := by
    rw [hAmass, hBmass]
    exact ENNReal.lt_add_right (by finiteness) hHpos.ne'
  have hperiod := loeb_add_periodic_of_saturated_deficit U hU H hHm Acore Bcore hBcorem hdeficit
  have hCm : MeasurableSet (Acore + Bcore) := by
    rw [← hperiod]
    exact measurable_saturation_of_positive_subgroup U hU q H hHm hHpos (Acore + Bcore)
  have hCS : Acore + Bcore ⊆ A + B := add_subset_add hAsub hBsub
  have hBsolid : ∀ b ∈ Bcore, 0 < μ (Bcore ∩ (b +ᵥ (H : Set G))) := by
    intro b hb
    rw [loeb_measure_section_eq_of_essential_period U hU H Bcore hBcorem hBperiod b hb]
    exact hHpos
  have hAsolid : ∀ a ∈ Acore, 0 < μ (Acore ∩ (a +ᵥ (H : Set G))) := by
    intro a ha
    rw [loeb_measure_section_eq_of_essential_period U hU H Acore hAcorem hAperiod a ha]
    exact hHpos
  have hleft := loeb_solid_extension_add_subset U hU H A Bcore (Acore + Bcore) (A + B)
    hBcorem hCm hCS (add_subset_add Subset.rfl hBsub) hfull hperiod hBsolid
  have hcross : B + Acore ⊆ A + B := by
    simpa only [add_comm] using (add_subset_add hAsub (show B ⊆ B from Subset.rfl))
  have hright := loeb_solid_extension_add_subset U hU H B Acore (Acore + Bcore) (A + B)
    hAcorem hCm hCS hcross hfull hperiod hAsolid
  exact ⟨hleft, by simpa only [add_comm] using hright⟩

theorem loeb_periodic_completion_one_coset
    (U : Ultrafilter ℕ) (hU : (U : Filter ℕ) ≤ atTop) (q : ℕ → ℕ+)
    (H : AddSubgroup ((U : Filter ℕ).Product (fun n => ZMod (q n : ℕ))))
    (P Q A : Set ((U : Filter ℕ).Product (fun n => ZMod (q n : ℕ))))
    (hPm : MeasurableSet P) (hQm : MeasurableSet Q) (hCm : MeasurableSet (P + Q))
    (hPpos : 0 < loebMeasure U hU P) (hQpos : 0 < loebMeasure U hU Q)
    (hle : loebMeasure U hU (P + Q) ≤ loebMeasure U hU P + loebMeasure U hU Q)
    (hHm : MeasurableSet (H : Set ((U : Filter ℕ).Product (fun n => ZMod (q n : ℕ)))))
    (hHpos : 0 < loebMeasure (X := fun n => ZMod (q n : ℕ)) U hU (H : Set _))
    (hH : H = AddAction.stabilizer ((U : Filter ℕ).Product (fun n => ZMod (q n : ℕ))) (P + Q))
    (hPperiod : P + (H : Set _) = P) (hA : A + Q ⊆ P + Q) :
    A ⊆ P ∨ ∃ a ∉ P, A ⊆ P ∪ (a +ᵥ (H : Set _)) := by
  have hcompletion : A ⊆ {x | x +ᵥ Q ⊆ P + Q} := by
    intro a ha y hy
    obtain ⟨b, hb, rfl⟩ := hy
    exact hA (add_mem_add ha hb)
  have hcases := loeb_completion_at_most_one_coset U hU q P Q hPm hQm hCm hPpos hQpos hle
  dsimp only at hcases
  rw [← hH] at hcases
  specialize hcases hHm hHpos
  rw [hPperiod] at hcases
  rcases hcases with hsame | ⟨a, ha, heq⟩
  · exact Or.inl (hsame ▸ hcompletion)
  · exact Or.inr ⟨a, ha, heq ▸ hcompletion⟩

end Erdos335.Loeb

end
