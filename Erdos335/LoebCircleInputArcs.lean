import Erdos335.LoebCircleComplementArc
import Erdos335.CircleArcComplement

/-!
# Closed-arc models for both inputs in a circle factor
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter MeasureTheory
open scoped Pointwise ENNReal

noncomputable section

namespace Erdos335.Loeb

def UnitCircleClosedArcModel (C : Set (AddCircle (1 : ℝ))) : Prop :=
  ∃ c a b : ℝ, a < b ∧ b - a < 1 ∧
    (-(c : AddCircle (1 : ℝ)) +ᵥ C) =ᵐ[volume]
      (((↑) : ℝ → AddCircle (1 : ℝ)) '' Icc a b)

theorem unitCircle_closedArcModel_of_complement_arc
    (C : Set (AddCircle (1 : ℝ))) (c a b : ℝ) (hab : a < b) (hwidth : b - a < 1)
    (hC : (-(c : AddCircle (1 : ℝ)) +ᵥ Cᶜ) =ᵐ[volume]
      (((↑) : ℝ → AddCircle (1 : ℝ)) '' Ioo a b)) :
    UnitCircleClosedArcModel C := by
  have hclosed := unitCircle_complement_ae_closedArc Cᶜ (-(c : AddCircle (1 : ℝ))) a b
    hab (by linarith) hC
  refine ⟨c, b, a + 1, by linarith, by linarith, ?_⟩
  simpa only [compl_compl] using hclosed

local instance circleInputArcsLoebSpace (U : Ultrafilter ℕ) (q : ℕ → ℕ+) :
    MeasurableSpace ((U : Filter ℕ).Product (fun n => ZMod (q n : ℕ))) := loebMeasurableSpace U

theorem loeb_unitCircle_pair_ae_closedArcs
    (U : Ultrafilter ℕ) (hU : (U : Filter ℕ) ≤ atTop) (q : ℕ → ℕ+)
    (φ : (U : Filter ℕ).Product (fun n => ZMod (q n : ℕ)) →+ AddCircle (1 : ℝ))
    (hφ : Measurable φ) (hsurj : Function.Surjective φ)
    (C D : Set (AddCircle (1 : ℝ)))
    (hC : MeasurableSet C) (hD : MeasurableSet D) (hS : MeasurableSet (C + D))
    (hCpos : 0 < volume C) (hDpos : 0 < volume D)
    (hcomp : 0 < loebMeasure U hU ((φ ⁻¹' C) + (φ ⁻¹' D))ᶜ)
    (hfull : loebMeasure U hU ((φ ⁻¹' C) + (φ ⁻¹' D)) =
      loebMeasure U hU (φ ⁻¹' C) + loebMeasure U hU (φ ⁻¹' D))
    (hirr : MeasureIrreducible (loebMeasure U hU) (internalInnerMeasure U hU)
      (φ ⁻¹' C) (φ ⁻¹' D))
    (hne : MeasureNonextendible (loebMeasure U hU) (internalInnerMeasure U hU)
      (φ ⁻¹' C) (φ ⁻¹' D))
    (hnoAE : ∀ H : AddSubgroup ((U : Filter ℕ).Product (fun n => ZMod (q n : ℕ))),
      MeasurableSet (H : Set ((U : Filter ℕ).Product (fun n => ZMod (q n : ℕ)))) →
      0 < loebMeasure (X := fun n => ZMod (q n : ℕ)) U hU (H : Set _) →
      ¬ ∀ t ∈ H, t +ᵥ ((φ ⁻¹' C) + (φ ⁻¹' D)) =ᵐ[loebMeasure U hU]
        (φ ⁻¹' C) + (φ ⁻¹' D))
    (hperiod : ∀ z : AddCircle (1 : ℝ), z +ᵥ (C + D) =ᵐ[volume] C + D → z = 0) :
    UnitCircleClosedArcModel C ∧ UnitCircleClosedArcModel D := by
  obtain ⟨c, a, b, _, hab, _, hwidth, hArcC⟩ := loeb_unitCircle_complement_ae_arc U hU q φ hφ hsurj
    C D hC hD hS hCpos hDpos hcomp hfull hirr hne hnoAE hperiod
  have hmodelC := unitCircle_closedArcModel_of_complement_arc C c a b hab hwidth hArcC
  have hSswap : MeasurableSet (D + C) := by simpa only [add_comm D C] using hS
  have hcompSwap : 0 < loebMeasure U hU ((φ ⁻¹' D) + (φ ⁻¹' C))ᶜ := by
    simpa only [add_comm] using hcomp
  have hfullSwap : loebMeasure U hU ((φ ⁻¹' D) + (φ ⁻¹' C)) =
      loebMeasure U hU (φ ⁻¹' D) + loebMeasure U hU (φ ⁻¹' C) := by
    simpa only [add_comm] using hfull
  have hnoAESwap : ∀ H : AddSubgroup ((U : Filter ℕ).Product (fun n => ZMod (q n : ℕ))),
      MeasurableSet (H : Set ((U : Filter ℕ).Product (fun n => ZMod (q n : ℕ)))) →
      0 < loebMeasure (X := fun n => ZMod (q n : ℕ)) U hU (H : Set _) →
      ¬ ∀ t ∈ H, t +ᵥ ((φ ⁻¹' D) + (φ ⁻¹' C)) =ᵐ[loebMeasure U hU]
        (φ ⁻¹' D) + (φ ⁻¹' C) := by
    simpa only [add_comm] using hnoAE
  have hperiodSwap : ∀ z : AddCircle (1 : ℝ), z +ᵥ (D + C) =ᵐ[volume] D + C → z = 0 := by
    simpa only [add_comm D C] using hperiod
  obtain ⟨d, u, v, _, huv, _, hwidthD, hArcD⟩ := loeb_unitCircle_complement_ae_arc U hU q φ hφ hsurj
    D C hD hC hSswap hDpos hCpos hcompSwap hfullSwap hirr.swap hne.swap hnoAESwap hperiodSwap
  exact ⟨hmodelC, unitCircle_closedArcModel_of_complement_arc D d u v huv hwidthD hArcD⟩

end Erdos335.Loeb

end
