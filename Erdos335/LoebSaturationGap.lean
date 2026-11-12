import Erdos335.LoebInverseIteration

/-!
# A positive saturation gap terminates quasi-periodic refinement

The measure gained by saturating a quasi-periodic input is at most the
measure of its period. A uniform positive lower bound on that gain
therefore excludes an infinite sequence of smaller periods.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter MeasureTheory
open scoped ENNReal Pointwise

noncomputable section

namespace Erdos335.Loeb

local instance saturationGapLoebSpace (U : Ultrafilter ℕ) (q : ℕ → ℕ+) :
    MeasurableSpace ((U : Filter ℕ).Product (fun n => ZMod (q n : ℕ))) := loebMeasurableSpace U

theorem loeb_quasiPeriodic_input_saturation_bound
    (U : Ultrafilter ℕ) (hU : (U : Filter ℕ) ≤ atTop) (q : ℕ → ℕ+)
    (A : Set ((U : Filter ℕ).Product (fun n => ZMod (q n : ℕ))))
    (H : AddSubgroup ((U : Filter ℕ).Product (fun n => ZMod (q n : ℕ))))
    (p : QuasiPeriodicDecomposition (loebMeasure U hU) H A) :
    loebMeasure U hU (A + (H : Set _)) ≤ loebMeasure U hU A +
      loebMeasure U hU (H : Set ((U : Filter ℕ).Product (fun n => ZMod (q n : ℕ)))) := by
  let G := (U : Filter ℕ).Product (fun n => ZMod (q n : ℕ))
  let μ := loebMeasure (X := fun n => ZMod (q n : ℕ)) U hU
  have hback : p.background ⊆ p.background + (H : Set G) :=
    fun x hx => ⟨x, hx, 0, H.zero_mem, add_zero x⟩
  have hbg : p.background + (H : Set G) =ᵐ[μ] p.background :=
    (ae_le_set.mpr p.background_periodic).antisymm hback.eventuallySubset
  have hsub : p.background ⊆ A := subset_union_left.trans p.partition.ge
  calc
    μ (A + (H : Set G)) = μ ((p.background + (H : Set G)) ∪
        (p.anchor +ᵥ (H : Set G))) := by
      conv_lhs => rw [p.partition]
      rw [union_add, p.active_add_period]
    _ ≤ μ (p.background + (H : Set G)) + μ (p.anchor +ᵥ (H : Set G)) :=
      measure_union_le _ _
    _ = μ p.background + μ (H : Set G) := by
      rw [measure_congr hbg, loebMeasure_coset U hU H p.anchor]
    _ ≤ μ A + μ (H : Set G) := add_le_add (measure_mono hsub) le_rfl

theorem loeb_quasiPeriodic_period_bound_of_saturation_gap
    (U : Ultrafilter ℕ) (hU : (U : Filter ℕ) ≤ atTop) (q : ℕ → ℕ+)
    (A : Set ((U : Filter ℕ).Product (fun n => ZMod (q n : ℕ))))
    (H : AddSubgroup ((U : Filter ℕ).Product (fun n => ZMod (q n : ℕ))))
    (p : QuasiPeriodicDecomposition (loebMeasure U hU) H A)
    (δ : ℝ)
    (hgap : δ ≤ (loebMeasure U hU (A + (H : Set _))).toReal -
      (loebMeasure U hU A).toReal) :
    δ ≤ (loebMeasure U hU (H : Set ((U : Filter ℕ).Product (fun n => ZMod (q n : ℕ))))).toReal := by
  let μ := loebMeasure (X := fun n => ZMod (q n : ℕ)) U hU
  have : IsProbabilityMeasure μ := isProbabilityMeasure_loebMeasure U hU
  have hbound := loeb_quasiPeriodic_input_saturation_bound U hU q A H p
  have hreal := ENNReal.toReal_mono (by finiteness : μ A + μ (H : Set _) ≠ ∞) hbound
  rw [ENNReal.toReal_add (measure_ne_top μ _) (measure_ne_top μ _)] at hreal
  linarith

theorem loeb_irreducible_inverse_of_saturation_gap
    (U : Ultrafilter ℕ) (hU : (U : Filter ℕ) ≤ atTop) (q : ℕ → ℕ+)
    (A B : Set ((U : Filter ℕ).Product (fun n => ZMod (q n : ℕ))))
    (hAm : MeasurableSet A) (hBm : MeasurableSet B) (hSm : MeasurableSet (A + B))
    (hApos : 0 < loebMeasure U hU A) (hBpos : 0 < loebMeasure U hU B)
    (hfull : loebMeasure U hU (A + B) = loebMeasure U hU A + loebMeasure U hU B)
    (hirr : MeasureIrreducible (loebMeasure U hU) (internalInnerMeasure U hU) A B)
    (hnoAE : ∀ H : AddSubgroup ((U : Filter ℕ).Product (fun n => ZMod (q n : ℕ))),
      MeasurableSet (H : Set ((U : Filter ℕ).Product (fun n => ZMod (q n : ℕ)))) →
      0 < loebMeasure U hU (H : Set ((U : Filter ℕ).Product (fun n => ZMod (q n : ℕ)))) →
      ¬ ∀ t ∈ H, t +ᵥ (A + B) =ᵐ[loebMeasure U hU] A + B)
    (δ : ℝ) (hδ : 0 < δ)
    (hgap : ∀ H : AddSubgroup ((U : Filter ℕ).Product (fun n => ZMod (q n : ℕ))),
      MeasurableSet (H : Set ((U : Filter ℕ).Product (fun n => ZMod (q n : ℕ)))) →
      0 < loebMeasure U hU (H : Set ((U : Filter ℕ).Product (fun n => ZMod (q n : ℕ)))) →
      δ ≤ (loebMeasure U hU (A + (H : Set _))).toReal - (loebMeasure U hU A).toReal) :
    Nonempty (InternalBohrPairData U hU q A B) ∨
      ∃ p : QuasiPeriodicPairData (loebMeasure U hU) (internalInnerMeasure U hU) A B,
        Nonempty (InternalBohrPairData U hU q p.left.active p.right.active) := by
  rcases loeb_irreducible_aperiodic_inverse_alternative U hU q A B hAm hBm hSm
    hApos hBpos hfull hirr hnoAE with hdirect | hterminal | hsmall
  · exact Or.inl hdirect
  · exact Or.inr hterminal
  · obtain ⟨p, hp⟩ := hsmall δ hδ
    have hbound := loeb_quasiPeriodic_period_bound_of_saturation_gap U hU q A p.period
      p.left δ (hgap p.period p.period_measurable p.period_positive)
    exact False.elim (not_lt_of_ge hbound hp)

end Erdos335.Loeb

end
