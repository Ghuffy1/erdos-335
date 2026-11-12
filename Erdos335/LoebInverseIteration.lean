import Erdos335.LoebAperiodicInverse
import Erdos335.LoebQuasiPeriodicActiveStructure
import Erdos335.LoebQuasiPeriodicActivePositive
import Erdos335.LoebQuasiPeriodicIteration

/-!
# Iterating the aperiodic inverse theorem

An irreducible aperiodic equality pair either has a Bohr model, has a
quasi-periodic decomposition with a Bohr active pair, or has decompositions
with arbitrarily small period measure.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter MeasureTheory
open scoped ENNReal Pointwise

noncomputable section

namespace Erdos335.Loeb

local instance inverseIterationLoebSpace (U : Ultrafilter ℕ) (q : ℕ → ℕ+) :
    MeasurableSpace ((U : Filter ℕ).Product (fun n => ZMod (q n : ℕ))) := loebMeasurableSpace U

theorem loeb_quasiPeriodic_active_inverse
    (U : Ultrafilter ℕ) (hU : (U : Filter ℕ) ≤ atTop) (q : ℕ → ℕ+)
    (A B : Set ((U : Filter ℕ).Product (fun n => ZMod (q n : ℕ))))
    (p : QuasiPeriodicPairData (loebMeasure U hU) (internalInnerMeasure U hU) A B)
    (hAm : MeasurableSet A) (hBm : MeasurableSet B) (hSm : MeasurableSet (A + B))
    (hirr : MeasureIrreducible (loebMeasure U hU) (internalInnerMeasure U hU) A B)
    (hnoAE : ∀ H : AddSubgroup ((U : Filter ℕ).Product (fun n => ZMod (q n : ℕ))),
      MeasurableSet (H : Set ((U : Filter ℕ).Product (fun n => ZMod (q n : ℕ)))) →
      0 < loebMeasure U hU (H : Set ((U : Filter ℕ).Product (fun n => ZMod (q n : ℕ)))) →
      ¬ ∀ t ∈ H, t +ᵥ (A + B) =ᵐ[loebMeasure U hU] A + B) :
    Nonempty (QuasiPeriodicPairData (loebMeasure U hU) (internalInnerMeasure U hU)
      p.left.active p.right.active) ∨
      Nonempty (InternalBohrPairData U hU q p.left.active p.right.active) := by
  have hleft := loeb_quasiPeriodic_active_positive_of_irreducible U hU q A B
    p.period p.period_measurable p.period_positive p.left hBm hSm hirr
    (hnoAE p.period p.period_measurable p.period_positive)
  have hright := loeb_quasiPeriodic_active_positive_of_irreducible U hU q B A
    p.period p.period_measurable p.period_positive p.right hAm
    (by simpa only [add_comm B A] using hSm) hirr.swap
    (by simpa only [add_comm B A] using
      hnoAE p.period p.period_measurable p.period_positive)
  obtain ⟨hactive, _, _, hperiods⟩ := loeb_quasiPeriodic_active_structure U hU q A B p
    hSm hleft hright hirr hnoAE
  have hfull : loebMeasure U hU (p.left.active + p.right.active) =
      loebMeasure U hU p.left.active + loebMeasure U hU p.right.active := by
    rw [← internalInnerMeasure_eq U hU _ hactive]
    exact p.active_identity
  exact loeb_aperiodic_equality_quasiPeriodic_or_internalBohr U hU q
    p.left.active p.right.active p.left.active_measurable p.right.active_measurable
    hactive hleft hright hfull hperiods

theorem loeb_irreducible_aperiodic_inverse_alternative
    (U : Ultrafilter ℕ) (hU : (U : Filter ℕ) ≤ atTop) (q : ℕ → ℕ+)
    (A B : Set ((U : Filter ℕ).Product (fun n => ZMod (q n : ℕ))))
    (hAm : MeasurableSet A) (hBm : MeasurableSet B) (hSm : MeasurableSet (A + B))
    (hApos : 0 < loebMeasure U hU A) (hBpos : 0 < loebMeasure U hU B)
    (hfull : loebMeasure U hU (A + B) = loebMeasure U hU A + loebMeasure U hU B)
    (hirr : MeasureIrreducible (loebMeasure U hU) (internalInnerMeasure U hU) A B)
    (hnoAE : ∀ H : AddSubgroup ((U : Filter ℕ).Product (fun n => ZMod (q n : ℕ))),
      MeasurableSet (H : Set ((U : Filter ℕ).Product (fun n => ZMod (q n : ℕ)))) →
      0 < loebMeasure U hU (H : Set ((U : Filter ℕ).Product (fun n => ZMod (q n : ℕ)))) →
      ¬ ∀ t ∈ H, t +ᵥ (A + B) =ᵐ[loebMeasure U hU] A + B) :
    Nonempty (InternalBohrPairData U hU q A B) ∨
      (∃ p : QuasiPeriodicPairData (loebMeasure U hU) (internalInnerMeasure U hU) A B,
        Nonempty (InternalBohrPairData U hU q p.left.active p.right.active)) ∨
      ∀ ε : ℝ, 0 < ε →
        ∃ p : QuasiPeriodicPairData (loebMeasure U hU) (internalInnerMeasure U hU) A B,
          (loebMeasure (X := fun n => ZMod (q n : ℕ)) U hU (p.period : Set _)).toReal < ε := by
  classical
  rcases loeb_aperiodic_equality_quasiPeriodic_or_internalBohr U hU q A B
    hAm hBm hSm hApos hBpos hfull hnoAE with hqp | hbohr
  · obtain ⟨p⟩ := hqp
    right
    by_cases hterminal : ∃ r : QuasiPeriodicPairData (loebMeasure U hU)
        (internalInnerMeasure U hU) A B,
        Nonempty (InternalBohrPairData U hU q r.left.active r.right.active)
    · exact Or.inl hterminal
    · right
      apply loeb_quasiPeriodic_arbitrarily_small_of_refinable U hU q A B p
      intro r
      rcases loeb_quasiPeriodic_active_inverse U hU q A B r hAm hBm hSm hirr hnoAE with
        hrefine | hbohr
      · exact hrefine
      · exact False.elim (hterminal ⟨r, hbohr⟩)
  · exact Or.inl hbohr

end Erdos335.Loeb

end
