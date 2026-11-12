import Erdos335.LoebIrreducibleCore

/-!
# Restricting an irreducible equality pair to full-measure subsets
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Filter Set MeasureTheory
open scoped Pointwise ENNReal

noncomputable section

namespace Erdos335.Loeb

theorem MeasureIrreducible.full_measure_restriction
    {G : Type*} [AddCommGroup G] [MeasurableSpace G]
    {μ : Measure G} {inner : Set G → ℝ≥0∞} {A B : Set G}
    (hirr : MeasureIrreducible μ inner A B)
    (P Q : Set G) (hPm : MeasurableSet P) (hQm : MeasurableSet Q)
    (hPA : P ⊆ A) (hQB : Q ⊆ B) (hPmass : μ P = μ A) (hQmass : μ Q = μ B) :
    MeasureIrreducible μ inner P Q := by
  intro R T hRm hTm hRP hTQ hRmass hTmass
  exact (hirr R T hRm hTm (hRP.trans hPA) (hTQ.trans hQB)
    (hRmass.trans hPmass) (hTmass.trans hQmass)).trans
      (hirr P Q hPm hQm hPA hQB hPmass hQmass).symm

local instance fullMeasureRestrictionLoebSpace (U : Ultrafilter ℕ) (q : ℕ → ℕ+) :
    MeasurableSpace ((U : Filter ℕ).Product (fun n => ZMod (q n : ℕ))) := loebMeasurableSpace U

theorem loeb_irreducible_full_measure_restriction
    (U : Ultrafilter ℕ) (hU : (U : Filter ℕ) ≤ atTop) (q : ℕ → ℕ+)
    (A B P Q : Set ((U : Filter ℕ).Product (fun n => ZMod (q n : ℕ))))
    (hPm : MeasurableSet P) (hQm : MeasurableSet Q) (hSm : MeasurableSet (A + B))
    (hPA : P ⊆ A) (hQB : Q ⊆ B)
    (hPmass : loebMeasure U hU P = loebMeasure U hU A)
    (hQmass : loebMeasure U hU Q = loebMeasure U hU B)
    (hirr : MeasureIrreducible (loebMeasure U hU) (internalInnerMeasure U hU) A B)
    (hfull : loebMeasure U hU (A + B) = loebMeasure U hU A + loebMeasure U hU B) :
    MeasurableSet (P + Q) ∧ P + Q =ᵐ[loebMeasure U hU] A + B ∧
      loebMeasure U hU (P + Q) = loebMeasure U hU P + loebMeasure U hU Q ∧
      MeasureIrreducible (loebMeasure U hU) (internalInnerMeasure U hU) P Q := by
  have hi := hirr P Q hPm hQm hPA hQB hPmass hQmass
  have hinner : internalInnerMeasure U hU (P + Q) = loebMeasure U hU (A + B) :=
    hi.trans (internalInnerMeasure_eq U hU _ hSm)
  obtain ⟨hPQm, hPQae⟩ := measurable_of_subset_full_inner U hU (P + Q) (A + B)
    (add_subset_add hPA hQB) hSm hinner
  refine ⟨hPQm, hPQae, ?_, hirr.full_measure_restriction P Q hPm hQm hPA hQB hPmass hQmass⟩
  rw [measure_congr hPQae, hfull, hPmass, hQmass]

end Erdos335.Loeb

end
