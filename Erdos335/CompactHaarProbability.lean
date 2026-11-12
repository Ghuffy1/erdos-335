import Mathlib.MeasureTheory.Measure.Haar.Basic

/-!
# Normalized Haar measure on a compact additive group
-/

set_option autoImplicit false

open Set MeasureTheory TopologicalSpace

noncomputable section

namespace Erdos335.Loeb

theorem exists_compact_addHaar_probability
    (G : Type*) [AddCommGroup G] [TopologicalSpace G] [IsTopologicalAddGroup G]
    [CompactSpace G] [T2Space G] [MeasurableSpace G] [BorelSpace G] :
    ∃ ν : Measure G, IsProbabilityMeasure ν ∧ Measure.IsAddHaarMeasure ν := by
  let ν := Measure.addHaarMeasure (⊤ : PositiveCompacts G)
  have hprob : IsProbabilityMeasure ν := ⟨by
    change Measure.addHaarMeasure (⊤ : PositiveCompacts G) univ = 1
    simpa only [PositiveCompacts.coe_top] using
      (Measure.addHaarMeasure_self (K₀ := (⊤ : PositiveCompacts G)))⟩
  exact ⟨ν, hprob, inferInstance⟩

end Erdos335.Loeb

end
