import Erdos335.CompactOpenSubgroupHaar
import Erdos335.CircleCharacterMeasure

/-!
# Uniqueness of the normalized open-subgroup measure
-/

set_option autoImplicit false

open Set MeasureTheory

namespace Erdos335.Loeb

theorem normalized_open_subgroup_measure
    {K : Type*} [AddCommGroup K] [TopologicalSpace K] [IsTopologicalAddGroup K]
    [CompactSpace K] [T2Space K] [MeasurableSpace K] [BorelSpace K] [MeasurableAdd₂ K]
    (μ : Measure K) [IsProbabilityMeasure μ] [μ.IsAddHaarMeasure]
    (H : OpenAddSubgroup K) (ν : Measure H) [IsProbabilityMeasure ν] [ν.IsAddHaarMeasure] :
    ∀ S : Set H, μ ((Subtype.val : H → K) '' S) = μ (H : Set K) * ν S := by
  have : IsTopologicalAddGroup H := inferInstanceAs (IsTopologicalAddGroup H.toAddSubgroup)
  have : CompactSpace H := isCompact_iff_compactSpace.mp H.isClosed.isCompact
  obtain ⟨η, hηprob, hηhaar, hηimage⟩ := exists_normalized_open_subgroup_measure μ H
  letI : IsProbabilityMeasure η := hηprob
  letI : η.IsAddHaarMeasure := hηhaar
  have heq : η = ν := Measure.isAddHaarMeasure_eq_of_isProbabilityMeasure _ _
  simpa only [heq] using hηimage

end Erdos335.Loeb
