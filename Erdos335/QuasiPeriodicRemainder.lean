import Erdos335.LoebCosetSectionSums
import Erdos335.QuasiPeriodicSets

/-!
# A periodic set with one exceptional coset
-/

set_option autoImplicit false

open Set MeasureTheory
open scoped Pointwise

namespace Erdos335.Loeb

theorem exists_quasiPeriodicDecomposition_of_single_coset_remainder
    {G : Type*} [AddCommGroup G] [MeasurableSpace G]
    (μ : Measure G) (H : AddSubgroup G) (S T : Set G) (a : G)
    (hSm : MeasurableSet S) (hTm : MeasurableSet T) (hTS : T ⊆ S)
    (hperiod : T + (H : Set G) = T) (ha : a ∉ T)
    (hactive : S \ T ⊆ a +ᵥ (H : Set G)) (hne : (S \ T).Nonempty) :
    ∃ p : QuasiPeriodicDecomposition μ H S,
      p.background = T ∧ p.active = S \ T ∧ p.anchor = a := by
  have hsat : (S \ T) + (H : Set G) ⊆ a +ᵥ (H : Set G) := by
    rintro x ⟨s, hs, k, hk, rfl⟩
    obtain ⟨l, hl, hls⟩ := hactive hs
    refine ⟨l + k, H.add_mem hl hk, ?_⟩
    change a + l = s at hls
    change a + (l + k) = s + k
    rw [← add_assoc, hls]
  let p : QuasiPeriodicDecomposition μ H S := {
    active := S \ T
    background := T
    anchor := a
    active_measurable := hSm.diff hTm
    background_measurable := hTm
    active_nonempty := hne
    partition := by
      ext x
      constructor
      · intro hx
        by_cases ht : x ∈ T
        · exact Or.inl ht
        · exact Or.inr ⟨hx, ht⟩
      · rintro (hx | hx)
        · exact hTS hx
        · exact hx.1
    active_subset_coset := hactive
    separated := (disjoint_periodic_set_coset H T hperiod a ha).symm.mono hsat Subset.rfl
    background_periodic := by rw [hperiod, sdiff_self, measure_empty]
  }
  exact ⟨p, rfl, rfl, rfl⟩

end Erdos335.Loeb
