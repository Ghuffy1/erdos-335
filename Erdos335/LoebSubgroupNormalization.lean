import Erdos335.LoebSubgroupCoordinates
import Erdos335.LoebEmbeddingMeasurability
import Erdos335.LoebEmbeddingInner

/-!
# Normalized cyclic Loeb coordinates on positive subgroups
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter MeasureTheory
open scoped ENNReal

noncomputable section

namespace Erdos335.Loeb

theorem positive_loeb_subgroup_normalized_coordinates
    (U : Ultrafilter ℕ) (hU : (U : Filter ℕ) ≤ atTop) (q : ℕ → ℕ+)
    (H : AddSubgroup ((U : Filter ℕ).Product (fun n => ZMod (q n : ℕ))))
    (hH : MeasurableSet[loebMeasurableSpace U]
      (H : Set ((U : Filter ℕ).Product (fun n => ZMod (q n : ℕ)))))
    (hpos : 0 < loebMeasure U hU
      (H : Set ((U : Filter ℕ).Product (fun n => ZMod (q n : ℕ))))) :
    ∃ r : ℕ → ℕ+, ∃ p : ∀ n, ZMod (r n : ℕ) →+ ZMod (q n : ℕ),
      (∀ n, Function.Injective (p n)) ∧
      Set.range (productMapHom (U : Filter ℕ) p) =
        (H : Set ((U : Filter ℕ).Product (fun n => ZMod (q n : ℕ)))) ∧
      @MeasurableEmbedding ((U : Filter ℕ).Product (fun n => ZMod (r n : ℕ)))
        ((U : Filter ℕ).Product (fun n => ZMod (q n : ℕ)))
        (loebMeasurableSpace U) (loebMeasurableSpace U) (productMapHom (U : Filter ℕ) p) ∧
      (∀ S : Set ((U : Filter ℕ).Product (fun n => ZMod (r n : ℕ))),
        loebMeasure U hU (productMapHom (U : Filter ℕ) p '' S) =
          loebMeasure U hU (H : Set ((U : Filter ℕ).Product (fun n => ZMod (q n : ℕ)))) *
            loebMeasure U hU S) ∧
      (∀ S : Set ((U : Filter ℕ).Product (fun n => ZMod (r n : ℕ))),
        internalInnerMeasure U hU (productMapHom (U : Filter ℕ) p '' S) =
          loebMeasure U hU (H : Set ((U : Filter ℕ).Product (fun n => ZMod (q n : ℕ)))) *
            internalInnerMeasure U hU S) := by
  obtain ⟨r, p, hp, hrange⟩ :=
    positive_measurable_subgroup_has_cyclic_coordinates U hU q H hH hpos
  have hpos' : 0 < loebMeasure U hU (Set.range (productMapHom (U : Filter ℕ) p)) := by
    rwa [hrange]
  refine ⟨r, p, hp, hrange,
    measurableEmbedding_positive_internal_injection U hU (fun n => p n) hp hpos', ?_, ?_⟩
  · intro S
    have h := loebMeasure_image_injection U hU (fun n => p n) hp hpos' S
    change loebMeasure U hU (productMapHom (U : Filter ℕ) p '' S) =
      loebMeasure U hU (Set.range (productMapHom (U : Filter ℕ) p)) * loebMeasure U hU S at h
    rwa [hrange] at h
  · intro S
    have h := internalInnerMeasure_image_injection U hU (fun n => p n) hp S
    change internalInnerMeasure U hU (productMapHom (U : Filter ℕ) p '' S) =
      loebMeasure U hU (Set.range (productMapHom (U : Filter ℕ) p)) * internalInnerMeasure U hU S at h
    rwa [hrange] at h

end Erdos335.Loeb

end
