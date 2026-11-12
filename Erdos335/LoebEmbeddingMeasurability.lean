import Erdos335.LoebEmbeddingMeasure

/-!
# Measurable embeddings onto positive internal sets
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter MeasureTheory
open scoped ENNReal

noncomputable section

namespace Erdos335.Loeb

variable {X Y : ℕ → Type*} [∀ n, Finite (X n)] [∀ n, Finite (Y n)]
variable [∀ n, Nonempty (X n)] [∀ n, Nonempty (Y n)]

theorem measurableSet_image_positive_internal_injection
    (U : Ultrafilter ℕ) (hU : (U : Filter ℕ) ≤ atTop)
    (f : ∀ n, X n → Y n) (hf : ∀ n, Function.Injective (f n))
    (hpos : 0 < loebMeasure U hU (Set.range (productMap (U : Filter ℕ) f)))
    (S : Set ((U : Filter ℕ).Product X)) (hS : MeasurableSet[loebMeasurableSpace U] S) :
    MeasurableSet[loebMeasurableSpace U] (productMap (U : Filter ℕ) f '' S) := by
  let : MeasurableSpace ((U : Filter ℕ).Product X) := loebMeasurableSpace U
  let : MeasurableSpace ((U : Filter ℕ).Product Y) := loebMeasurableSpace U
  let e := productMap (U : Filter ℕ) f
  let c := loebMeasure U hU (Set.range e)
  have he := productMap_injective (U : Filter ℕ) f hf
  have hH : MeasurableSet (Set.range e) := by
    rw [show Set.range e = internalSet U (fun n => Set.range (f n)) from range_productMap U f]
    exact measurable_internalSet U _
  change ∀ T, loebMeasure U hU T =
    loebMeasure U hU (T ∩ Set.range e) + loebMeasure U hU (T \ Set.range e) at hH
  change ∀ T, loebMeasure U hU T =
    loebMeasure U hU (T ∩ S) + loebMeasure U hU (T \ S) at hS
  change ∀ T, loebMeasure U hU T =
    loebMeasure U hU (T ∩ e '' S) + loebMeasure U hU (T \ e '' S)
  intro T
  have hR : e '' (e ⁻¹' T) = T ∩ Set.range e := image_preimage_eq_inter_range
  have hI : e '' ((e ⁻¹' T) ∩ S) = T ∩ e '' S := by
    ext y
    constructor
    · rintro ⟨x, ⟨hx, hs⟩, rfl⟩
      exact ⟨hx, ⟨x, hs, rfl⟩⟩
    · rintro ⟨hy, x, hs, rfl⟩
      exact ⟨x, ⟨hy, hs⟩, rfl⟩
  have hD : e '' ((e ⁻¹' T) \ S) = (T ∩ Set.range e) \ e '' S := by
    ext y
    constructor
    · rintro ⟨x, ⟨hx, hs⟩, rfl⟩
      refine ⟨⟨hx, ⟨x, rfl⟩⟩, ?_⟩
      rintro ⟨z, hz, heq⟩
      exact hs (he heq ▸ hz)
    · rintro ⟨⟨hy, x, rfl⟩, hs⟩
      exact ⟨x, ⟨hy, fun hx => hs ⟨x, hx, rfl⟩⟩, rfl⟩
  have hsplit : loebMeasure U hU (T ∩ Set.range e) =
      loebMeasure U hU (T ∩ e '' S) +
      loebMeasure U hU ((T ∩ Set.range e) \ e '' S) := by
    rw [← hD, ← hI, ← hR, loebMeasure_image_injection U hU f hf hpos,
      loebMeasure_image_injection U hU f hf hpos,
      loebMeasure_image_injection U hU f hf hpos, ← mul_add, hS (e ⁻¹' T)]
  have hDI : (T \ e '' S) ∩ Set.range e = (T ∩ Set.range e) \ e '' S := by
    ext y
    simp only [mem_inter_iff, Set.mem_sdiff]
    tauto
  have hDD : (T \ e '' S) \ Set.range e = T \ Set.range e := by
    ext y
    constructor
    · exact fun h => ⟨h.1.1, h.2⟩
    · intro h
      refine ⟨⟨h.1, ?_⟩, h.2⟩
      rintro ⟨x, _, rfl⟩
      exact h.2 ⟨x, rfl⟩
  calc
    loebMeasure U hU T = loebMeasure U hU (T ∩ Set.range e) +
        loebMeasure U hU (T \ Set.range e) := hH T
    _ = loebMeasure U hU (T ∩ e '' S) +
        (loebMeasure U hU ((T ∩ Set.range e) \ e '' S) +
          loebMeasure U hU (T \ Set.range e)) := by rw [hsplit, add_assoc]
    _ = loebMeasure U hU (T ∩ e '' S) + loebMeasure U hU (T \ e '' S) := by
      rw [← hDI, ← hDD, ← hH (T \ e '' S)]

theorem measurableEmbedding_positive_internal_injection
    (U : Ultrafilter ℕ) (hU : (U : Filter ℕ) ≤ atTop)
    (f : ∀ n, X n → Y n) (hf : ∀ n, Function.Injective (f n))
    (hpos : 0 < loebMeasure U hU (Set.range (productMap (U : Filter ℕ) f))) :
    @MeasurableEmbedding ((U : Filter ℕ).Product X) ((U : Filter ℕ).Product Y)
      (loebMeasurableSpace U) (loebMeasurableSpace U) (productMap (U : Filter ℕ) f) := by
  let : MeasurableSpace ((U : Filter ℕ).Product X) := loebMeasurableSpace U
  let : MeasurableSpace ((U : Filter ℕ).Product Y) := loebMeasurableSpace U
  exact {
    injective := productMap_injective (U : Filter ℕ) f hf
    measurable := measurable_positive_internal_injection U hU f hf hpos
    measurableSet_image' := fun S hS => measurableSet_image_positive_internal_injection U hU f hf hpos S hS
  }

end Erdos335.Loeb

end
