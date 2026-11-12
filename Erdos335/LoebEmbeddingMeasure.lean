import Erdos335.LoebEmbeddingCounting
import Erdos335.LoebOuterApproximation

/-!
# Loeb measure under positive internal embeddings
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter MeasureTheory
open scoped ENNReal

noncomputable section

namespace Erdos335.Loeb

variable {X Y : ℕ → Type*} [∀ n, Finite (X n)] [∀ n, Finite (Y n)]
variable [∀ n, Nonempty (X n)] [∀ n, Nonempty (Y n)]

theorem loebMeasure_image_injection
    (U : Ultrafilter ℕ) (hU : (U : Filter ℕ) ≤ atTop)
    (f : ∀ n, X n → Y n) (hf : ∀ n, Function.Injective (f n))
    (hpos : 0 < loebMeasure U hU (Set.range (productMap (U : Filter ℕ) f)))
    (S : Set ((U : Filter ℕ).Product X)) :
    loebMeasure U hU (productMap (U : Filter ℕ) f '' S) =
      loebMeasure U hU (Set.range (productMap (U : Filter ℕ) f)) * loebMeasure U hU S := by
  let e := productMap (U : Filter ℕ) f
  let c := loebMeasure U hU (Set.range e)
  have hc : c ≠ ∞ := ne_of_lt (calc
    c ≤ loebMeasure (X := Y) U hU univ := measure_mono (subset_univ _)
    _ = 1 := loebMeasure_univ U hU
    _ < ∞ := by simp)
  apply le_antisymm
  · change loebMeasure U hU (e '' S) ≤ c * loebMeasure U hU S
    rw [loebMeasure_eq_iInf_internal_supersets U hU S,
      ENNReal.mul_iInf_of_ne hpos.ne' hc]
    apply le_iInf
    intro T
    calc
      loebMeasure U hU (e '' S) ≤ loebMeasure U hU (e '' T.1) :=
        measure_mono (image_mono T.2.2)
      _ = c * loebMeasure U hU T.1 :=
        loebMeasure_internal_image_injection U hU f hf T.1 T.2.1
  · change c * loebMeasure U hU S ≤ loebMeasure U hU (e '' S)
    rw [loebMeasure_eq_iInf_internal_supersets U hU (e '' S)]
    apply le_iInf
    intro T
    have hpre : e ⁻¹' T.1 ∈ internalSets U := by
      obtain ⟨A, hA⟩ := T.2.1
      rw [← hA, internalSet_preimage]
      exact ⟨fun n => f n ⁻¹' A n, rfl⟩
    have hsub : S ⊆ e ⁻¹' T.1 := fun x hx => T.2.2 ⟨x, hx, rfl⟩
    calc
      c * loebMeasure U hU S ≤ c * loebMeasure U hU (e ⁻¹' T.1) := by
        gcongr
      _ = loebMeasure U hU (e '' (e ⁻¹' T.1)) :=
        (loebMeasure_internal_image_injection U hU f hf _ hpre).symm
      _ ≤ loebMeasure U hU T.1 := measure_mono (image_preimage_subset _ _)

theorem measurable_positive_internal_injection
    (U : Ultrafilter ℕ) (hU : (U : Filter ℕ) ≤ atTop)
    (f : ∀ n, X n → Y n) (hf : ∀ n, Function.Injective (f n))
    (hpos : 0 < loebMeasure U hU (Set.range (productMap (U : Filter ℕ) f))) :
    @Measurable ((U : Filter ℕ).Product X) ((U : Filter ℕ).Product Y)
      (loebMeasurableSpace U) (loebMeasurableSpace U) (productMap (U : Filter ℕ) f) := by
  let : MeasurableSpace ((U : Filter ℕ).Product X) := loebMeasurableSpace U
  let : MeasurableSpace ((U : Filter ℕ).Product Y) := loebMeasurableSpace U
  let e := productMap (U : Filter ℕ) f
  let c := loebMeasure U hU (Set.range e)
  have hc : c ≠ ∞ := ne_of_lt (calc
    c ≤ loebMeasure (X := Y) U hU univ := measure_mono (subset_univ _)
    _ = 1 := loebMeasure_univ U hU
    _ < ∞ := by simp)
  intro S hS
  change ∀ T, loebMeasure U hU T = loebMeasure U hU (T ∩ S) + loebMeasure U hU (T \ S) at hS
  change ∀ T, loebMeasure U hU T =
    loebMeasure U hU (T ∩ e ⁻¹' S) + loebMeasure U hU (T \ e ⁻¹' S)
  intro T
  apply (ENNReal.mul_right_inj hpos.ne' hc).mp
  rw [mul_add]
  change loebMeasure U hU (Set.range e) * loebMeasure U hU T = _
  rw [← loebMeasure_image_injection U hU f hf hpos T,
    ← loebMeasure_image_injection U hU f hf hpos (T ∩ e ⁻¹' S),
    ← loebMeasure_image_injection U hU f hf hpos (T \ e ⁻¹' S)]
  have hI : e '' (T ∩ e ⁻¹' S) = (e '' T) ∩ S := by
    ext y
    constructor
    · rintro ⟨x, ⟨hx, hs⟩, rfl⟩
      exact ⟨⟨x, hx, rfl⟩, hs⟩
    · rintro ⟨⟨x, hx, rfl⟩, hs⟩
      exact ⟨x, ⟨hx, hs⟩, rfl⟩
  have hD : e '' (T \ e ⁻¹' S) = (e '' T) \ S := by
    ext y
    constructor
    · rintro ⟨x, ⟨hx, hs⟩, rfl⟩
      exact ⟨⟨x, hx, rfl⟩, hs⟩
    · rintro ⟨⟨x, hx, rfl⟩, hs⟩
      exact ⟨x, ⟨hx, hs⟩, rfl⟩
  rw [hI, hD]
  exact hS (e '' T)

end Erdos335.Loeb

end
