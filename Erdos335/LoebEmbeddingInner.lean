import Erdos335.LoebEmbeddingMeasure
import Erdos335.LoebInnerMeasure

/-!
# Internal inner measure under coordinate embeddings
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter MeasureTheory
open scoped ENNReal

noncomputable section

namespace Erdos335.Loeb

variable {X Y : ℕ → Type*} [∀ n, Finite (X n)] [∀ n, Finite (Y n)]
variable [∀ n, Nonempty (X n)] [∀ n, Nonempty (Y n)]

theorem internalInnerMeasure_image_injection
    (U : Ultrafilter ℕ) (hU : (U : Filter ℕ) ≤ atTop)
    (f : ∀ n, X n → Y n) (hf : ∀ n, Function.Injective (f n))
    (S : Set ((U : Filter ℕ).Product X)) :
    internalInnerMeasure U hU (productMap (U : Filter ℕ) f '' S) =
      loebMeasure U hU (Set.range (productMap (U : Filter ℕ) f)) * internalInnerMeasure U hU S := by
  let e := productMap (U : Filter ℕ) f
  let c := loebMeasure U hU (Set.range e)
  have he := productMap_injective (U : Filter ℕ) f hf
  apply le_antisymm
  · unfold internalInnerMeasure
    apply iSup_le
    intro T
    have hpre : e ⁻¹' T.1 ∈ internalSets U := by
      obtain ⟨A, hA⟩ := T.2.1
      rw [← hA, internalSet_preimage]
      exact ⟨fun n => f n ⁻¹' A n, rfl⟩
    have hpreS : e ⁻¹' T.1 ⊆ S := by
      intro x hx
      obtain ⟨z, hz, hzx⟩ := T.2.2 hx
      exact he hzx ▸ hz
    have himage : e '' (e ⁻¹' T.1) = T.1 := image_preimage_eq_of_subset
      (T.2.2.trans (image_subset_range e S))
    calc
      loebMeasure U hU T.1 = loebMeasure U hU (e '' (e ⁻¹' T.1)) :=
        congrArg (loebMeasure U hU) himage.symm
      _ = c * loebMeasure U hU (e ⁻¹' T.1) :=
        loebMeasure_internal_image_injection U hU f hf _ hpre
      _ ≤ c * ⨆ V : {V : Set ((U : Filter ℕ).Product X) //
          V ∈ internalSets U ∧ V ⊆ S}, loebMeasure U hU V.1 := by
        gcongr
        exact le_iSup_of_le ⟨e ⁻¹' T.1, hpre, hpreS⟩ le_rfl
  · change c * internalInnerMeasure U hU S ≤ internalInnerMeasure U hU (e '' S)
    unfold internalInnerMeasure
    rw [ENNReal.mul_iSup]
    apply iSup_le
    intro T
    have himage : e '' T.1 ∈ internalSets U := by
      obtain ⟨A, hA⟩ := T.2.1
      rw [← hA, internalSet_image]
      exact ⟨fun n => f n '' A n, rfl⟩
    calc
      c * loebMeasure U hU T.1 = loebMeasure U hU (e '' T.1) :=
        (loebMeasure_internal_image_injection U hU f hf T.1 T.2.1).symm
      _ ≤ ⨆ V : {V : Set ((U : Filter ℕ).Product Y) //
          V ∈ internalSets U ∧ V ⊆ e '' S}, loebMeasure U hU V.1 :=
        le_iSup_of_le ⟨e '' T.1, himage, image_mono T.2.2⟩ le_rfl

end Erdos335.Loeb

end
