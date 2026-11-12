import Erdos335.LoebInternalEmbedding

/-!
# Counting measure on an internal embedded family
-/

set_option autoImplicit false

open Set Filter MeasureTheory
open scoped ENNReal

namespace Erdos335.Loeb

theorem countingRatio_image_injection
    {X Y : Type*} [Finite X] [Nonempty X] (f : X → Y)
    (hf : Function.Injective f) (A : Set X) :
    countingRatio (f '' A) = countingRatio (Set.range f) * countingRatio A := by
  have hX : (Nat.card X : ℝ≥0∞) ≠ 0 := by exact_mod_cast Nat.card_pos.ne'
  simp only [countingRatio, Set.ncard_image_of_injective A hf,
    Set.ncard_range_of_injective hf]
  rw [mul_comm]
  exact (ENNReal.div_mul_div_cancel hX (by simp)).symm

variable {X Y : ℕ → Type*} [∀ n, Finite (X n)] [∀ n, Finite (Y n)]
variable [∀ n, Nonempty (X n)] [∀ n, Nonempty (Y n)]

theorem ultraCount_image_injection
    (U : Ultrafilter ℕ) (f : ∀ n, X n → Y n)
    (hf : ∀ n, Function.Injective (f n)) (A : ∀ n, Set (X n)) :
    ultraCount U (fun n => f n '' A n) =
      ultraCount U (fun n => Set.range (f n)) * ultraCount U A := by
  have hA : ultraCount U A ≠ ∞ := ne_of_lt ((ultraCount_le_one U A).trans_lt (by simp))
  have hR : ultraCount U (fun n => Set.range (f n)) ≠ ∞ :=
    ne_of_lt ((ultraCount_le_one U _).trans_lt (by simp))
  apply tendsto_nhds_unique (tendsto_ultraCount U _)
  have hlim := ENNReal.Tendsto.mul (tendsto_ultraCount U (fun n => Set.range (f n)))
    (Or.inr hA) (tendsto_ultraCount U A) (Or.inr hR)
  exact hlim.congr' (.of_forall fun n => (countingRatio_image_injection (f n) (hf n) (A n)).symm)

theorem loebMeasure_internal_image_injection
    (U : Ultrafilter ℕ) (hU : (U : Filter ℕ) ≤ atTop)
    (f : ∀ n, X n → Y n) (hf : ∀ n, Function.Injective (f n))
    (T : Set ((U : Filter ℕ).Product X)) (hT : T ∈ internalSets U) :
    loebMeasure U hU (productMap (U : Filter ℕ) f '' T) =
      loebMeasure U hU (Set.range (productMap (U : Filter ℕ) f)) * loebMeasure U hU T := by
  obtain ⟨A, rfl⟩ := hT
  rw [internalSet_image, range_productMap, loebMeasure_internal,
    loebMeasure_internal, loebMeasure_internal]
  exact ultraCount_image_injection U f hf A

end Erdos335.Loeb
