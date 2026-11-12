import Erdos335.HaarOverlapPositivePart

/-!
# Translating the set preserves its Haar overlap profile
-/

set_option autoImplicit false

open Set MeasureTheory
open scoped Pointwise

namespace Erdos335.Loeb

theorem haarOverlap_translate_eq
    {G : Type*} [AddCommGroup G] [MeasurableSpace G] [MeasurableAdd₂ G]
    (μ : Measure G) [μ.IsAddLeftInvariant] (S : Set G) (c t : G) :
    haarOverlap μ (c +ᵥ S) t = haarOverlap μ S t := by
  have hcomm : t +ᵥ (c +ᵥ S) = c +ᵥ (t +ᵥ S) := by
    rw [vadd_vadd, vadd_vadd, add_comm t c]
  have hset : (c +ᵥ S) ∩ (t +ᵥ (c +ᵥ S)) = c +ᵥ (S ∩ (t +ᵥ S)) := by
    rw [hcomm, vadd_set_inter]
  unfold haarOverlap
  rw [hset, vadd_set_eq_neg_preimage, measure_preimage_add]

end Erdos335.Loeb
