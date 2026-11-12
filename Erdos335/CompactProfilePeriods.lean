import Erdos335.CompactProfileRegularization

/-!
# Exact periods of the positive intersection profile
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Filter Set MeasureTheory
open scoped Pointwise

noncomputable section

namespace Erdos335.Loeb

variable {G : Type*} [AddCommGroup G] [TopologicalSpace G] [IsTopologicalAddGroup G]
variable [T2Space G] [MeasurableSpace G] [BorelSpace G]

theorem compactIntersectionProfile_translate_left
    (μ : Measure G) [μ.IsAddLeftInvariant] (A B : Set G) (t e : G) :
    compactIntersectionProfile μ (t +ᵥ A) B (t + e) = compactIntersectionProfile μ A B e := by
  unfold compactIntersectionProfile
  rw [← vadd_vadd, ← vadd_set_inter, vadd_set_eq_neg_preimage, measure_preimage_add]

theorem compactIntersectionProfile_period_of_ae
    (μ : Measure G) [μ.IsAddLeftInvariant] (A B : Set G) (t e : G)
    (hperiod : t +ᵥ A =ᵐ[μ] A) :
    compactIntersectionProfile μ A B (t + e) = compactIntersectionProfile μ A B e := by
  calc
    compactIntersectionProfile μ A B (t + e) =
        compactIntersectionProfile μ (t +ᵥ A) B (t + e) :=
      (compactIntersectionProfile_congr_ae μ (t +ᵥ A) A B B hperiod Filter.EventuallyEq.rfl _).symm
    _ = compactIntersectionProfile μ A B e := compactIntersectionProfile_translate_left μ A B t e

theorem positive_intersection_support_periodic
    (μ : Measure G) [μ.IsAddLeftInvariant] (A B : Set G) (H : AddSubgroup G)
    (hperiod : ∀ t ∈ H, t +ᵥ A =ᵐ[μ] A) :
    ∀ t ∈ H, t +ᵥ {e | 0 < compactIntersectionProfile μ A B e} =
      {e | 0 < compactIntersectionProfile μ A B e} := by
  intro t ht
  ext e
  constructor
  · rintro ⟨x, hx, rfl⟩
    change 0 < compactIntersectionProfile μ A B (t + x)
    rwa [compactIntersectionProfile_period_of_ae μ A B t x (hperiod t ht)]
  · intro he
    refine ⟨-t + e, ?_, by simp [vadd_eq_add]⟩
    change 0 < compactIntersectionProfile μ A B (-t + e)
    rwa [compactIntersectionProfile_period_of_ae μ A B (-t) e (hperiod (-t) (H.neg_mem ht))]

end Erdos335.Loeb

end
