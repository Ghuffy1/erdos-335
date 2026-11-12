import Erdos335.CircleArcSupport
import Erdos335.CircleArcErosion

/-!
# Literal containment from a short sum-arc container
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set MeasureTheory
open scoped Pointwise

namespace Erdos335.Loeb

theorem support_unitCircle_translated_closedArc
    (x : AddCircle (1 : ℝ)) (p : ℝ) (hp : 0 < p) :
    (volume.restrict (x +ᵥ (((↑) : ℝ → AddCircle (1 : ℝ)) '' Icc 0 p))).support =
      x +ᵥ (((↑) : ℝ → AddCircle (1 : ℝ)) '' Icc 0 p) := by
  obtain ⟨r, rfl⟩ := QuotientAddGroup.mk'_surjective (AddSubgroup.zmultiples (1 : ℝ)) x
  change (volume.restrict ((r : AddCircle (1 : ℝ)) +ᵥ
    (((↑) : ℝ → AddCircle (1 : ℝ)) '' Icc 0 p))).support =
      (r : AddCircle (1 : ℝ)) +ᵥ (((↑) : ℝ → AddCircle (1 : ℝ)) '' Icc 0 p)
  rw [unitCircle_translate_image, image_const_add_Icc, add_zero]
  exact support_unitCircle_closedArc r (r + p) (by linarith)

theorem unitCircle_translated_closedArc_erosion
    (x y z : AddCircle (1 : ℝ)) (p q : ℝ) (hp : 0 ≤ p) (hq : 0 ≤ q)
    (hsum : p + q < 1)
    (hsub : z +ᵥ (y +ᵥ (((↑) : ℝ → AddCircle (1 : ℝ)) '' Icc 0 q)) ⊆
      (x + y) +ᵥ (((↑) : ℝ → AddCircle (1 : ℝ)) '' Icc 0 (p + q))) :
    z ∈ x +ᵥ (((↑) : ℝ → AddCircle (1 : ℝ)) '' Icc 0 p) := by
  have hred : (z - x) +ᵥ (((↑) : ℝ → AddCircle (1 : ℝ)) '' Icc 0 q) ⊆
      (((↑) : ℝ → AddCircle (1 : ℝ)) '' Icc 0 (p + q)) := by
    rintro u ⟨v, hv, rfl⟩
    have h := hsub (show z + (y + v) ∈
        z +ᵥ (y +ᵥ (((↑) : ℝ → AddCircle (1 : ℝ)) '' Icc 0 q)) from
      ⟨y + v, ⟨v, hv, rfl⟩, rfl⟩)
    obtain ⟨w, hw, heq⟩ := h
    have hweq : w = (z - x) + v := by
      apply add_left_cancel (a := x + y)
      calc
        (x + y) + w = z + (y + v) := heq
        _ = (x + y) + ((z - x) + v) := by abel
    change (z - x) + v ∈ (((↑) : ℝ → AddCircle (1 : ℝ)) '' Icc 0 (p + q))
    rwa [← hweq]
  have hz := (unitCircle_translate_closedArc_subset_iff p q hp hq hsum (z - x)).mp hred
  exact ⟨z - x, hz, by change x + (z - x) = z; abel⟩

theorem unitCircle_left_subset_of_ae_sum_container
    (C D : Set (AddCircle (1 : ℝ))) (hD : MeasurableSet D)
    (x y : AddCircle (1 : ℝ)) (p q : ℝ) (hp : 0 ≤ p) (hq : 0 < q)
    (hsum : p + q < 1)
    (hDmodel : D =ᵐ[volume] y +ᵥ (((↑) : ℝ → AddCircle (1 : ℝ)) '' Icc 0 q))
    (hcontainer : C + D ≤ᵐ[volume]
      (x + y) +ᵥ (((↑) : ℝ → AddCircle (1 : ℝ)) '' Icc 0 (p + q))) :
    C ⊆ x +ᵥ (((↑) : ℝ → AddCircle (1 : ℝ)) '' Icc 0 p) := by
  have : Fact (0 < (1 : ℝ)) := ⟨zero_lt_one⟩
  let K : Set (AddCircle (1 : ℝ)) :=
    (x + y) +ᵥ (((↑) : ℝ → AddCircle (1 : ℝ)) '' Icc 0 (p + q))
  have hK : IsClosed K := by
    dsimp [K]
    rw [vadd_set_eq_neg_preimage]
    exact (isCompact_Icc.image (AddCircle.continuous_mk' 1)).isClosed.preimage
      (continuous_const.add continuous_id)
  have hsupport : (volume.restrict D).support =
      y +ᵥ (((↑) : ℝ → AddCircle (1 : ℝ)) '' Icc 0 q) := by
    rw [Measure.restrict_congr_set hDmodel, support_unitCircle_translated_closedArc y q hq]
  intro z hz
  have hsub := add_support_subset_of_sum_ae_subset volume C D K hD hK hcontainer z hz
  rw [hsupport] at hsub
  exact unitCircle_translated_closedArc_erosion x y z p q hp hq.le hsum hsub

end Erdos335.Loeb
