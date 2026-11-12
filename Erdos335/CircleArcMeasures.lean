import Erdos335.CircleArcCutTransfer
import Erdos335.CompactDysonTransform
import Mathlib.Algebra.Order.Interval.Set.Monoid

/-!
# Translation and measure of circle interval images
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set MeasureTheory
open scoped Pointwise

namespace Erdos335.Loeb

theorem unitCircle_translate_image (t : ℝ) (E : Set ℝ) :
    (t : AddCircle (1 : ℝ)) +ᵥ (((↑) : ℝ → AddCircle (1 : ℝ)) '' E) =
      ((↑) : ℝ → AddCircle (1 : ℝ)) '' ((fun x => t + x) '' E) := by
  ext z
  constructor
  · rintro ⟨y, ⟨x, hx, rfl⟩, rfl⟩
    exact ⟨t + x, ⟨x, hx, rfl⟩, AddCircle.coe_add 1 t x⟩
  · rintro ⟨y, ⟨x, hx, rfl⟩, rfl⟩
    exact ⟨(x : AddCircle (1 : ℝ)), ⟨x, hx, rfl⟩, (AddCircle.coe_add 1 t x).symm⟩

theorem volume_unitCircle_openArc_of_width
    (a b : ℝ) (hwidth : b - a ≤ 1) :
    volume (((↑) : ℝ → AddCircle (1 : ℝ)) '' Ioo a b) = ENNReal.ofReal (b - a) := by
  have : Fact (0 < (1 : ℝ)) := ⟨zero_lt_one⟩
  have hI : (fun x : ℝ => a + x) '' Ioo (0 : ℝ) (b - a) = Ioo a b := by
    simpa using image_const_add_Ioo a 0 (b - a)
  rw [← hI, ← unitCircle_translate_image, vadd_set_eq_neg_preimage, measure_preimage_add]
  simpa only [sub_zero] using volume_unitCircle_openArc 0 (b - a) le_rfl hwidth

theorem unitCircle_closedArc_ae_openArc (a b : ℝ) :
    (((↑) : ℝ → AddCircle (1 : ℝ)) '' Icc a b) =ᵐ[volume]
      (((↑) : ℝ → AddCircle (1 : ℝ)) '' Ioo a b) := by
  have : Fact (0 < (1 : ℝ)) := ⟨zero_lt_one⟩
  have hpoint (x : AddCircle (1 : ℝ)) : volume ({x} : Set (AddCircle (1 : ℝ))) = 0 := by
    simpa using (AddCircle.volume_closedBall (T := (1 : ℝ)) (x := x) 0)
  have hna : ∀ᵐ x : AddCircle (1 : ℝ), x ≠ (a : AddCircle (1 : ℝ)) := by
    rw [ae_iff]
    simpa using hpoint (a : AddCircle (1 : ℝ))
  have hnb : ∀ᵐ x : AddCircle (1 : ℝ), x ≠ (b : AddCircle (1 : ℝ)) := by
    rw [ae_iff]
    simpa using hpoint (b : AddCircle (1 : ℝ))
  filter_upwards [hna, hnb] with z hza hzb
  apply propext
  constructor
  · rintro ⟨x, hx, hxz⟩
    have hxa : x ≠ a := fun h => hza (by rw [← hxz, h])
    have hxb : x ≠ b := fun h => hzb (by rw [← hxz, h])
    exact ⟨x, ⟨lt_of_le_of_ne hx.1 (Ne.symm hxa), lt_of_le_of_ne hx.2 hxb⟩, hxz⟩
  · rintro ⟨x, hx, hxz⟩
    exact ⟨x, ⟨hx.1.le, hx.2.le⟩, hxz⟩

theorem volume_unitCircle_closedArc_of_width
    (a b : ℝ) (hwidth : b - a ≤ 1) :
    volume (((↑) : ℝ → AddCircle (1 : ℝ)) '' Icc a b) = ENNReal.ofReal (b - a) := by
  rw [measure_congr (unitCircle_closedArc_ae_openArc a b)]
  exact volume_unitCircle_openArc_of_width a b hwidth

end Erdos335.Loeb
