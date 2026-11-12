import Erdos335.LoebCircleInputArcs
import Erdos335.CircleArcMeasures

/-!
# Normalized closed-arc models and their measure
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set MeasureTheory
open scoped Pointwise

namespace Erdos335.Loeb

theorem unitCircle_normalized_closedArcModel
    (C : Set (AddCircle (1 : ℝ))) (hC : UnitCircleClosedArcModel C) :
    ∃ x : AddCircle (1 : ℝ), ∃ p : ℝ, 0 < p ∧ p < 1 ∧
      C =ᵐ[volume] x +ᵥ (((↑) : ℝ → AddCircle (1 : ℝ)) '' Icc 0 p) := by
  have : Fact (0 < (1 : ℝ)) := ⟨zero_lt_one⟩
  obtain ⟨c, a, b, hab, hwidth, hmodel⟩ := hC
  have hCshift : C =ᵐ[volume]
      (c : AddCircle (1 : ℝ)) +ᵥ (((↑) : ℝ → AddCircle (1 : ℝ)) '' Icc a b) := by
    have h := (vadd_set_ae_eq (c : AddCircle (1 : ℝ))).2 hmodel
    simpa only [vadd_vadd, add_neg_cancel, zero_vadd] using h
  have hI : (fun z : ℝ => a + z) '' Icc (0 : ℝ) (b - a) = Icc a b := by
    simpa using image_const_add_Icc a 0 (b - a)
  have hArc : ((↑) : ℝ → AddCircle (1 : ℝ)) '' Icc a b =
      (a : AddCircle (1 : ℝ)) +ᵥ (((↑) : ℝ → AddCircle (1 : ℝ)) '' Icc 0 (b - a)) := by
    rw [unitCircle_translate_image, hI]
  refine ⟨(c : AddCircle (1 : ℝ)) + (a : AddCircle (1 : ℝ)), b - a,
    sub_pos.mpr hab, hwidth, ?_⟩
  rwa [hArc, vadd_vadd] at hCshift

theorem volume_unitCircle_normalized_closedArc
    (x : AddCircle (1 : ℝ)) (p : ℝ) (hp : p ≤ 1) :
    volume (x +ᵥ (((↑) : ℝ → AddCircle (1 : ℝ)) '' Icc 0 p)) = ENNReal.ofReal p := by
  have : Fact (0 < (1 : ℝ)) := ⟨zero_lt_one⟩
  rw [vadd_set_eq_neg_preimage, measure_preimage_add]
  simpa only [sub_zero] using volume_unitCircle_closedArc_of_width 0 p (by simpa using hp)

end Erdos335.Loeb
