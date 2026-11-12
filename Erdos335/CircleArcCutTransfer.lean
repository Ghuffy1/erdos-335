import Erdos335.CircleRegularCut

/-!
# Recovering a circle arc from its almost-everywhere cut interval
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set MeasureTheory
open scoped symmDiff

namespace Erdos335.Loeb

theorem unitCircle_openArc_preimage
    (a b : ℝ) (ha : 0 ≤ a) (hb : b ≤ 1) :
    ((↑) : ℝ → AddCircle (1 : ℝ)) ⁻¹' (((↑) : ℝ → AddCircle (1 : ℝ)) '' Ioo a b)
      ∩ Ioo (0 : ℝ) 1 = Ioo a b := by
  have : Fact (0 < (1 : ℝ)) := ⟨zero_lt_one⟩
  ext x
  constructor
  · rintro ⟨⟨y, hy, heq⟩, hx⟩
    have hyI : y ∈ Ico (0 : ℝ) (0 + 1) := by
      simpa only [zero_add] using (show y ∈ Ico (0 : ℝ) 1 from
        ⟨(ha.trans_lt hy.1).le, hy.2.trans_le hb⟩)
    have hxI : x ∈ Ico (0 : ℝ) (0 + 1) := by
      simpa only [zero_add] using (show x ∈ Ico (0 : ℝ) 1 from ⟨hx.1.le, hx.2⟩)
    have hyx : y = x := (AddCircle.coe_eq_coe_iff_of_mem_Ico hyI hxI).mp heq
    rwa [← hyx]
  · intro hx
    exact ⟨⟨x, hx, rfl⟩, ⟨ha.trans_lt hx.1, hx.2.trans_le hb⟩⟩

theorem unitCircle_ae_eq_openArc_of_cut
    (S : Set (AddCircle (1 : ℝ))) (hS : MeasurableSet S)
    (a b : ℝ) (ha : 0 ≤ a) (hb : b ≤ 1)
    (hcut : (((↑) : ℝ → AddCircle (1 : ℝ)) ⁻¹' S ∩ Ioo (0 : ℝ) 1)
      =ᵐ[volume] Ioo a b) :
    S =ᵐ[volume] (((↑) : ℝ → AddCircle (1 : ℝ)) '' Ioo a b) := by
  let I : Set (AddCircle (1 : ℝ)) := ((↑) : ℝ → AddCircle (1 : ℝ)) '' Ioo a b
  have hI : MeasurableSet I :=
    (QuotientAddGroup.isOpenMap_coe (Ioo a b) isOpen_Ioo).measurableSet
  have hpre := unitCircle_openArc_preimage a b ha hb
  have hset : (((↑) : ℝ → AddCircle (1 : ℝ)) ⁻¹' (S ∆ I) ∩ Ioo (0 : ℝ) 1) =
      ((((↑) : ℝ → AddCircle (1 : ℝ)) ⁻¹' S ∩ Ioo (0 : ℝ) 1) ∆ Ioo a b) := by
    rw [← hpre]
    ext x
    simp only [I, mem_inter_iff, mem_preimage, mem_symmDiff]
    tauto
  apply measure_symmDiff_eq_zero_iff.mp
  rw [← volume_unitCircle_lift_openInterval (S ∆ I) (hS.symmDiff hI), hset]
  exact measure_symmDiff_eq_zero_iff.mpr hcut

theorem volume_unitCircle_openArc
    (a b : ℝ) (ha : 0 ≤ a) (hb : b ≤ 1) :
    volume (((↑) : ℝ → AddCircle (1 : ℝ)) '' Ioo a b) = ENNReal.ofReal (b - a) := by
  have hI : MeasurableSet (((↑) : ℝ → AddCircle (1 : ℝ)) '' Ioo a b) :=
    (QuotientAddGroup.isOpenMap_coe (Ioo a b) isOpen_Ioo).measurableSet
  rw [← volume_unitCircle_lift_openInterval _ hI, unitCircle_openArc_preimage a b ha hb,
    Real.volume_Ioo]

end Erdos335.Loeb
