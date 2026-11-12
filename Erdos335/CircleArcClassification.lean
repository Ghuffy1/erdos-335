import Erdos335.CircleIntervalCut
import Erdos335.CircleArcCutTransfer

/-!
# Arc classification from localized critical circle pairs
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter Topology MeasureTheory
open scoped Pointwise

namespace Erdos335.Loeb

theorem unitCircle_ae_arc_of_localized_critical_pairs
    (S : Set (AddCircle (1 : ℝ))) (hS : MeasurableSet S)
    (hSpos : 0 < volume S) (hcomp : 0 < volume Sᶜ)
    (A B : ℕ → Set (AddCircle (1 : ℝ)))
    (hB : ∀ n, MeasurableSet (B n)) (hpositive : ∀ n, 0 < volume (B n))
    (hsum : ∀ n, A n + B n ≤ᵐ[volume] S)
    (hmass : ∀ n, (volume S).toReal = (volume (A n)).toReal + (volume (B n)).toReal)
    (hlocal : ∀ V ∈ 𝓝 (0 : AddCircle (1 : ℝ)), ∀ᶠ n in atTop, B n - B n ⊆ V) :
    ∃ c a b : ℝ, 0 ≤ a ∧ a < b ∧ b ≤ 1 ∧ b - a < 1 ∧
      (-(c : AddCircle (1 : ℝ)) +ᵥ S) =ᵐ[volume]
        (((↑) : ℝ → AddCircle (1 : ℝ)) '' Ioo a b) := by
  have : Fact (0 < (1 : ℝ)) := ⟨zero_lt_one⟩
  obtain ⟨c, a, b, ha, hab, hb, hcut⟩ :=
    unitCircle_ae_interval_cut_of_localized_critical_pairs S hS hSpos hcomp A B
      hB hpositive hsum hmass hlocal
  let R : Set (AddCircle (1 : ℝ)) := -(c : AddCircle (1 : ℝ)) +ᵥ S
  have hR : MeasurableSet R := by
    dsimp [R]
    rw [vadd_set_eq_neg_preimage]
    exact hS.preimage (measurable_const_add (- -(c : AddCircle (1 : ℝ))))
  have hmassR : volume R = volume S := by
    dsimp [R]
    rw [vadd_set_eq_neg_preimage, measure_preimage_add]
  have heq := unitCircle_ae_eq_openArc_of_cut R hR a b ha hb hcut
  refine ⟨c, a, b, ha, hab, hb, ?_, heq⟩
  have hlength : (volume S).toReal = b - a := by
    rw [← hmassR, measure_congr heq, volume_unitCircle_openArc a b ha hb,
      ENNReal.toReal_ofReal (sub_nonneg.mpr hab.le)]
  have hcompReal : 0 < (volume Sᶜ).toReal :=
    ENNReal.toReal_pos hcomp.ne' (measure_ne_top volume _)
  have htotal := congrArg ENNReal.toReal (measure_add_measure_compl (μ := volume) hS)
  rw [ENNReal.toReal_add (measure_ne_top volume _) (measure_ne_top volume _)] at htotal
  have huniv : (volume (univ : Set (AddCircle (1 : ℝ)))).toReal = 1 := by
    rw [AddCircle.measure_univ]
    norm_num
  rw [huniv, hlength] at htotal
  linarith

end Erdos335.Loeb
