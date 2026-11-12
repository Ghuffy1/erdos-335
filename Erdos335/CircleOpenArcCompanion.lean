import Erdos335.CircleSumLowerBound
import Erdos335.CircleShrinkingArcs
import Erdos335.CircleArcClassification
import Erdos335.CircleArcContainment
import Erdos335.CircleArcModels
import Mathlib.Topology.Algebra.Group.Pointwise

/-!
# A compact companion using an open sum-arc bound

Private proof development. Verification status is recorded separately.
The surjective Loeb-to-circle certificate is an explicit input and is
available from the intended whole-prefix Bohr model.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000

open Filter Set Topology MeasureTheory
open scoped Pointwise ENNReal

noncomputable section

namespace Erdos335.Loeb

local instance openArcCompanionLoebSpace (U : Ultrafilter ℕ) (q : ℕ → ℕ+) :
    MeasurableSpace ((U : Filter ℕ).Product (fun n => ZMod (q n : ℕ))) := loebMeasurableSpace U

theorem unitCircle_compact_openArc_companion
    (U : Ultrafilter ℕ) (hU : (U : Filter ℕ) ≤ atTop) (q : ℕ → ℕ+)
    (φ : (U : Filter ℕ).Product (fun n => ZMod (q n : ℕ)) →+ AddCircle (1 : ℝ))
    (hφ : Measurable φ) (hsurj : Function.Surjective φ)
    (K : Set (AddCircle (1 : ℝ))) (hK : IsCompact K)
    (j : AddCircle (1 : ℝ)) (x y : ℝ)
    (hx : 0 < x) (hy : 0 < y) (hxy : x + y < 1)
    (hKlower : x ≤ (volume K).toReal)
    (hSupper : (volume (K + (j +ᵥ (((↑) : ℝ → AddCircle (1 : ℝ)) '' Ioo 0 y)))).toReal ≤ x + y) :
    ∃ c : AddCircle (1 : ℝ),
      K ⊆ c +ᵥ (((↑) : ℝ → AddCircle (1 : ℝ)) '' Icc 0 x) ∧
      K =ᵐ[volume] c +ᵥ (((↑) : ℝ → AddCircle (1 : ℝ)) '' Icc 0 x) := by
  classical
  letI : Fact (0 < (1 : ℝ)) := ⟨zero_lt_one⟩
  letI : IsProbabilityMeasure (volume : Measure (AddCircle (1 : ℝ))) :=
    ⟨by simpa using AddCircle.measure_univ (1 : ℝ)⟩
  let I : ℝ → Set (AddCircle (1 : ℝ)) := fun t => ((↑) : ℝ → AddCircle (1 : ℝ)) '' Icc 0 t
  let O : ℝ → Set (AddCircle (1 : ℝ)) := fun t => ((↑) : ℝ → AddCircle (1 : ℝ)) '' Ioo 0 t
  let J : ℝ → Set (AddCircle (1 : ℝ)) := fun t => j +ᵥ O t
  let S := K + J y
  have hIcompact (t : ℝ) : IsCompact (I t) :=
    isCompact_Icc.image (AddCircle.continuous_mk' (1 : ℝ))
  have hOopen (t : ℝ) : IsOpen (O t) := by
    exact (QuotientAddGroup.isOpenMap_coe (N := AddSubgroup.zmultiples (1 : ℝ))) _ isOpen_Ioo
  have hJopen (t : ℝ) : IsOpen (J t) := by
    change IsOpen (j +ᵥ O t)
    rw [vadd_set_eq_neg_preimage]
    exact (hOopen t).preimage (continuous_const.add continuous_id)
  have hSopen : IsOpen S := (hJopen y).add_left
  have hKmeas : MeasurableSet K := hK.measurableSet
  have hSmeas : MeasurableSet S := hSopen.measurableSet
  have hJmodel (t : ℝ) : J t =ᵐ[volume] j +ᵥ I t :=
    (vadd_set_ae_eq j).2 (unitCircle_closedArc_ae_openArc 0 t).symm
  have hJmass (t : ℝ) (ht : 0 ≤ t) (htone : t ≤ 1) : (volume (J t)).toReal = t := by
    rw [measure_congr (hJmodel t), volume_unitCircle_normalized_closedArc j t htone,
      ENNReal.toReal_ofReal ht]
  have hImass (t : ℝ) (ht : 0 ≤ t) (htone : t ≤ 1) : (volume (I t)).toReal = t := by
    have hmeasure := volume_unitCircle_normalized_closedArc (0 : AddCircle (1 : ℝ)) t htone
    simp only [zero_vadd] at hmeasure
    rw [show volume (I t) = ENNReal.ofReal t from hmeasure, ENNReal.toReal_ofReal ht]
  have hyone : y < 1 := by linarith
  have hKpos : 0 < volume K := (ENNReal.toReal_pos_iff.mp (hx.trans_le hKlower)).1
  have hJpos : 0 < volume (J y) :=
    (ENNReal.toReal_pos_iff.mp (by rw [hJmass y hy.le hyone.le]; exact hy)).1
  have hSproper : (volume S).toReal < 1 := hSupper.trans_lt hxy
  have hmain := unitCircle_sum_measure_toReal_lower_bound U hU q φ hφ hsurj
    K (J y) hKmeas (hJopen y).measurableSet hSmeas hKpos hJpos hSproper
  rw [hJmass y hy.le hyone.le] at hmain
  have hKmass : (volume K).toReal = x := by linarith
  have hSmass : (volume S).toReal = x + y := by linarith
  let ε : ℕ → ℝ := fun n => (y / 2) * (1 / ((n : ℝ) + 1))
  have hεpos (n : ℕ) : 0 < ε n := by dsimp only [ε]; positivity
  have hεhalf (n : ℕ) : ε n ≤ y / 2 := by
    have hden : (0 : ℝ) < (n : ℝ) + 1 := by positivity
    have hinv : 1 / ((n : ℝ) + 1) ≤ 1 :=
      (div_le_one hden).mpr (by linarith [Nat.cast_nonneg (α := ℝ) n])
    have hmul := mul_le_mul_of_nonneg_left hinv (show 0 ≤ y / 2 by positivity)
    simpa only [mul_one] using hmul
  have hεlt (n : ℕ) : ε n < y := by linarith [hεhalf n]
  have hεlim : Tendsto ε atTop (𝓝 0) := by
    simpa only [ε, mul_zero] using
      (tendsto_const_nhds.mul (tendsto_one_div_add_atTop_nhds_zero_nat :
        Tendsto (fun n : ℕ => (1 : ℝ) / ((n : ℝ) + 1)) atTop (𝓝 0)))
  let A : ℕ → Set (AddCircle (1 : ℝ)) := fun n => K + J (y - ε n)
  let B : ℕ → Set (AddCircle (1 : ℝ)) := fun n => I (ε n)
  have hOadd (s t : ℝ) (hs : 0 < s) (ht : 0 ≤ t) : O s + I t = O (s + t) :=
    circle_open_arc_add_closed_arc s t hs ht
  have hJadd (s t : ℝ) (hs : 0 < s) (ht : 0 ≤ t) : J s + I t = J (s + t) := by
    calc
      J s + I t = j +ᵥ (O s + I t) := by
        change (j +ᵥ O s) + I t = j +ᵥ (O s + I t)
        ext z
        constructor
        · rintro ⟨_, ⟨u, hu, rfl⟩, v, hv, rfl⟩
          refine ⟨u + v, ⟨u, hu, v, hv, rfl⟩, ?_⟩
          change j + (u + v) = (j + u) + v
          abel
        · rintro ⟨_, ⟨u, hu, v, hv, rfl⟩, rfl⟩
          refine ⟨j + u, ⟨u, hu, rfl⟩, v, hv, ?_⟩
          change (j + u) + v = j + (u + v)
          abel
      _ = J (s + t) := congrArg (fun T : Set (AddCircle (1 : ℝ)) => j +ᵥ T) (hOadd s t hs ht)
  have hAB (n : ℕ) : A n + B n = S := by
    change (K + J (y - ε n)) + I (ε n) = K + J y
    rw [add_assoc, hJadd (y - ε n) (ε n) (sub_pos.mpr (hεlt n)) (hεpos n).le,
      sub_add_cancel]
  have hAopen (n : ℕ) : IsOpen (A n) := (hJopen (y - ε n)).add_left
  have hBcompact (n : ℕ) : IsCompact (B n) := hIcompact (ε n)
  have hAsub (n : ℕ) : A n ⊆ S := by
    apply Set.add_subset_add (Subset.refl K)
    rintro z ⟨t, ⟨r, hr, hrt⟩, rfl⟩
    refine ⟨t, ⟨r, ⟨hr.1, ?_⟩, hrt⟩, rfl⟩
    linarith [hr.2, hεpos n]
  have hAmass (n : ℕ) : (volume (A n)).toReal = x + y - ε n := by
    have hJsmallpos : 0 < volume (J (y - ε n)) := by
      apply (ENNReal.toReal_pos_iff.mp ?_).1
      rw [hJmass (y - ε n) (sub_nonneg.mpr (hεlt n).le) (by linarith [hεpos n])]
      exact sub_pos.mpr (hεlt n)
    have hAproper : (volume (A n)).toReal < 1 :=
      (ENNReal.toReal_mono (measure_ne_top volume S) (measure_mono (hAsub n))).trans_lt hSproper
    have hlower := unitCircle_sum_measure_toReal_lower_bound U hU q φ hφ hsurj
      K (J (y - ε n)) hKmeas (hJopen (y - ε n)).measurableSet
      (hAopen n).measurableSet hKpos hJsmallpos hAproper
    rw [hKmass, hJmass (y - ε n) (sub_nonneg.mpr (hεlt n).le) (by linarith [hεpos n])] at hlower
    have hApos : 0 < volume (A n) := (ENNReal.toReal_pos_iff.mp (by
      have : 0 < x + (y - ε n) := by linarith [hx, hεlt n]
      exact this.trans_le hlower)).1
    have hBpos : 0 < volume (B n) := (ENNReal.toReal_pos_iff.mp (by
      rw [show (volume (B n)).toReal = ε n from hImass (ε n) (hεpos n).le
        (by linarith [hεlt n, hyone])]
      exact hεpos n)).1
    have hupper := unitCircle_sum_measure_toReal_lower_bound U hU q φ hφ hsurj
      (A n) (B n) (hAopen n).measurableSet (hBcompact n).measurableSet
      (by rw [hAB n]; exact hSmeas) hApos hBpos (by rw [hAB n]; exact hSproper)
    rw [hAB n, hSmass, show (volume (B n)).toReal = ε n from hImass (ε n)
      (hεpos n).le (by linarith [hεlt n, hyone])] at hupper
    linarith
  have hBpositive (n : ℕ) : 0 < volume (B n) := (ENNReal.toReal_pos_iff.mp (by
    rw [show (volume (B n)).toReal = ε n from hImass (ε n) (hεpos n).le
      (by linarith [hεlt n, hyone])]
    exact hεpos n)).1
  have hcritical (n : ℕ) : (volume S).toReal = (volume (A n)).toReal + (volume (B n)).toReal := by
    rw [hSmass, hAmass n, show (volume (B n)).toReal = ε n from hImass (ε n)
      (hεpos n).le (by linarith [hεlt n, hyone])]
    ring
  have hSpos : 0 < volume S := (ENNReal.toReal_pos_iff.mp (by rw [hSmass]; linarith)).1
  have hSproperENN : volume S < 1 :=
    (ENNReal.toReal_lt_toReal (measure_ne_top volume S) (by simp)).mp (by simpa using hSproper)
  have hScomp : 0 < volume Sᶜ := by
    apply pos_iff_ne_zero.mpr
    intro hzero
    have htotal := measure_add_measure_compl (μ := volume) hSmeas
    rw [hzero, add_zero, measure_univ] at htotal
    exact hSproperENN.ne htotal
  obtain ⟨c, a, b, _, hab, _, hwidth, hmodelOpen⟩ :=
    unitCircle_ae_arc_of_localized_critical_pairs S hSmeas hSpos hScomp A B
      (fun n => (hBcompact n).measurableSet) hBpositive
      (fun n => (hAB n).subset.eventuallySubset) hcritical
      (circle_closed_arc_differences_shrink ε hεlim)
  have hmodelClosed : UnitCircleClosedArcModel S :=
    ⟨c, a, b, hab, hwidth, hmodelOpen.trans (unitCircle_closedArc_ae_openArc a b).symm⟩
  obtain ⟨start, length, hlengthpos, hlengthone, hmodel⟩ :=
    unitCircle_normalized_closedArcModel S hmodelClosed
  have hlength : length = x + y := by
    have hm := congrArg ENNReal.toReal (measure_congr hmodel)
    rw [hSmass, volume_unitCircle_normalized_closedArc start length hlengthone.le,
      ENNReal.toReal_ofReal hlengthpos.le] at hm
    exact hm.symm
  rw [hlength] at hmodel
  have hKsub : K ⊆ (start - j) +ᵥ I x :=
    unitCircle_left_subset_of_ae_sum_container K (J y) (hJopen y).measurableSet
      (start - j) j x y hx.le hy hxy (hJmodel y)
      (by rw [sub_add_cancel]; exact hmodel.le)
  have hcontainerMass : volume ((start - j) +ᵥ I x) = volume K := by
    apply (ENNReal.toReal_eq_toReal_iff' (measure_ne_top volume _) (measure_ne_top volume _)).mp
    rw [volume_unitCircle_normalized_closedArc (start - j) x (by linarith [hy, hxy]),
      ENNReal.toReal_ofReal hx.le, hKmass]
  have hKae : K =ᵐ[volume] (start - j) +ᵥ I x :=
    ae_eq_of_ae_subset_of_measure_ge hKsub.eventuallySubset hcontainerMass.le
      hKmeas.nullMeasurableSet (measure_ne_top volume _)
  exact ⟨start - j, hKsub, hKae⟩

end Erdos335.Loeb

end
