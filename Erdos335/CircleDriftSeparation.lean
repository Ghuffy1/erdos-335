import Mathlib.Analysis.Normed.Group.AddCircle
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Topology.MetricSpace.HausdorffDistance
import Mathlib.Tactic

/-!
# A separated real interval for a nonzero integral circle drift

Privately checked supporting development.
-/

set_option autoImplicit false

open Filter Set Topology

noncomputable section

namespace Erdos335.Loeb

private theorem integral_drift_Icc_surjective (d : ℤ) (hd : d ≠ 0)
    (z : AddCircle (1 : ℝ)) :
    ∃ t ∈ Icc (0 : ℝ) 1, (((d : ℝ) * t : ℝ) : AddCircle (1 : ℝ)) = z := by
  let w : ℝ := (AddCircle.equivIco (1 : ℝ) 0 z : ℝ)
  have hw : w ∈ Ico (0 : ℝ) 1 := by
    simpa only [w, zero_add] using (AddCircle.equivIco (1 : ℝ) 0 z).property
  have hwz : (w : AddCircle (1 : ℝ)) = z := AddCircle.coe_equivIco
  have hdR : (d : ℝ) ≠ 0 := by exact_mod_cast hd
  by_cases hdpos : 0 < d
  · have hdRpos : (0 : ℝ) < d := by exact_mod_cast hdpos
    have hdRone : (1 : ℝ) ≤ d := by exact_mod_cast (show (1 : ℤ) ≤ d by omega)
    refine ⟨w / (d : ℝ), ⟨div_nonneg hw.1 hdRpos.le, ?_⟩, ?_⟩
    · exact (div_le_one hdRpos).mpr (hw.2.le.trans hdRone)
    · have heq : (d : ℝ) * (w / (d : ℝ)) = w := by field_simp
      rw [heq]
      exact hwz
  · have hdneg : d < 0 := by omega
    have hdRneg : (d : ℝ) < 0 := by exact_mod_cast hdneg
    have hdRminus : (d : ℝ) ≤ -1 := by exact_mod_cast (show d ≤ (-1 : ℤ) by omega)
    refine ⟨(w - 1) / (d : ℝ), ⟨?_, ?_⟩, ?_⟩
    · exact (div_nonneg_iff).2 (Or.inr ⟨by linarith [hw.2], hdRneg.le⟩)
    · exact (div_le_one_of_neg hdRneg).mpr (by linarith [hw.1])
    · have heq : (d : ℝ) * ((w - 1) / (d : ℝ)) = w - 1 := by field_simp
      rw [heq, AddCircle.coe_sub, AddCircle.coe_period, sub_zero]
      exact hwz

private theorem continuous_positive_at_interior
    (g : ℝ → ℝ) (hg : Continuous g) (r : ℝ)
    (hr : r ∈ Icc (0 : ℝ) 1) (hgr : 0 < g r) :
    ∃ t ∈ Ioo (0 : ℝ) 1, 0 < g t := by
  let ε : ℕ → ℝ := fun n => 1 / ((n : ℝ) + 1)
  let x : ℕ → ℝ := fun n => (r + ε n) / (1 + 2 * ε n)
  have hε (n : ℕ) : 0 < ε n := by dsimp only [ε]; positivity
  have hεlim : Tendsto ε atTop (𝓝 0) := tendsto_one_div_add_atTop_nhds_zero_nat
  have hxlim : Tendsto x atTop (𝓝 r) := by
    have hden : Tendsto (fun n => 1 + 2 * ε n) atTop (𝓝 (1 : ℝ)) := by
      simpa only [mul_zero, add_zero] using
        tendsto_const_nhds.add (tendsto_const_nhds.mul hεlim)
    have hnum : Tendsto (fun n => r + ε n) atTop (𝓝 r) := by
      simpa only [add_zero] using tendsto_const_nhds.add hεlim
    have hdiv : Tendsto ((fun n => r + ε n) / (fun n => 1 + 2 * ε n))
        atTop (𝓝 r) := by
      simpa only [div_one] using hnum.div hden (by norm_num : (1 : ℝ) ≠ 0)
    exact hdiv.congr (fun n => rfl)
  have hpositive : ∀ᶠ n in atTop, 0 < g (x n) :=
    ((hg.tendsto r).comp hxlim).eventually (lt_mem_nhds hgr)
  obtain ⟨n, hn⟩ := hpositive.exists
  refine ⟨x n, ⟨?_, ?_⟩, hn⟩
  · exact div_pos (by linarith [hε n, hr.1]) (by linarith [hε n])
  · exact (div_lt_one (by linarith [hε n])).mpr (by linarith [hε n, hr.2])

private theorem continuous_positive_separated_interval
    (g : ℝ → ℝ) (hg : Continuous g) (r : ℝ)
    (hr : r ∈ Ioo (0 : ℝ) 1) (hgr : 0 < g r) :
    ∃ u α β v η : ℝ, 0 ≤ u ∧ u < α ∧ α < β ∧ β < v ∧ v ≤ 1 ∧
      0 < η ∧ ∀ t ∈ Icc u v, η ≤ g t := by
  let η : ℝ := g r / 2
  have hη : 0 < η := by dsimp only [η]; linarith
  have hηr : η < g r := by dsimp only [η]; linarith
  have hopen : IsOpen {t : ℝ | η < g t} := isOpen_lt continuous_const hg
  obtain ⟨δ, hδ, hball⟩ := Metric.mem_nhds_iff.mp (hopen.mem_nhds hηr)
  let b : ℝ := min (δ / 2) (min (r / 2) ((1 - r) / 2))
  have hb : 0 < b := by
    dsimp only [b]
    exact lt_min (by linarith) (lt_min (by linarith [hr.1]) (by linarith [hr.2]))
  have hbδ : b ≤ δ / 2 := min_le_left _ _
  have hbr : b ≤ r / 2 := (min_le_right _ _).trans (min_le_left _ _)
  have hb1 : b ≤ (1 - r) / 2 := (min_le_right _ _).trans (min_le_right _ _)
  refine ⟨r - b, r - b / 2, r + b / 2, r + b, η, ?_, ?_, ?_, ?_, ?_, hη, ?_⟩
  · linarith [hr.1]
  · linarith
  · linarith
  · linarith
  · linarith [hr.2]
  · intro t ht
    have hdist : dist t r < δ := by
      rw [Real.dist_eq]
      have habs : |t - r| ≤ b := abs_le.mpr ⟨by linarith [ht.1], by linarith [ht.2]⟩
      linarith
    exact (hball hdist).le

theorem exists_circle_drift_separated_interval
    (d : ℤ) (hd : d ≠ 0) (J : Set (AddCircle (1 : ℝ)))
    (hJ : IsClosed J) (hJnonempty : J.Nonempty) (hJproper : J ≠ univ) :
    ∃ u α β v η : ℝ, 0 ≤ u ∧ u < α ∧ α < β ∧ β < v ∧ v ≤ 1 ∧
      0 < η ∧ ∀ t ∈ Icc u v, η ≤ Metric.infDist
        ((((d : ℝ) * t : ℝ)) : AddCircle (1 : ℝ)) J := by
  obtain ⟨z, hz⟩ : ∃ z : AddCircle (1 : ℝ), z ∉ J := by
    by_contra h
    apply hJproper
    apply eq_univ_of_forall
    intro z
    by_contra hz
    exact h ⟨z, hz⟩
  obtain ⟨r, hr, hdr⟩ := integral_drift_Icc_surjective d hd z
  let g : ℝ → ℝ := fun t => Metric.infDist
    ((((d : ℝ) * t : ℝ)) : AddCircle (1 : ℝ)) J
  have hg : Continuous g := by
    dsimp only [g]
    exact (Metric.continuous_infDist_pt J).comp
      ((AddCircle.continuous_mk' (1 : ℝ)).comp (continuous_const.mul continuous_id))
  have hgr : 0 < g r := by
    simpa only [g, hdr] using (hJ.notMem_iff_infDist_pos hJnonempty).mp hz
  obtain ⟨t, ht, hgt⟩ := continuous_positive_at_interior g hg r hr hgr
  exact continuous_positive_separated_interval g hg t ht hgt

end Erdos335.Loeb

end
