import Mathlib.Analysis.Normed.Group.AddCircle
import Mathlib.Topology.MetricSpace.Pseudo.Defs
import Mathlib.Tactic

/-!
# Shrinking circle arcs and mixed interval sums

Private proof development. Verification status is recorded separately.
-/

set_option autoImplicit false

open Filter Set Topology
open scoped Pointwise

noncomputable section

namespace Erdos335.Loeb

theorem circle_closed_arc_differences_shrink
    (ε : ℕ → ℝ) (hε : Tendsto ε atTop (𝓝 0)) :
    ∀ V ∈ 𝓝 (0 : AddCircle (1 : ℝ)), ∀ᶠ n in atTop,
      (((↑) : ℝ → AddCircle (1 : ℝ)) '' Icc 0 (ε n)) -
        (((↑) : ℝ → AddCircle (1 : ℝ)) '' Icc 0 (ε n)) ⊆ V := by
  intro V hV
  have hcoe : Tendsto (fun t : ℝ => (t : AddCircle (1 : ℝ)))
      (𝓝 (0 : ℝ)) (𝓝 (0 : AddCircle (1 : ℝ))) := by
    simpa only [map_zero, QuotientAddGroup.coe_mk'] using
      (AddCircle.continuous_mk' (1 : ℝ)).tendsto (0 : ℝ)
  have hpre : ((↑) : ℝ → AddCircle (1 : ℝ)) ⁻¹' V ∈ 𝓝 (0 : ℝ) := hcoe hV
  obtain ⟨δ, hδ, hball⟩ := Metric.mem_nhds_iff.mp hpre
  filter_upwards [hε.eventually (gt_mem_nhds hδ)] with n hn
  rintro z ⟨x, ⟨u, hu, rfl⟩, y, ⟨v, hv, rfl⟩, rfl⟩
  have habs : |u - v| ≤ ε n := abs_le.mpr ⟨by linarith [hu.1, hv.2],
    by linarith [hu.2, hv.1]⟩
  have hin : u - v ∈ Metric.ball (0 : ℝ) δ := by
    rw [Metric.mem_ball, Real.dist_eq, sub_zero]
    exact habs.trans_lt hn
  have hmem := hball hin
  simpa only [Set.mem_preimage, AddCircle.coe_sub] using hmem

private theorem real_open_closed_interval_sum (a b : ℝ) (ha : 0 < a) (hb : 0 ≤ b) :
    Ioo (0 : ℝ) a + Icc 0 b = Ioo 0 (a + b) := by
  ext t
  constructor
  · rintro ⟨u, hu, v, hv, rfl⟩
    exact ⟨by linarith [hu.1, hv.1], by linarith [hu.2, hv.2]⟩
  · intro ht
    have hsum : 0 < a + b := by linarith
    have hratio0 : 0 < t / (a + b) := div_pos ht.1 hsum
    have hratio1 : t / (a + b) < 1 := (div_lt_one hsum).mpr ht.2
    refine ⟨a * (t / (a + b)), ⟨mul_pos ha hratio0, ?_⟩,
      b * (t / (a + b)), ⟨mul_nonneg hb hratio0.le, ?_⟩, ?_⟩
    · simpa only [mul_one] using mul_lt_mul_of_pos_left hratio1 ha
    · simpa only [mul_one] using mul_le_mul_of_nonneg_left hratio1.le hb
    · field_simp [hsum.ne'] <;> ring

theorem circle_open_arc_add_closed_arc
    (a b : ℝ) (ha : 0 < a) (hb : 0 ≤ b) :
    (((↑) : ℝ → AddCircle (1 : ℝ)) '' Ioo 0 a) +
      (((↑) : ℝ → AddCircle (1 : ℝ)) '' Icc 0 b) =
        (((↑) : ℝ → AddCircle (1 : ℝ)) '' Ioo 0 (a + b)) := by
  ext z
  constructor
  · rintro ⟨x, ⟨u, hu, rfl⟩, y, ⟨v, hv, rfl⟩, rfl⟩
    refine ⟨u + v, ⟨by linarith [hu.1, hv.1], by linarith [hu.2, hv.2]⟩, ?_⟩
    exact AddCircle.coe_add (1 : ℝ) u v
  · rintro ⟨t, ht, rfl⟩
    have hreal : t ∈ Ioo (0 : ℝ) a + Icc 0 b := by
      rw [real_open_closed_interval_sum a b ha hb]
      exact ht
    obtain ⟨u, hu, v, hv, huv⟩ := hreal
    refine ⟨(u : AddCircle (1 : ℝ)), ⟨u, hu, rfl⟩,
      (v : AddCircle (1 : ℝ)), ⟨v, hv, rfl⟩, ?_⟩
    change u + v = t at huv
    change (u : AddCircle (1 : ℝ)) + (v : AddCircle (1 : ℝ)) = (t : AddCircle (1 : ℝ))
    rw [← AddCircle.coe_add, huv]

end Erdos335.Loeb

end
