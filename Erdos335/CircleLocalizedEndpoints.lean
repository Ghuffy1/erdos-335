import Erdos335.CenteredCircleLift
import Erdos335.RealSetEndpointWidth

/-!
# Short real endpoint differences for localized circle sets
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter Topology MeasureTheory

namespace Erdos335.Loeb

theorem exists_unitCircle_localized_endpoints
    (B : ℕ → Set (AddCircle (1 : ℝ)))
    (hB : ∀ n, MeasurableSet (B n)) (hpositive : ∀ n, 0 < volume (B n))
    (hsmall : ∀ n, B n ⊆ Metric.ball 0 (1 / 4 : ℝ))
    (hlocal : ∀ V ∈ 𝓝 (0 : AddCircle (1 : ℝ)), ∀ᶠ n in atTop, B n ⊆ V)
    (ε : ℕ → ℝ) (hε : ∀ n, 0 < ε n) :
    ∃ x y : ℕ → ℝ,
      (∀ n, (x n : AddCircle (1 : ℝ)) ∈ B n ∧
        (y n : AddCircle (1 : ℝ)) ∈ B n ∧ 0 < y n - x n ∧ y n - x n < 1 ∧
        (volume (B n)).toReal ≤ (1 + ε n) * (y n - x n)) ∧
      Tendsto (fun n => y n - x n) atTop (𝓝 0) := by
  let C (n : ℕ) : Set ℝ :=
    ((↑) : ℝ → AddCircle (1 : ℝ)) ⁻¹' B n ∩ Ioc (-(1 / 2 : ℝ)) (1 / 2)
  have hmeasure (n : ℕ) : volume (C n) = volume (B n) :=
    volume_centered_circle_lift (B n) (hB n)
  have hCsmall (n : ℕ) : C n ⊆ Ioo (-(1 / 4 : ℝ)) (1 / 4) :=
    centered_circle_lift_in_small_interval (B n) (1 / 4) (hsmall n)
  have hbelow (n : ℕ) : BddBelow (C n) :=
    ⟨-(1 / 4), fun z hz => (hCsmall n hz).1.le⟩
  have habove (n : ℕ) : BddAbove (C n) :=
    ⟨1 / 4, fun z hz => (hCsmall n hz).2.le⟩
  have hCpos (n : ℕ) : 0 < volume (C n) := by rw [hmeasure]; exact hpositive n
  choose x hx y hy hxy hbound using
    fun n => exists_endpoints_cover_measure (C n) (hbelow n) (habove n) (hCpos n) (ε n) (hε n)
  have hconverges (z : ℕ → ℝ) (hz : ∀ n, z n ∈ C n) : Tendsto z atTop (𝓝 0) := by
    apply Metric.tendsto_nhds.mpr
    intro δ hδ
    filter_upwards [hlocal (Metric.ball 0 δ) (Metric.ball_mem_nhds 0 hδ)] with n hn
    have hinterval := centered_circle_lift_in_small_interval (B n) δ hn (hz n)
    simpa only [Real.dist_eq, sub_zero, abs_lt, mem_Ioo] using hinterval
  refine ⟨x, y, ?_, ?_⟩
  · intro n
    refine ⟨(hx n).1, (hy n).1, sub_pos.mpr (hxy n), ?_, ?_⟩
    · have hleft := hCsmall n (hx n)
      have hright := hCsmall n (hy n)
      linarith [hleft.1, hright.2]
    · simpa only [hmeasure] using hbound n
  · simpa only [sub_zero] using (hconverges y hy).sub (hconverges x hx)

end Erdos335.Loeb
