import Erdos335.CircleLocalizedEndpoints
import Erdos335.TranslatedCompactPairs

/-!
# Real translation parameters from shrinking circle difference sets
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter Topology MeasureTheory
open scoped Pointwise

namespace Erdos335.Loeb

theorem exists_unitCircle_difference_sequence
    (B : ℕ → Set (AddCircle (1 : ℝ)))
    (hB : ∀ n, MeasurableSet (B n)) (hpositive : ∀ n, 0 < volume (B n))
    (hlocal : ∀ V ∈ 𝓝 (0 : AddCircle (1 : ℝ)), ∀ᶠ n in atTop, B n - B n ⊆ V)
    (ε : ℕ → ℝ) (hε : ∀ n, 0 < ε n) :
    ∃ N : ℕ, ∃ t : ℕ → ℝ,
      (∀ n, 0 < t n ∧ t n < 1 ∧
        ∃ x ∈ B (n + N), ∃ y ∈ B (n + N),
          (t n : AddCircle (1 : ℝ)) = x - y ∧
          (volume (B (n + N))).toReal ≤ (1 + ε n) * t n) ∧
      Tendsto t atTop (𝓝 0) := by
  classical
  have : Fact (0 < (1 : ℝ)) := ⟨zero_lt_one⟩
  choose b hb using fun n => nonempty_of_measure_ne_zero (hpositive n).ne'
  obtain ⟨N, hN⟩ := eventually_atTop.mp
    (hlocal (Metric.ball 0 (1 / 4)) (Metric.ball_mem_nhds 0 (by norm_num)))
  let D (n : ℕ) : Set (AddCircle (1 : ℝ)) := -(b (n + N)) +ᵥ B (n + N)
  have hDsubset (n : ℕ) : D n ⊆ B (n + N) - B (n + N) := by
    rintro z ⟨w, hw, rfl⟩
    exact ⟨w, hw, b (n + N), hb (n + N), by simp [vadd_eq_add, sub_eq_add_neg, add_comm]⟩
  have hDm (n : ℕ) : MeasurableSet (D n) := by
    dsimp [D]
    rw [vadd_set_eq_neg_preimage]
    exact (hB (n + N)).preimage (measurable_const.add measurable_id)
  have hmass (n : ℕ) : volume (D n) = volume (B (n + N)) := by
    dsimp [D]
    rw [vadd_set_eq_neg_preimage, measure_preimage_add]
  have hDpositive (n : ℕ) : 0 < volume (D n) := by rw [hmass]; exact hpositive _
  have hDsmall (n : ℕ) : D n ⊆ Metric.ball 0 (1 / 4 : ℝ) :=
    (hDsubset n).trans (hN (n + N) (Nat.le_add_left N n))
  have hDlocal : ∀ V ∈ 𝓝 (0 : AddCircle (1 : ℝ)), ∀ᶠ n in atTop, D n ⊆ V := by
    intro V hV
    filter_upwards [(tendsto_add_atTop_nat N).eventually (hlocal V hV)] with n hn
    exact (hDsubset n).trans hn
  obtain ⟨x, y, hxy, hlimit⟩ := exists_unitCircle_localized_endpoints D hDm hDpositive
    hDsmall hDlocal ε hε
  refine ⟨N, fun n => y n - x n, ?_, hlimit⟩
  intro n
  obtain ⟨hx, hy, hpos, hlt, hbound⟩ := hxy n
  obtain ⟨u, hu, heu⟩ := hx
  obtain ⟨v, hv, hev⟩ := hy
  refine ⟨hpos, hlt, v, hv, u, hu, ?_, ?_⟩
  · rw [AddCircle.coe_sub, ← hev, ← heu]
    change (-(b (n + N)) + v) - (-(b (n + N)) + u) = v - u
    abel
  · simpa only [hmass] using hbound

end Erdos335.Loeb
