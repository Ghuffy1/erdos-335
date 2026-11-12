import Erdos335.PopularSumsetContainer
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Data.Nat.Find

/-!
# Choosing vanishing deletion rates above prescribed popularity thresholds
-/

set_option autoImplicit false

open Filter Topology

noncomputable section

namespace Erdos335.ArithmeticRemoval

theorem exists_slow_index_for_positive_thresholds
    (d r : ℕ → ℝ) (hd : Tendsto d atTop (𝓝 0)) (hr : ∀ j, 0 < r j) :
    ∃ k : ℕ → ℕ, Tendsto k atTop atTop ∧ ∀ᶠ n in atTop, d n < r (k n) := by
  classical
  have hthreshold (j : ℕ) : ∃ N : ℕ, ∀ n ≥ N, d n < r j :=
    eventually_atTop.mp (hd.eventually (eventually_lt_nhds (hr j)))
  choose N hN using hthreshold
  let M : ℕ → ℕ := fun j => max j (N j)
  let k : ℕ → ℕ := fun n => Nat.findGreatest (fun j => M j ≤ n) n
  have hk : Tendsto k atTop atTop := by
    apply tendsto_atTop.mpr
    intro j
    filter_upwards [eventually_ge_atTop (M j)] with n hn
    exact Nat.le_findGreatest ((le_max_left j (N j)).trans hn) hn
  refine ⟨k, hk, ?_⟩
  filter_upwards [eventually_ge_atTop (M 0)] with n hn
  have hkn : M (k n) ≤ n := Nat.findGreatest_spec (P := fun j => M j ≤ n) (Nat.zero_le n) hn
  exact hN (k n) n ((le_max_right (k n) (N (k n))).trans hkn)

theorem exists_vanishing_removal_parameters
    (d : ℕ → ℝ) (hd : Tendsto d atTop (𝓝 0)) :
    ∃ ε : ℕ → ℝ, (∀ n, 0 < ε n) ∧ Tendsto ε atTop (𝓝 0) ∧
      ∀ᶠ n in atTop, d n ≤ popularRemovalBound (ε n) := by
  let r : ℕ → ℝ := fun j => popularRemovalBound (1 / ((j : ℝ) + 1))
  have hr (j : ℕ) : 0 < r j := popularRemovalBound_pos _ (by positivity)
  obtain ⟨k, hk, hbound⟩ := exists_slow_index_for_positive_thresholds d r hd hr
  let ε : ℕ → ℝ := fun n => 1 / ((k n : ℝ) + 1)
  refine ⟨ε, (fun n => by dsimp [ε]; positivity), ?_, hbound.mono (fun _ hn => hn.le)⟩
  exact (tendsto_one_div_add_atTop_nhds_zero_nat :
    Tendsto (fun j : ℕ => 1 / ((j : ℝ) + 1)) atTop (𝓝 0)).comp hk

end Erdos335.ArithmeticRemoval

end
