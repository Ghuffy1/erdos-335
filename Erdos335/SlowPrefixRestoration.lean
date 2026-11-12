import Erdos335.RemovalParameters

/-!
# Initial segments whose restoration cost is sublinear
-/

set_option autoImplicit false

open Filter Topology Finset
open scoped BigOperators

namespace Erdos335.IntermediateScale

noncomputable def finitePrefix (B : Set ℕ) (J : ℕ) : Finset ℕ := by
  classical
  exact (range J).filter (fun b => b ∈ B)

theorem exists_slow_square_prefix (q : ℕ → ℕ) (hq : Tendsto q atTop atTop) :
    ∃ J : ℕ → ℕ, (∀ n, J n ≤ q n) ∧ Tendsto J atTop atTop ∧
      Tendsto (fun n => ((J n : ℝ) ^ 2) / q n) atTop (𝓝 0) := by
  have hd : Tendsto (fun n => (1 : ℝ) / q n) atTop (𝓝 0) :=
    (tendsto_const_div_atTop_nhds_zero_nat 1).comp hq
  let r := fun j : ℕ => 1 / (((j : ℝ) + 1) ^ 3)
  obtain ⟨k, hk, hbound⟩ := ArithmeticRemoval.exists_slow_index_for_positive_thresholds
    (fun n => (1 : ℝ) / q n) r hd (fun j => by dsimp [r]; positivity)
  let J := fun n => min (k n + 1) (q n)
  have hJ : Tendsto J atTop atTop := by
    apply tendsto_atTop.mpr
    intro m
    filter_upwards [hk.eventually (eventually_ge_atTop m),
      hq.eventually (eventually_ge_atTop m)] with n hn hqn
    exact le_min (by omega) hqn
  refine ⟨J, (fun n => min_le_right _ _), hJ, ?_⟩
  have hr : Tendsto (fun n => 1 / ((k n : ℝ) + 1)) atTop (𝓝 0) :=
    tendsto_one_div_add_atTop_nhds_zero_nat.comp hk
  apply squeeze_zero' (Eventually.of_forall fun n => by positivity) ?_ hr
  filter_upwards [hbound, hq.eventually (eventually_gt_atTop 0)] with n hn hqn
  have hqpos : (0 : ℝ) < q n := by exact_mod_cast hqn
  have hkp : (0 : ℝ) < (k n : ℝ) + 1 := by positivity
  have hcub : ((k n : ℝ) + 1) ^ 3 < q n := by
    change 1 / (q n : ℝ) < 1 / (((k n : ℝ) + 1) ^ 3) at hn
    exact (one_div_lt_one_div hqpos (pow_pos hkp _)).mp hn
  have hJle : (J n : ℝ) ≤ (k n : ℝ) + 1 := by
    exact_mod_cast (min_le_left (k n + 1) (q n))
  calc
    (J n : ℝ) ^ 2 / q n ≤ ((k n : ℝ) + 1) ^ 2 / q n := by gcongr
    _ ≤ 1 / ((k n : ℝ) + 1) := by
      apply (div_le_div_iff₀ hqpos hkp).mpr
      nlinarith

theorem prefix_sum_le_square (B : Set ℕ) (J : ℕ) :
    ∑ b ∈ finitePrefix B J, b ≤ J ^ 2 := by
  classical
  unfold finitePrefix
  calc
    _ ≤ ∑ _b ∈ (range J).filter (fun b => b ∈ B), J := by
      apply sum_le_sum
      intro b hb
      exact (mem_range.mp (mem_filter.mp hb).1).le
    _ = ((range J).filter (fun b => b ∈ B)).card * J := by simp
    _ ≤ J * J := Nat.mul_le_mul_right J (by simpa using card_filter_le (range J) (fun b => b ∈ B))
    _ = J ^ 2 := by ring

end Erdos335.IntermediateScale
