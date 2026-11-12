import Erdos335.SlowDiagonalSelection
import Erdos335.IntermediateScale
import Erdos335.ReciprocalScaleRatios

/-!
# A common sublinear envelope for countably many macroscopic errors

Private proof development. Verification status is recorded separately. All source and scratch work stays on F:.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000

open Filter Topology Finset
open scoped BigOperators

noncomputable section

namespace Erdos335.IntermediateScale

theorem exists_countable_sublinear_error_scale
    (N : ℕ → ℕ) (hNpos : ∀ n, 0 < N n) (hN : Tendsto N atTop atTop)
    (error : ℕ → ℕ → ℝ)
    (herror : ∀ j, Tendsto (fun n => error j n / N n) atTop (𝓝 0)) :
    ∃ K : ℕ → ℕ, (∀ n, 0 < K n) ∧ Tendsto K atTop atTop ∧
      Tendsto (fun n => (K n : ℝ) / N n) atTop (𝓝 0) ∧
      ∀ j, Tendsto (fun n => error j n / K n) atTop (𝓝 0) := by
  classical
  have hNabs (n : ℕ) : |(N n : ℝ)| = (N n : ℝ) := abs_of_nonneg (Nat.cast_nonneg _)
  have habs (j : ℕ) : Tendsto (fun n => |error j n| / N n) atTop (𝓝 0) := by
    simpa only [abs_div, hNabs, abs_zero] using (herror j).abs
  let P := fun j l n : ℕ => |error j n| / N n ≤ 1 / ((l + 1 : ℕ) : ℝ) ^ 2
  have hP : ∀ l j, j ≤ l → ∀ᶠ n in atTop, P j l n := by
    intro l j _
    have hpositive : (0 : ℝ) < 1 / ((l + 1 : ℕ) : ℝ) ^ 2 := by positivity
    exact ((habs j).eventually (eventually_lt_nhds hpositive)).mono fun _ hn => hn.le
  obtain ⟨index, hindex, _, hgood⟩ := exists_slow_diagonal_for_finite_requirements P hP
  let R := fun n => 1 + ∑ j ∈ range (index n + 1), |error j n|
  have hR : ∀ n, 1 ≤ R n := by
    intro n
    dsimp only [R]
    exact le_add_of_nonneg_right (sum_nonneg fun _ _ => abs_nonneg _)
  have hRnonneg : ∀ n, 0 ≤ R n := fun n => zero_le_one.trans (hR n)
  have hupper : ∀ᶠ n in atTop,
      R n / N n ≤ 1 / (N n : ℝ) + 1 / ((index n + 1 : ℕ) : ℝ) := by
    filter_upwards [hgood] with n hn
    have hsum : (∑ j ∈ range (index n + 1), |error j n| / N n) ≤
        ((index n + 1 : ℕ) : ℝ) * (1 / ((index n + 1 : ℕ) : ℝ) ^ 2) := by
      calc
        _ ≤ ∑ _j ∈ range (index n + 1), (1 / ((index n + 1 : ℕ) : ℝ) ^ 2) := by
          apply sum_le_sum
          intro j hj
          exact hn j (by have hjlt := mem_range.mp hj; omega)
        _ = _ := by simp only [sum_const, card_range, nsmul_eq_mul]
    have hunit : ((index n + 1 : ℕ) : ℝ) * (1 / ((index n + 1 : ℕ) : ℝ) ^ 2) =
        1 / ((index n + 1 : ℕ) : ℝ) := by
      have hne : (((index n + 1 : ℕ) : ℝ)) ≠ 0 := by positivity
      field_simp [hne] <;> ring
    dsimp only [R]
    rw [add_div, sum_div]
    exact add_le_add le_rfl (hsum.trans_eq hunit)
  have hRlim : Tendsto (fun n => R n / N n) atTop (𝓝 0) := by
    have hfirst : Tendsto (fun n => 1 / (N n : ℝ)) atTop (𝓝 0) :=
      (tendsto_const_div_atTop_nhds_zero_nat 1).comp hN
    have hsecond : Tendsto (fun n => 1 / ((index n + 1 : ℕ) : ℝ)) atTop (𝓝 0) :=
      (tendsto_const_div_atTop_nhds_zero_nat 1).comp
        ((tendsto_add_atTop_nat 1).comp hindex)
    exact squeeze_zero' (Eventually.of_forall fun n => div_nonneg (hRnonneg n) (by positivity))
      hupper (by simpa only [add_zero] using hfirst.add hsecond)
  let x := fun n => Real.sqrt (R n / N n)
  let K := fun n => Nat.ceil ((N n : ℝ) * x n) + 1
  have hxnonneg : ∀ n, 0 ≤ x n := fun n => Real.sqrt_nonneg _
  have hxlim : Tendsto x atTop (𝓝 0) := by
    simpa only [x, Function.comp_def, Real.sqrt_zero] using
      (Real.continuous_sqrt.tendsto 0).comp hRlim
  have hKpos : ∀ n, 0 < K n := fun n => Nat.succ_pos _
  have hKreal : ∀ n, (0 : ℝ) < K n := fun n => by exact_mod_cast hKpos n
  have hlow (n : ℕ) : (N n : ℝ) * x n ≤ K n := by
    have h := Nat.le_ceil ((N n : ℝ) * x n)
    dsimp only [K]
    push_cast
    linarith
  have hhigh (n : ℕ) : (K n : ℝ) ≤ (N n : ℝ) * x n + 2 := by
    have h := Nat.ceil_lt_add_one (show 0 ≤ (N n : ℝ) * x n from
      mul_nonneg (Nat.cast_nonneg (N n)) (hxnonneg n))
    dsimp only [K]
    push_cast
    linarith
  have hidentity (n : ℕ) : R n = (N n : ℝ) * (x n) ^ 2 := by
    have hne : ((N n : ℝ)) ≠ 0 := by exact_mod_cast (hNpos n).ne'
    have hx2 : (x n) ^ 2 = R n / N n :=
      Real.sq_sqrt (div_nonneg (hRnonneg n) (by positivity))
    rw [hx2]
    field_simp [hne] <;> ring
  have hRK (n : ℕ) : R n / K n ≤ x n := by
    apply (div_le_iff₀ (hKreal n)).mpr
    have hm := mul_le_mul_of_nonneg_right (hlow n) (hxnonneg n)
    rw [hidentity n]
    nlinarith
  have hRKl : Tendsto (fun n => R n / K n) atTop (𝓝 0) :=
    squeeze_zero (fun n => div_nonneg (hRnonneg n) (hKreal n).le) hRK hxlim
  have hKN : Tendsto (fun n => (K n : ℝ) / N n) atTop (𝓝 0) := by
    have hb (n : ℕ) : (K n : ℝ) / N n ≤ x n + 2 / N n := by
      have hn : (0 : ℝ) < N n := by exact_mod_cast hNpos n
      apply (div_le_iff₀ hn).mpr
      have he : (x n + 2 / N n) * N n = (N n : ℝ) * x n + 2 := by
        field_simp [ne_of_gt hn] <;> ring
      rw [he]
      exact hhigh n
    exact squeeze_zero (fun _ => by positivity) hb
      (by simpa only [add_zero, Function.comp_def] using hxlim.add ((tendsto_const_div_atTop_nhds_zero_nat 2).comp hN))
  have hKtop : Tendsto K atTop atTop := by
    apply tendsto_atTop.mpr
    intro m
    filter_upwards [hN.eventually (eventually_ge_atTop (m * m + 1))] with n hn
    have hprod := mul_nonneg (sub_nonneg.mpr (hlow n))
      (add_nonneg (hKreal n).le (mul_nonneg (Nat.cast_nonneg (N n)) (hxnonneg n)))
    have hRn := mul_le_mul_of_nonneg_left (hR n) (Nat.cast_nonneg (N n))
    have hid := congrArg (fun r : ℝ => (N n : ℝ) * r) (hidentity n)
    have hsq : N n ≤ K n * K n := by exact_mod_cast (show (N n : ℝ) ≤ (K n : ℝ) * K n by nlinarith)
    nlinarith
  refine ⟨K, hKpos, hKtop, hKN, ?_⟩
  intro j
  have hdom : ∀ᶠ n in atTop, |error j n| ≤ R n := by
    filter_upwards [hindex.eventually (eventually_ge_atTop j)] with n hn
    have hterm := single_le_sum (fun k _ => abs_nonneg (error k n))
      (show j ∈ range (index n + 1) by simpa only [mem_range] using Nat.lt_succ_of_le hn)
    dsimp only [R]
    linarith
  have habsK : Tendsto (fun n => |error j n| / K n) atTop (𝓝 0) :=
    squeeze_zero' (Eventually.of_forall fun n => div_nonneg (abs_nonneg _) (hKreal n).le)
      (hdom.mono fun n hn => div_le_div_of_nonneg_right hn (hKreal n).le) hRKl
  have habs' : Tendsto (fun n => |error j n / K n|) atTop (𝓝 0) := by
    have hKabs (n : ℕ) : |(K n : ℝ)| = (K n : ℝ) := abs_of_pos (hKreal n)
    simpa only [abs_div, hKabs] using habsK
  rw [tendsto_zero_iff_abs_tendsto_zero]
  exact habs'

end Erdos335.IntermediateScale

end
