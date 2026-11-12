import Erdos335.WindowMeanTransfer

/-!
# Bounded averages from vanishing bad-set proportions

Privately checked supporting development.
The error bound is required only on the finite range being averaged.
-/

set_option autoImplicit false

open Filter Topology Finset
open scoped BigOperators

namespace Erdos335.IntermediateScale

theorem finite_mean_le_threshold_add_bad_fraction
    (e : ℕ → ℝ) (C ε : ℝ) (N : ℕ) (hN : 0 < N) (hε : 0 ≤ ε)
    (hbound : ∀ n, n < N → e n ∈ Set.Icc (0 : ℝ) C) :
    (∑ n ∈ range N, e n) / N ≤
      ε + C * (((range N).filter (fun n => ε ≤ e n)).card : ℝ) / N := by
  classical
  have hpoint (n : ℕ) (hn : n ∈ range N) :
      e n ≤ ε + if ε ≤ e n then C else 0 := by
    by_cases hbad : ε ≤ e n
    · simp only [hbad, ite_true]
      have hupper := (hbound n (mem_range.mp hn)).2
      linarith
    · simpa only [hbad, ite_false, add_zero] using (lt_of_not_ge hbad).le
  have hsum : (∑ n ∈ range N, e n) ≤
      (N : ℝ) * ε + (((range N).filter (fun n => ε ≤ e n)).card : ℝ) * C := by
    calc
      _ ≤ ∑ n ∈ range N, (ε + if ε ≤ e n then C else 0) := sum_le_sum hpoint
      _ = _ := by
        simp only [sum_add_distrib, sum_const, card_range, nsmul_eq_mul,
          sum_ite, mul_zero, add_zero]
  have hNr : (0 : ℝ) < N := by exact_mod_cast hN
  calc
    _ ≤ ((N : ℝ) * ε + (((range N).filter (fun n => ε ≤ e n)).card : ℝ) * C) / N :=
      div_le_div_of_nonneg_right hsum hNr.le
    _ = _ := by field_simp <;> ring

theorem finite_mean_tendsto_zero_of_bad_fractions
    (e : ℕ → ℕ → ℝ) (C : ℝ) (N : ℕ → ℕ) (hN : ∀ s, 0 < N s)
    (hbound : ∀ s n, n < N s → e s n ∈ Set.Icc (0 : ℝ) C)
    (hbad : ∀ ε : ℝ, 0 < ε →
      Tendsto (fun s => (((range (N s)).filter (fun n => ε ≤ e s n)).card : ℝ) / N s)
        atTop (𝓝 0)) :
    Tendsto (fun s => (∑ n ∈ range (N s), e s n) / N s) atTop (𝓝 0) := by
  classical
  apply tendsto_order.mpr
  constructor
  · intro a ha
    apply Eventually.of_forall
    intro s
    have hnonneg : 0 ≤ (∑ n ∈ range (N s), e s n) / N s :=
      div_nonneg (sum_nonneg fun n hn => (hbound s n (mem_range.mp hn)).1)
        (by positivity)
    exact ha.trans_le hnonneg
  · intro ε hε
    have hhalf : 0 < ε / 2 := by linarith
    have hweighted : Tendsto (fun s =>
        C * (((range (N s)).filter (fun n => ε / 2 ≤ e s n)).card : ℝ) / N s)
        atTop (𝓝 0) := by
      simpa only [mul_zero, mul_div_assoc] using (hbad (ε / 2) hhalf).const_mul C
    filter_upwards [hweighted.eventually (gt_mem_nhds hhalf)] with s hs
    have hmean := finite_mean_le_threshold_add_bad_fraction
      (e s) C (ε / 2) (N s) (hN s) hhalf.le (hbound s)
    linarith

end Erdos335.IntermediateScale