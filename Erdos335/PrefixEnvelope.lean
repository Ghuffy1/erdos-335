import Erdos335.DensityLimits

/-!
# Uniform prefix errors for moving windows

Ordinary density gives a sublinear envelope for every prefix up to a cutoff.
The envelope controls all windows inside that cutoff simultaneously.
-/

set_option autoImplicit false

open Filter Topology

namespace Erdos335

noncomputable def prefixError (A : Set ℕ) (d : ℝ) (N : ℕ) : ℝ :=
  (Finset.range (N + 1)).sup' (by simp) (fun n => |(count A n : ℝ) - d * n|)

theorem count_error_le_prefixError (A : Set ℕ) (d : ℝ) {n N : ℕ} (hn : n ≤ N) :
    |(count A n : ℝ) - d * n| ≤ prefixError A d N := by
  exact Finset.le_sup' (fun n => |(count A n : ℝ) - d * n|)
    (Finset.mem_range.mpr (by omega))

theorem prefixError_nonneg (A : Set ℕ) (d : ℝ) (N : ℕ) : 0 ≤ prefixError A d N :=
  (abs_nonneg _).trans (count_error_le_prefixError A d (show 0 ≤ N by omega))

theorem HasDensity.uniform_linear_error {A : Set ℕ} {d : ℝ} (hA : HasDensity A d)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ n : ℕ, |(count A n : ℝ) - d * n| ≤ ε * n + C := by
  have ht : Tendsto (fun n : ℕ => |(count A n : ℝ) / n - d|) atTop (𝓝 0) := by
    simpa only [sub_self, abs_zero] using
      (hA.sub (tendsto_const_nhds : Tendsto (fun _ : ℕ => d) atTop (𝓝 d))).abs
  obtain ⟨K, hK⟩ := eventually_atTop.mp (ht.eventually (gt_mem_nhds hε))
  let C := prefixError A d (K + 1)
  have hC : 0 ≤ C := prefixError_nonneg A d (K + 1)
  refine ⟨C, hC, ?_⟩
  intro n
  by_cases hn : n ≤ K + 1
  · exact (count_error_le_prefixError A d hn).trans
      (le_add_of_nonneg_left (mul_nonneg hε.le (Nat.cast_nonneg n)))
  · have hnr : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
    have hsmall := hK n (by omega)
    calc
      |(count A n : ℝ) - d * n| = |((count A n : ℝ) / n - d) * n| := by
        congr 1
        field_simp
      _ = |(count A n : ℝ) / n - d| * n := by rw [abs_mul, abs_of_pos hnr]
      _ ≤ ε * n := mul_le_mul_of_nonneg_right hsmall.le hnr.le
      _ ≤ ε * n + C := le_add_of_nonneg_right hC

theorem prefixError_le_of_linear_error (A : Set ℕ) (d ε C : ℝ) (hε : 0 ≤ ε)
    (hbound : ∀ n : ℕ, |(count A n : ℝ) - d * n| ≤ ε * n + C) (N : ℕ) :
    prefixError A d N ≤ ε * N + C := by
  apply Finset.sup'_le
  intro n hn
  have hnN : n ≤ N := by have := Finset.mem_range.mp hn; omega
  have hnR : (n : ℝ) ≤ N := by exact_mod_cast hnN
  have hm := mul_le_mul_of_nonneg_left hnR hε
  linarith [hbound n]

theorem HasDensity.prefixError_tendsto_zero {A : Set ℕ} {d : ℝ} (hA : HasDensity A d) :
    Tendsto (fun N : ℕ => prefixError A d N / N) atTop (𝓝 0) := by
  apply tendsto_order.2
  constructor
  · intro a ha
    exact Eventually.of_forall fun N => ha.trans_le (div_nonneg (prefixError_nonneg A d N) (Nat.cast_nonneg N))
  · intro b hb
    have hb2 : 0 < b / 2 := by linarith
    obtain ⟨C, hC, hbound⟩ := hA.uniform_linear_error hb2
    have hlim := tendsto_const_div_atTop_nhds_zero_nat C
    filter_upwards [hlim.eventually (gt_mem_nhds hb2), eventually_ge_atTop 1] with N hCN hN
    have hNR : (0 : ℝ) < N := by exact_mod_cast hN
    have he := prefixError_le_of_linear_error A d (b / 2) C hb2.le hbound N
    have hdiv := div_le_div_of_nonneg_right he hNR.le
    have heq : (b / 2 * N + C) / N = b / 2 + C / N := by field_simp
    rw [heq] at hdiv
    linarith

theorem window_error_le_prefixError (A : Set ℕ) (d : ℝ) {n L N : ℕ} (hnL : n + L ≤ N) :
    |(count A (n + L) : ℝ) - count A n - d * L| ≤ 2 * prefixError A d N := by
  have hn : n ≤ N := by omega
  have hleft := count_error_le_prefixError A d hnL
  have hright := count_error_le_prefixError A d hn
  have htriangle : |((count A (n + L) : ℝ) - d * (n + L)) -
      ((count A n : ℝ) - d * n)| ≤ |(count A (n + L) : ℝ) - d * (n + L)| +
        |(count A n : ℝ) - d * n| := by
    simpa only [sub_zero, zero_sub, abs_neg] using
      abs_sub_le ((count A (n + L) : ℝ) - d * (n + L)) 0 ((count A n : ℝ) - d * n)
  have heq : ((count A (n + L) : ℝ) - d * (n + L)) -
      ((count A n : ℝ) - d * n) = (count A (n + L) : ℝ) - count A n - d * L := by
    ring
  rw [heq] at htriangle
  rw [Nat.cast_add] at hleft
  linarith

end Erdos335
