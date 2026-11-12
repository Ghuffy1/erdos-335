import Erdos335.FourierModelPeriodData
import Erdos335.ConstrainedConvolutionWindows

/-!
# Averaged errors at all prescribed intermediate windows

The starting point remains free.  Subsequent almost-everywhere sampling uses
these nonnegative error averages for each fixed ambient enlargement.
-/

set_option autoImplicit false

open Filter Set Topology Finset
open Erdos335.IntermediateScale
open scoped BigOperators

namespace Erdos335.PeriodicRefinement

theorem exists_prescribed_window_error_data
    {I : Type*} (A B : I → Set ℕ) (N : I → ℕ → ℕ) (L V H : ℕ → ℕ)
    (hN : ∀ i n, 0 < N i n) (hHpos : ∀ n, 0 < H n)
    (hH : Tendsto H atTop atTop)
    (hLH : Tendsto (fun n => (L n : ℝ) / H n) atTop (𝓝 0))
    (hHV : Tendsto (fun n => (H n : ℝ) / V n) atTop (𝓝 0))
    (hHN : ∀ i, Tendsto (fun n => (H n : ℝ) / N i n) atTop (𝓝 0))
    (model : ∀ i, IntermediateFourierModel ((A i).indicator (fun _ => (1 : ℝ))) (N i) L V) :
    ∃ (Q : I → ℕ → ℕ → ℕ) (ε : I → ℕ → ℝ),
      (∀ i n, 0 < ε i n) ∧ (∀ i, Tendsto (ε i) atTop (𝓝 0)) ∧
      (∀ i, ∀ᶠ n in atTop, ∀ s,
        H n ≤ Q i n s ∧ (Q i n s : ℝ) ≤ (1 + ε i n) * H n) ∧
      (∀ i m, 0 < m → ∀ᶠ n in atTop, ∀ s, m ∣ Q i n s) ∧
      (∀ i, Tendsto (fun n => (∑ s ∈ range (N i n),
        linearConvolutionPeriodError ((A i).indicator (fun _ => (1 : ℝ)))
          ((B i).indicator (fun _ => (1 : ℂ))) (Q i n s) (s + 3 * H n)) / N i n)
          atTop (𝓝 0)) := by
  classical
  have hF (i : I) (n : ℕ) : (A i).indicator (fun _ => (1 : ℝ)) n ∈ Icc (0 : ℝ) 1 := by
    by_cases hn : n ∈ A i <;> simp [hn]
  have hdata (i : I) := exists_fourier_model_period_data (model i) (hF i)
    (hN i) H hHpos hH hLH hHV (hHN i)
  choose Q ε hεpos hεlim hQ hdiv hperiod hFourier using hdata
  refine ⟨Q, ε, hεpos, hεlim, hQ, hdiv, ?_⟩
  intro i
  have hhalf : ∀ᶠ n in atTop, ∀ s, H n ≤ Q i n s ∧ 2 * Q i n s ≤ 3 * H n := by
    filter_upwards [hQ i, (hεlim i).eventually
      (gt_mem_nhds (by norm_num : (0 : ℝ) < 1 / 2))] with n hn hε
    intro s
    refine ⟨(hn s).1, ?_⟩
    have hHr : (0 : ℝ) ≤ H n := Nat.cast_nonneg _
    have hreal : (2 : ℝ) * Q i n s ≤ 3 * H n := by nlinarith [(hn s).2]
    exact_mod_cast hreal
  have hB : ∀ n s k : ℕ, ‖(B i).indicator (fun _ => (1 : ℂ)) k‖ ≤ 1 := by
    intro n s k
    by_cases hk : k ∈ B i <;> simp [hk]
  exact convolution_period_average_tendsto_zero
    ((A i).indicator (fun _ => (1 : ℝ))) (model i).structured
    (fun _ _ => (B i).indicator (fun _ => (1 : ℂ))) hB
    (N i) H (hN i) hHpos (Q i) hhalf (hFourier i) (hperiod i)

theorem threshold_fraction_tendsto_zero
    (e : ℕ → ℕ → ℝ) (N : ℕ → ℕ) (hN : ∀ n, 0 < N n)
    (he : ∀ n s, 0 ≤ e n s)
    (hmean : Tendsto (fun n => (∑ s ∈ range (N n), e n s) / N n) atTop (𝓝 0))
    (ε : ℝ) (hε : 0 < ε) :
    Tendsto (fun n => (((range (N n)).filter (fun s => ε ≤ e n s)).card : ℝ) / N n)
      atTop (𝓝 0) := by
  classical
  have hbound (n : ℕ) :
      (((range (N n)).filter (fun s => ε ≤ e n s)).card : ℝ) / N n ≤
        ((∑ s ∈ range (N n), e n s) / N n) / ε := by
    have hsum : ε * (((range (N n)).filter (fun s => ε ≤ e n s)).card : ℝ) ≤
        ∑ s ∈ range (N n), e n s := by
      calc
        _ = ∑ _s ∈ (range (N n)).filter (fun s => ε ≤ e n s), ε := by
          simp only [sum_const, nsmul_eq_mul]
          ring
        _ ≤ ∑ s ∈ (range (N n)).filter (fun s => ε ≤ e n s), e n s :=
          sum_le_sum (fun s hs => (mem_filter.mp hs).2)
        _ ≤ ∑ s ∈ range (N n), e n s :=
          sum_le_sum_of_subset_of_nonneg (filter_subset _ _) (fun s _ _ => he n s)
    have hNr : (0 : ℝ) < N n := by exact_mod_cast hN n
    apply (le_div_iff₀ hε).mpr
    calc
      _ = (ε * (((range (N n)).filter (fun s => ε ≤ e n s)).card : ℝ)) / N n := by ring
      _ ≤ _ := div_le_div_of_nonneg_right hsum hNr.le
  apply squeeze_zero (fun n => div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)) hbound
  simpa only [zero_div] using hmean.div_const ε

end Erdos335.PeriodicRefinement
