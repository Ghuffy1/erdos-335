import Erdos335.ConvolutionPeriodLimits
import Erdos335.InteriorSmallAverage

/-!
# Selecting interior cyclic windows with small convolution translation error
-/

set_option autoImplicit false

open Filter Topology Finset
open scoped BigOperators

namespace Erdos335.IntermediateScale

theorem exists_selected_convolution_windows (A B : Set ℕ) (w : ℕ → ℝ)
    (N H : ℕ → ℕ) (hN : ∀ s, 0 < N s) (hHpos : ∀ s, 0 < H s)
    (hH : Tendsto H atTop atTop)
    (hscale : Tendsto (fun s => (H s : ℝ) / N s) atTop (𝓝 0))
    (Q : ℕ → ℕ → ℕ) (ε : ℕ → ℝ)
    (hε : ∀ s, 0 ≤ ε s) (hεlim : Tendsto ε atTop (𝓝 0))
    (hQ : ∀ᶠ s in atTop, ∀ n, H s ≤ Q s n ∧ (Q s n : ℝ) ≤ (1 + ε s) * H s)
    (hdiv : ∀ M : ℕ, 0 < M → ∀ᶠ s in atTop, ∀ n, M ∣ Q s n)
    (hFourier : Tendsto (fun s => (∑ n ∈ range (N s),
      windowFourierNorm (fun t => A.indicator (fun _ => (1 : ℝ)) t - w t) n (6 * H s)) / N s)
      atTop (𝓝 0))
    (hperiod : Tendsto (fun s => averagedWindowTranslationError (fun n => (w n : ℂ))
      (Q s) (N s) (6 * H s)) atTop (𝓝 0)) :
    ∃ (q : ℕ → ℕ+) (start : ℕ → ℕ),
      (∀ s, H s ≤ (q s : ℕ)) ∧ Tendsto (fun s => (q s : ℕ)) atTop atTop ∧
      Tendsto (fun s => (((q s : ℕ) - H s : ℕ) : ℝ) / (q s : ℕ)) atTop (𝓝 0) ∧
      (∀ M : ℕ, 0 < M → ∀ᶠ s in atTop, M ∣ (q s : ℕ)) ∧
      (∀ s, 0 < start s) ∧
      (∀ᶠ s in atTop, start s + (q s : ℕ) ≤ N s) ∧
      Tendsto (fun s => convolutionTranslationError A B (start s) (q s : ℕ) /
        ((q s : ℕ) : ℝ) ^ 2) atTop (𝓝 0) := by
  classical
  have hhalf : ∀ᶠ s in atTop, ∀ n, H s ≤ Q s n ∧ 2 * Q s n ≤ 3 * H s := by
    filter_upwards [hQ, hεlim.eventually (gt_mem_nhds (by norm_num : (0 : ℝ) < 1 / 2))] with s hs heps
    intro n
    refine ⟨(hs n).1, ?_⟩
    have hr : (2 : ℝ) * Q s n ≤ 3 * H s := by
      have hHnonneg : (0 : ℝ) ≤ H s := by positivity
      nlinarith [(hs n).2]
    exact_mod_cast hr
  let e : ℕ → ℕ → ℝ := fun s n => linearConvolutionPeriodError
    (A.indicator (fun _ => (1 : ℝ))) (B.indicator (fun _ => (1 : ℂ))) (Q s n) (n + 3 * H s)
  have he : ∀ s n, 0 ≤ e s n := by
    intro s n
    unfold e linearConvolutionPeriodError
    positivity
  have hg : ∀ s n m : ℕ, ‖B.indicator (fun _ => (1 : ℂ)) m‖ ≤ 1 := by
    intro s n m
    by_cases hm : m ∈ B <;> simp [hm]
  have hmean : Tendsto (fun s => (∑ n ∈ range (N s), e s n) / N s) atTop (𝓝 0) :=
    convolution_period_average_tendsto_zero (A.indicator (fun _ => (1 : ℝ))) w
      (fun _ _ => B.indicator (fun _ => (1 : ℂ))) hg N H hN hHpos Q hhalf hFourier hperiod
  have htail : Tendsto (fun s => ((6 * H s : ℕ) : ℝ) / N s) atTop (𝓝 0) := by
    simpa only [Nat.cast_mul, Nat.cast_ofNat, mul_div_assoc, mul_zero] using hscale.const_mul 6
  obtain ⟨n, hn, hinside, hsmall⟩ := exists_small_interior_positions e he N (fun s => 6 * H s) hN htail hmean
  let q : ℕ → ℕ+ := fun s => ⟨max (H s) (Q s (n s)), (hHpos s).trans_le (le_max_left _ _)⟩
  let start := fun s => n s + 3 * H s
  have hqH (s : ℕ) : H s ≤ (q s : ℕ) := le_max_left _ _
  have heq : ∀ᶠ s in atTop, (q s : ℕ) = Q s (n s) := by
    filter_upwards [hQ] with s hs
    exact max_eq_right (hs (n s)).1
  have hqtop : Tendsto (fun s => (q s : ℕ)) atTop atTop := by
    apply tendsto_atTop.mpr
    intro b
    filter_upwards [hH.eventually (eventually_ge_atTop b)] with s hs
    exact hs.trans (hqH s)
  have hqgap : Tendsto (fun s => (((q s : ℕ) - H s : ℕ) : ℝ) / (q s : ℕ)) atTop (𝓝 0) := by
    apply squeeze_zero' (Eventually.of_forall fun s => by positivity) ?_ hεlim
    filter_upwards [heq, hQ] with s hqs hs
    rw [Nat.cast_sub (hqH s)]
    apply (div_le_iff₀ (show (0 : ℝ) < (q s : ℕ) by exact_mod_cast (q s).pos)).mpr
    have hbound := (hs (n s)).2
    rw [← hqs] at hbound
    have hlower : (H s : ℝ) ≤ (q s : ℕ) := by exact_mod_cast hqH s
    nlinarith [mul_nonneg (hε s) (sub_nonneg.mpr hlower)]
  refine ⟨q, start, hqH, hqtop, hqgap, ?_, ?_, ?_, ?_⟩
  · intro M hM
    filter_upwards [heq, hdiv M hM] with s hqs hs
    simpa only [hqs] using hs (n s)
  · intro s
    dsimp only [start]
    have hs := hHpos s
    omega
  · filter_upwards [hinside, heq, hhalf] with s hs hqs hq
    dsimp only [start]
    rw [hqs]
    have hb := (hq (n s)).2
    omega
  · apply hsmall.congr'
    filter_upwards [heq, hhalf] with s hqs hq
    dsimp only [e, start]
    rw [← hqs]
    symm
    exact convolutionTranslationError_eq_linear A B (q s : ℕ) (n s + 3 * H s) (by
      have hb := (hq (n s)).2
      rw [← hqs] at hb
      omega)

end Erdos335.IntermediateScale
