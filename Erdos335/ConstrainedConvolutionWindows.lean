import Erdos335.ConstrainedJointSelection
import Erdos335.SelectedPeriodNormalization

/-!
# Convolution models selected within prescribed positive-density starts
-/

set_option autoImplicit false

open Filter Topology Finset
open scoped BigOperators

namespace Erdos335.IntermediateScale

theorem joint_convolution_windows_from_selected_errors {I : Type*}
    (A B : I → Set ℕ) (N H n : ℕ → ℕ)
    (hHpos : ∀ s, 0 < H s) (hH : Tendsto H atTop atTop)
    (hinside : ∀ᶠ s in atTop, n s + 6 * H s ≤ N s)
    (Q : I → ℕ → ℕ → ℕ) (ε : I → ℕ → ℝ)
    (hε : ∀ i s, 0 ≤ ε i s) (hεlim : ∀ i, Tendsto (ε i) atTop (𝓝 0))
    (hQ : ∀ i, ∀ᶠ s in atTop, ∀ t,
      H s ≤ Q i s t ∧ (Q i s t : ℝ) ≤ (1 + ε i s) * H s)
    (hdiv : ∀ i M, 0 < M → ∀ᶠ s in atTop, ∀ t, M ∣ Q i s t)
    (herror : ∀ i, Tendsto (fun s => linearConvolutionPeriodError
      ((A i).indicator (fun _ => (1 : ℝ))) ((B i).indicator (fun _ => (1 : ℂ)))
        (Q i s (n s)) (n s + 3 * H s)) atTop (𝓝 0)) :
    ∃ q : I → ℕ → ℕ+, ∀ i,
      (∀ s, H s ≤ (q i s : ℕ)) ∧ Tendsto (fun s => (q i s : ℕ)) atTop atTop ∧
      Tendsto (fun s => (((q i s : ℕ) - H s : ℕ) : ℝ) / (q i s : ℕ)) atTop (𝓝 0) ∧
      (∀ M : ℕ, 0 < M → ∀ᶠ s in atTop, M ∣ (q i s : ℕ)) ∧
      (∀ᶠ s in atTop, n s + 3 * H s + (q i s : ℕ) ≤ N s) ∧
      Tendsto (fun s => convolutionTranslationError (A i) (B i) (n s + 3 * H s) (q i s : ℕ) /
        ((q i s : ℕ) : ℝ) ^ 2) atTop (𝓝 0) := by
  classical
  have hn (i : I) := exists_normalized_selected_period N H n hHpos hH hinside
    (Q i) (ε i) (hε i) (hεlim i) (hQ i) (hdiv i)
  choose q hq using hn
  refine ⟨q, ?_⟩
  intro i
  obtain ⟨hHq, hqtop, hqgap, hqdiv, hqinside, hqeq⟩ := hq i
  refine ⟨hHq, hqtop, hqgap, hqdiv, hqinside, ?_⟩
  apply (herror i).congr'
  filter_upwards [hqeq] with s hs
  rw [← hs.1]
  symm
  exact convolutionTranslationError_eq_linear (A i) (B i) (q i s : ℕ) (n s + 3 * H s) (by omega)

theorem exists_joint_convolution_windows_in_dense_sets {I : Type*} [Fintype I]
    (A B : I → Set ℕ) (w : I → ℕ → ℝ)
    (N H : ℕ → ℕ) (hN : ∀ s, 0 < N s) (hHpos : ∀ s, 0 < H s)
    (hH : Tendsto H atTop atTop)
    (hscale : Tendsto (fun s => (H s : ℝ) / N s) atTop (𝓝 0))
    (Q : I → ℕ → ℕ → ℕ) (ε : I → ℕ → ℝ)
    (hε : ∀ i s, 0 ≤ ε i s) (hεlim : ∀ i, Tendsto (ε i) atTop (𝓝 0))
    (hQ : ∀ i, ∀ᶠ s in atTop, ∀ n,
      H s ≤ Q i s n ∧ (Q i s n : ℝ) ≤ (1 + ε i s) * H s)
    (hdiv : ∀ i M, 0 < M → ∀ᶠ s in atTop, ∀ n, M ∣ Q i s n)
    (hFourier : ∀ i, Tendsto (fun s => (∑ n ∈ range (N s),
      windowFourierNorm (fun t => (A i).indicator (fun _ => (1 : ℝ)) t - w i t) n (6 * H s)) / N s)
      atTop (𝓝 0))
    (hperiod : ∀ i, Tendsto (fun s => averagedWindowTranslationError (fun n => (w i n : ℂ))
      (Q i s) (N s) (6 * H s)) atTop (𝓝 0))
    (S : ℕ → Finset ℕ) (hS : ∀ s, S s ⊆ range (N s))
    (δ : ℝ) (hδ : 0 < δ) (hcard : ∀ᶠ s in atTop, δ ≤ ((S s).card : ℝ) / N s) :
    ∃ (n : ℕ → ℕ) (q : I → ℕ → ℕ+),
      (∀ s, n s < N s) ∧ (∀ᶠ s in atTop, n s ∈ S s) ∧ ∀ i,
      (∀ s, H s ≤ (q i s : ℕ)) ∧ Tendsto (fun s => (q i s : ℕ)) atTop atTop ∧
      Tendsto (fun s => (((q i s : ℕ) - H s : ℕ) : ℝ) / (q i s : ℕ)) atTop (𝓝 0) ∧
      (∀ M : ℕ, 0 < M → ∀ᶠ s in atTop, M ∣ (q i s : ℕ)) ∧
      (∀ᶠ s in atTop, n s + 3 * H s + (q i s : ℕ) ≤ N s) ∧
      Tendsto (fun s => convolutionTranslationError (A i) (B i) (n s + 3 * H s) (q i s : ℕ) /
        ((q i s : ℕ) : ℝ) ^ 2) atTop (𝓝 0) := by
  let e : I → ℕ → ℕ → ℝ := fun i s n => linearConvolutionPeriodError
    ((A i).indicator (fun _ => (1 : ℝ))) ((B i).indicator (fun _ => (1 : ℂ)))
      (Q i s n) (n + 3 * H s)
  have he : ∀ i s n, 0 ≤ e i s n := by
    intro i s n
    unfold e linearConvolutionPeriodError
    positivity
  have hhalf (i : I) : ∀ᶠ s in atTop, ∀ n, H s ≤ Q i s n ∧ 2 * Q i s n ≤ 3 * H s := by
    filter_upwards [hQ i, (hεlim i).eventually
      (gt_mem_nhds (by norm_num : (0 : ℝ) < 1 / 2))] with s hs heps
    intro n
    refine ⟨(hs n).1, ?_⟩
    have hHr : (0 : ℝ) ≤ H s := by positivity
    have hreal : (2 : ℝ) * Q i s n ≤ 3 * H s := by nlinarith [(hs n).2]
    exact_mod_cast hreal
  have hmean (i : I) : Tendsto (fun s => (∑ n ∈ range (N s), e i s n) / N s)
      atTop (𝓝 0) := by
    have hg : ∀ s n m : ℕ, ‖(B i).indicator (fun _ => (1 : ℂ)) m‖ ≤ 1 := by
      intro s n m
      by_cases hm : m ∈ B i <;> simp [hm]
    exact convolution_period_average_tendsto_zero ((A i).indicator (fun _ => (1 : ℝ))) (w i)
      (fun _ _ => (B i).indicator (fun _ => (1 : ℂ))) hg N H hN hHpos (Q i)
      (hhalf i) (hFourier i) (hperiod i)
  have htail : Tendsto (fun s => ((6 * H s : ℕ) : ℝ) / N s) atTop (𝓝 0) := by
    simpa only [Nat.cast_mul, Nat.cast_ofNat, mul_div_assoc, mul_zero] using hscale.const_mul 6
  obtain ⟨n, hn, hinside, hsmall⟩ := exists_common_small_interior_positions_in_dense_sets e he
    N (fun s => 6 * H s) hN S hS δ hδ hcard htail hmean
  obtain ⟨q, hq⟩ := joint_convolution_windows_from_selected_errors A B N H n hHpos hH
    (hinside.mono fun s hs => hs.2) Q ε hε hεlim hQ hdiv hsmall
  exact ⟨n, q, hn, hinside.mono (fun s hs => hs.1), hq⟩

end Erdos335.IntermediateScale
