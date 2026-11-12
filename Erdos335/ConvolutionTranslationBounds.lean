import Erdos335.PaddedConvolutionBlocks
import Erdos335.WindowTranslationTransfer

/-!
# Convolution translation bounds on a fixed larger input interval
-/

set_option autoImplicit false

open Finset
open scoped BigOperators

namespace Erdos335.IntermediateScale

theorem backward_window_sum_le (f : ℕ → ℝ) (hf : ∀ k, 0 ≤ f k)
    (n H Q i : ℕ) (hH : 0 < H) (hHQ : H ≤ Q) (hQL : 2 * Q ≤ 3 * H) (hi : i < Q) :
    (∑ m ∈ range Q, f (n + 3 * H + i - m)) ≤ ∑ t ∈ range (6 * H), f (n + t) := by
  classical
  let φ : ℕ → ℕ := fun m => 3 * H + i - m
  have hinj : Set.InjOn φ (range Q) := by
    intro a ha b hb hab
    have ha' := mem_range.mp ha
    have hb' := mem_range.mp hb
    dsimp [φ] at hab
    omega
  have hsub : (range Q).image φ ⊆ range (6 * H) := by
    intro t ht
    obtain ⟨m, hm, rfl⟩ := mem_image.mp ht
    have hm' := mem_range.mp hm
    apply mem_range.mpr
    dsimp [φ]
    omega
  calc
    _ = ∑ m ∈ range Q, f (n + φ m) := by
      apply sum_congr rfl
      intro m hm
      have hm' := mem_range.mp hm
      congr 1
      dsimp [φ]
      omega
    _ = ∑ t ∈ (range Q).image φ, f (n + t) :=
      (sum_image (f := fun t => f (n + t)) hinj).symm
    _ ≤ _ := sum_le_sum_of_subset_of_nonneg hsub (fun t ht hnot => hf _)

theorem linearWindowConvolution_norm_le_abs_average (r : ℕ → ℝ) (g : ℕ → ℂ)
    (hg : ∀ m, ‖g m‖ ≤ 1) (Q n : ℕ) (hQ : 0 < Q) :
    ‖linearWindowConvolution r g Q n‖ ≤ (∑ m ∈ range Q, |r (n - m)|) / Q := by
  unfold linearWindowConvolution
  rw [norm_div, Complex.norm_natCast]
  apply div_le_div_of_nonneg_right _ (by positivity)
  exact (norm_sum_le _ _).trans (sum_le_sum fun m hm => by
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
    exact mul_le_of_le_one_right (abs_nonneg _) (hg m))

theorem linear_convolution_translation_difference (w : ℕ → ℝ) (g : ℕ → ℂ)
    (Q x : ℕ) (hQx : Q ≤ x) :
    linearWindowConvolution w g Q (x + Q) - linearWindowConvolution w g Q x =
      linearWindowConvolution (fun t => w (t + Q) - w t) g Q x := by
  unfold linearWindowConvolution
  rw [← sub_div, ← sum_sub_distrib]
  congr 1
  apply sum_congr rfl
  intro m hm
  have hm' := mem_range.mp hm
  have heq : x + Q - m = x - m + Q := by omega
  rw [heq, Complex.ofReal_sub, sub_mul]

noncomputable def linearConvolutionPeriodError (w : ℕ → ℝ) (g : ℕ → ℂ) (Q start : ℕ) : ℝ :=
  (∑ i ∈ range Q, ‖linearWindowConvolution w g Q (start + Q + i) -
    linearWindowConvolution w g Q (start + i)‖) / Q

theorem structured_convolution_period_bound (w : ℕ → ℝ) (g : ℕ → ℂ)
    (hg : ∀ m, ‖g m‖ ≤ 1) (n H Q : ℕ)
    (hH : 0 < H) (hHQ : H ≤ Q) (hQL : 2 * Q ≤ 3 * H) :
    linearConvolutionPeriodError w g Q (n + 3 * H) ≤
      6 * ((∑ t ∈ range (6 * H), |w (n + t + Q) - w (n + t)|) / (6 * H : ℕ)) := by
  have hQ : 0 < Q := hH.trans_le hHQ
  have hQr : (0 : ℝ) < Q := by exact_mod_cast hQ
  have hHr : (0 : ℝ) < H := by exact_mod_cast hH
  let S : ℝ := ∑ t ∈ range (6 * H), |w (n + t + Q) - w (n + t)|
  have hS : 0 ≤ S := sum_nonneg fun t ht => abs_nonneg _
  have hpoint (i : ℕ) (hi : i < Q) :
      ‖linearWindowConvolution w g Q (n + 3 * H + Q + i) -
        linearWindowConvolution w g Q (n + 3 * H + i)‖ ≤ S / Q := by
    rw [show n + 3 * H + Q + i = (n + 3 * H + i) + Q by omega,
      linear_convolution_translation_difference w g Q _ (by omega)]
    have ht := linearWindowConvolution_norm_le_abs_average (fun t => w (t + Q) - w t) g hg
      Q (n + 3 * H + i) hQ
    apply ht.trans
    apply div_le_div_of_nonneg_right _ hQr.le
    exact backward_window_sum_le (fun t => |w (t + Q) - w t|) (fun t => abs_nonneg _) n H Q i hH hHQ hQL hi
  unfold linearConvolutionPeriodError
  calc
    _ ≤ (∑ _i ∈ range Q, S / Q) / Q :=
      div_le_div_of_nonneg_right (sum_le_sum fun i hi => hpoint i (mem_range.mp hi)) hQr.le
    _ = S / Q := by simp [hQr.ne']
    _ ≤ S / H := div_le_div_of_nonneg_left hS hHr (by exact_mod_cast hHQ)
    _ = _ := by dsimp [S]; push_cast; field_simp

end Erdos335.IntermediateScale
