import Erdos335.StrictSubsequenceExtension
import Erdos335.PositiveIntermediateScales
import Erdos335.ReciprocalScaleRatios

/-!
# Intermediate-window control survives strict subsequences
-/

set_option autoImplicit false

open Filter Topology

namespace Erdos335.IntermediateScale

theorem tendsto_subsequence_of_intermediate_control
    (A B : ℕ → ℕ) (hApos : ∀ s, 0 < A s) (hBpos : ∀ s, 0 < B s)
    (hA : Tendsto A atTop atTop)
    (hAB : Tendsto (fun s => (A s : ℝ) / B s) atTop (𝓝 0))
    (f : ℕ → ℕ → ℝ)
    (hcontrol : ∀ W : ℕ → ℕ, (∀ᶠ s in atTop, 0 < W s) →
      Tendsto (fun s => (A s : ℝ) / W s) atTop (𝓝 0) →
      Tendsto (fun s => (W s : ℝ) / B s) atTop (𝓝 0) →
      Tendsto (fun s => f s (W s)) atTop (𝓝 0))
    (σ : ℕ → ℕ) (hσ : StrictMono σ) (W : ℕ → ℕ)
    (hW : ∀ᶠ s in atTop, 0 < W s)
    (hAW : Tendsto (fun s => (A (σ s) : ℝ) / W s) atTop (𝓝 0))
    (hWB : Tendsto (fun s => (W s : ℝ) / B (σ s)) atTop (𝓝 0)) :
    Tendsto (fun s => f (σ s) (W s)) atTop (𝓝 0) := by
  let H := positiveIntermediateScale A B (1 / 2) 0
  have hHpos : ∀ s, 0 < H s := positiveIntermediateScale_pos A B _ _
  have hB := scale_tendsto_atTop_of_smaller A B hA hBpos hAB
  have hBA := reciprocal_scale_ratio_tendsto_atTop A B hApos hBpos hAB
  have hAH : Tendsto (fun s => (A s : ℝ) / H s) atTop (𝓝 0) :=
    positiveIntermediateScale_lower_ratio A B hA hBA _ _ (by norm_num)
  have hHB : Tendsto (fun s => (H s : ℝ) / B s) atTop (𝓝 0) :=
    positiveIntermediateScale_ambient_ratio A B B hA hB hBA
      (Eventually.of_forall fun _ => le_rfl) _ _ (by norm_num) (by norm_num)
  let V := strictSubsequenceExtension σ W H
  have hV : ∀ᶠ s in atTop, 0 < V s :=
    eventually_strictSubsequenceExtension σ hσ W H (fun _ x => 0 < x) hW
      (Eventually.of_forall hHpos)
  have hAV : Tendsto (fun s => (A s : ℝ) / V s) atTop (𝓝 0) :=
    tendsto_strictSubsequenceExtension σ hσ W H (fun s x => (A s : ℝ) / x) 0 hAW hAH
  have hVB : Tendsto (fun s => (V s : ℝ) / B s) atTop (𝓝 0) :=
    tendsto_strictSubsequenceExtension σ hσ W H (fun s x => (x : ℝ) / B s) 0 hWB hHB
  have ht := (hcontrol V hV hAV hVB).comp hσ.tendsto_atTop
  simpa only [Function.comp_def, V, strictSubsequenceExtension_on σ hσ W H] using ht

end Erdos335.IntermediateScale
