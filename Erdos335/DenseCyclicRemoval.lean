import Erdos335.CyclicWindowDensities
import Erdos335.ConvolutionPeriodWindowRemoval

/-!
# Dense cyclic models obtained from convolution periods
-/

set_option autoImplicit false

open Filter Topology Finset
open scoped BigOperators Pointwise

namespace Erdos335.IntermediateScale

theorem exists_dense_cyclic_removal (A B : Set ℕ) (a b c : ℝ) (hB : HasDensity B b)
    (N H q start : ℕ → ℕ) [∀ s, NeZero (q s)] (hH : ∀ s, 0 < H s)
    (hHq : ∀ s, H s ≤ q s) (hq : Tendsto q atTop atTop)
    (hstart : ∀ᶠ s in atTop, 0 < start s)
    (hinside : ∀ᶠ s in atTop, start s + q s ≤ N s)
    (hAerror : Tendsto (fun s => prefixError A a (N s) / H s) atTop (𝓝 0))
    (hCerror : Tendsto (fun s => prefixError (A + B) c (N s) / H s) atTop (𝓝 0))
    (hperiod : Tendsto (fun s => convolutionTranslationError A B (start s) (q s) /
      (q s : ℝ) ^ 2) atTop (𝓝 0)) :
    ∃ A' B' : ∀ s, Finset (ZMod (q s)),
      (∀ s, A' s ⊆ cyclicWindow A (start s) (q s) ∧ B' s ⊆ cyclicWindow B 0 (q s)) ∧
      (∀ v ∈ B, ∀ᶠ s in atTop, (v : ZMod (q s)) ∈ B' s) ∧
      Tendsto (fun s => ((A' s).card : ℝ) / q s) atTop (𝓝 a) ∧
      Tendsto (fun s => ((B' s).card : ℝ) / q s) atTop (𝓝 b) ∧
      Tendsto (fun s => ((cyclicWindow (A + B) (start s) (q s)).card : ℝ) / q s) atTop (𝓝 c) ∧
      Tendsto (fun s => ((cyclicWindow A (start s) (q s) \ A' s).card : ℝ) / q s) atTop (𝓝 0) ∧
      Tendsto (fun s => ((cyclicWindow B 0 (q s) \ B' s).card : ℝ) / q s) atTop (𝓝 0) ∧
      Tendsto (fun s => (((A' s + B' s) \ cyclicWindow (A + B) (start s) (q s)).card : ℝ) / q s)
        atTop (𝓝 0) := by
  have htransfer (S : Set ℕ) (d : ℝ)
      (herror : Tendsto (fun s => prefixError S d (N s) / H s) atTop (𝓝 0)) :
      Tendsto (fun s => prefixError S d (N s) / q s) atTop (𝓝 0) := by
    apply squeeze_zero (fun s => div_nonneg (prefixError_nonneg S d (N s)) (Nat.cast_nonneg _))
      (fun s => ?_) herror
    exact div_le_div_of_nonneg_left (prefixError_nonneg S d (N s))
      (by exact_mod_cast hH s) (by exact_mod_cast hHq s)
  have hAdensity := cyclic_window_density_of_prefix_error A a N q start hstart hinside
    (htransfer A a hAerror)
  have hCdensity := cyclic_window_density_of_prefix_error (A + B) c N q start hstart hinside
    (htransfer (A + B) c hCerror)
  have hBdensity : Tendsto (fun s => ((cyclicWindow B 0 (q s)).card : ℝ) / q s) atTop (𝓝 b) := by
    have hp := ((hasDensity_iff_prefixCount B b).mp hB).comp hq
    simpa [cyclicWindow_card_eq_prefixCount, tailShift, Function.comp_def] using hp
  obtain ⟨A', B', hsub, hexhaust, hAloss, hBloss, hsum⟩ :=
    cyclic_window_removal_of_convolution_periods A B q start hq hperiod
  exact ⟨A', B', hsub, hexhaust,
    density_of_small_removed_subset q (fun s => cyclicWindow A (start s) (q s)) A'
      (fun s => (hsub s).1) a hAdensity hAloss,
    density_of_small_removed_subset q (fun s => cyclicWindow B 0 (q s)) B'
      (fun s => (hsub s).2) b hBdensity hBloss,
    hCdensity, hAloss, hBloss, hsum⟩

end Erdos335.IntermediateScale
