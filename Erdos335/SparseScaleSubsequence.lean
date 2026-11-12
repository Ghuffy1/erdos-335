import Erdos335.SparsePrefixSubsequence

/-!
# Sparse prefix ratios are preserved by increasing subsequences
-/

set_option autoImplicit false

open Filter Topology

namespace Erdos335.IntermediateScale

theorem sparse_prefix_ratio_subsequence (N : ℕ → ℕ) (hmono : Monotone N)
    (hprev : Tendsto (fun s => (N (s - 1) : ℝ) / N s) atTop (𝓝 0))
    (ρ : ℕ → ℕ) (hρ : StrictMono ρ) :
    Tendsto (fun s => (N (ρ (s - 1)) : ℝ) / N (ρ s)) atTop (𝓝 0) := by
  have hupper : Tendsto (fun s => (N (ρ s - 1) : ℝ) / N (ρ s)) atTop (𝓝 0) :=
    hprev.comp hρ.tendsto_atTop
  apply squeeze_zero' (Eventually.of_forall fun s => by positivity) ?_ hupper
  filter_upwards [eventually_ge_atTop 1] with s hs
  have hslt : s - 1 < s := by omega
  have hρlt := hρ hslt
  have hindices : ρ (s - 1) ≤ ρ s - 1 := by omega
  exact div_le_div_of_nonneg_right (by exact_mod_cast hmono hindices) (Nat.cast_nonneg _)

end Erdos335.IntermediateScale
