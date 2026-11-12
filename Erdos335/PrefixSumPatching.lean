import Erdos335.PrefixCorrelationPatching

/-!
# Patching nonnegative prefix errors
-/

set_option autoImplicit false

open Finset
open scoped BigOperators

namespace Erdos335.IntermediateScale

theorem prefix_sum_le_of_patching (v w : ℕ → ℝ) (N L : ℕ) (C : ℝ) (hC : 0 ≤ C)
    (hv : ∀ n, v n ∈ Set.Icc (0 : ℝ) C) (hw : ∀ n, w n ∈ Set.Icc (0 : ℝ) C)
    (heq : ∀ n, L ≤ n → n < N → v n = w n) :
    ∑ n ∈ range N, v n ≤ (∑ n ∈ range N, w n) + C * L := by
  have hdiff (n : ℕ) : |v n - w n| ≤ C := by
    apply abs_le.mpr
    constructor <;> linarith [(hv n).1, (hv n).2, (hw n).1, (hw n).2]
  have hsupp (n : ℕ) (hn : L ≤ n) (hN : n < N) : v n - w n = 0 := by
    rw [heq n hn hN, sub_self]
  have h := prefix_supported_abs_sum_bound (fun n => v n - w n) N L C hC hdiff hsupp
  rw [sum_sub_distrib] at h
  have hupper := (le_abs_self _).trans h
  linarith

end Erdos335.IntermediateScale
