import Erdos335.BlockRegularModel
import Erdos335.PrefixSumPatching
import Erdos335.SparsePrefixStitchingControl

/-!
# Block regularity models stitched across sparse prefix intervals
-/

set_option autoImplicit false

open Filter Topology Finset
open scoped BigOperators

namespace Erdos335.IntermediateScale

variable {F : ℕ → ℝ} {H : ℕ → ℕ} {L : ℕ} {ε : ℝ}

noncomputable def stitchedBlockValue (N : ℕ → ℕ) (hN : Tendsto N atTop atTop)
    (m : ∀ s, BlockRegularModel F (H s) L ε) : ℕ → ℝ :=
  prefixStitch N hN (fun s => (m s).value) id

noncomputable def stitchedBlockPolynomial (N : ℕ → ℕ) (hN : Tendsto N atTop atTop)
    (m : ∀ s, BlockRegularModel F (H s) L ε) (n : ℕ) : ℂ :=
  (m (firstCutIndex N hN n)).polynomial n

theorem stitchedBlockValue_mem (N : ℕ → ℕ) (hN : Tendsto N atTop atTop)
    (m : ∀ s, BlockRegularModel F (H s) L ε) (n : ℕ) :
    stitchedBlockValue N hN m n ∈ Set.Icc (0 : ℝ) 1 := (m _).value_mem n

theorem stitchedBlockPolynomial_norm_le (N : ℕ → ℕ) (hN : Tendsto N atTop atTop)
    (m : ∀ s, BlockRegularModel F (H s) L ε) (n : ℕ) :
    ‖stitchedBlockPolynomial N hN m n‖ ≤ L := (m _).polynomial_norm_le n

theorem stitchedBlock_prefix_approximation
    (N : ℕ → ℕ) (hN : Tendsto N atTop atTop) (hmono : Monotone N)
    (m : ∀ s, BlockRegularModel F (H s) L ε) (s : ℕ) (hHs : 0 < H s) (hNs : 0 < N s) :
    (∑ n ∈ range (N s), ‖(stitchedBlockValue N hN m n : ℂ) - stitchedBlockPolynomial N hN m n‖ ^ 2) /
      N s ≤ ε ^ 2 + ((L : ℝ) + 1) ^ 2 * ((H s : ℝ) / N s + (N (s - 1) : ℝ) / N s) := by
  let v := fun n => ‖(stitchedBlockValue N hN m n : ℂ) - stitchedBlockPolynomial N hN m n‖ ^ 2
  let w := fun n => ‖((m s).value n : ℂ) - (m s).polynomial n‖ ^ 2
  let C := ((L : ℝ) + 1) ^ 2
  have hv (n : ℕ) : v n ∈ Set.Icc (0 : ℝ) C := (m (firstCutIndex N hN n)).error_sq_bound n
  have hw (n : ℕ) : w n ∈ Set.Icc (0 : ℝ) C := (m s).error_sq_bound n
  have heq (n : ℕ) (hlow : N (s - 1) ≤ n) (hhigh : n < N s) : v n = w n := by
    change ‖((m (firstCutIndex N hN n)).value n : ℂ) - (m (firstCutIndex N hN n)).polynomial n‖ ^ 2 = _
    rw [firstCutIndex_eq N hN hmono s n hhigh hlow]
  have hpatch := prefix_sum_le_of_patching v w (N s) (N (s - 1)) C (sq_nonneg _) hv hw heq
  have hdiv := div_le_div_of_nonneg_right hpatch (Nat.cast_nonneg (N s) : (0 : ℝ) ≤ N s)
  have hmain := (m s).prefix_approximation hHs (N s) hNs
  change (∑ n ∈ range (N s), v n) / N s ≤ _
  rw [add_div] at hdiv
  change (∑ n ∈ range (N s), w n) / N s ≤ ε ^ 2 + C * H s / N s at hmain
  calc
    _ ≤ (ε ^ 2 + C * H s / N s) + C * N (s - 1) / N s :=
      hdiv.trans (add_le_add hmain le_rfl)
    _ = _ := by dsimp [C]; ring

theorem stitchedBlock_orthogonality
    (N : ℕ → ℕ) (hN : Tendsto N atTop atTop) (hmono : Monotone N)
    (hratio : Tendsto (fun s => (N (s - 1) : ℝ) / N s) atTop (𝓝 0))
    (hHratio : Tendsto (fun s => (H s : ℝ) / N s) atTop (𝓝 0))
    (hH : ∀ s, 0 < H s) (m : ∀ s, BlockRegularModel F (H s) L ε)
    (hF : ∀ n, F n ∈ Set.Icc (0 : ℝ) 1) :
    Tendsto (fun s => prefixCorrelation (stitchedBlockValue N hN m)
      (fun n => F n - stitchedBlockValue N hN m n) (N s)) atTop (𝓝 0) := by
  apply sparse_prefix_stitch_orthogonality N hN hmono hratio F (fun s => (m s).value) hF
    (fun s => (m s).value_mem)
  rw [tendsto_zero_iff_abs_tendsto_zero]
  exact squeeze_zero (fun s => abs_nonneg _) (fun s => (m s).prefix_orthogonality hF (hH s) (N s)) hHratio

theorem stitchedBlock_mean_preservation
    (N : ℕ → ℕ) (hN : Tendsto N atTop atTop) (hmono : Monotone N)
    (hratio : Tendsto (fun s => (N (s - 1) : ℝ) / N s) atTop (𝓝 0))
    (hHratio : Tendsto (fun s => (H s : ℝ) / N s) atTop (𝓝 0))
    (hH : ∀ s, 0 < H s) (m : ∀ s, BlockRegularModel F (H s) L ε)
    (hF : ∀ n, F n ∈ Set.Icc (0 : ℝ) 1) :
    Tendsto (fun s => prefixCorrelation (fun n => F n - stitchedBlockValue N hN m n)
      (fun _ => 1) (N s)) atTop (𝓝 0) := by
  apply sparse_prefix_stitch_mean N hN hmono hratio F (fun s => (m s).value)
    (fun s => (m s).value_mem)
  rw [tendsto_zero_iff_abs_tendsto_zero]
  exact squeeze_zero (fun s => abs_nonneg _) (fun s => (m s).prefix_mean hF (hH s) (N s)) hHratio

end Erdos335.IntermediateScale
