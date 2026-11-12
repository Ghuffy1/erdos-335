import Erdos335.BlockFourierWindows
import Erdos335.IntegerCircleCharacters

/-!
# Uniform Fourier control on windows longer than the regularity blocks
-/

set_option autoImplicit false

open Finset
open scoped BigOperators

namespace Erdos335.IntermediateScale

theorem unitCharacter_add (α β : ℝ) : unitCharacter (α + β) = unitCharacter α * unitCharacter β := by
  unfold unitCharacter
  rw [← Complex.exp_add]
  congr 1
  push_cast
  ring

theorem window_fourier_shift_norm (r : ℕ → ℝ) (n W : ℕ) (β : ℝ) :
    ‖∑ i ∈ range W, (r (n + i) : ℂ) * unitCharacter ((i : ℝ) * β)‖ =
      ‖∑ i ∈ range W, (r (n + i) : ℂ) * unitCharacter (((n + i : ℕ) : ℝ) * β)‖ := by
  have heq : (∑ i ∈ range W, (r (n + i) : ℂ) * unitCharacter (((n + i : ℕ) : ℝ) * β)) =
      unitCharacter ((n : ℝ) * β) * ∑ i ∈ range W, (r (n + i) : ℂ) * unitCharacter ((i : ℝ) * β) := by
    rw [mul_sum]
    apply sum_congr rfl
    intro i hi
    rw [Nat.cast_add, add_mul, unitCharacter_add]
    ring
  rw [heq, norm_mul, unitCharacter_norm, one_mul]

theorem window_fourier_bound_of_blocks (r : ℕ → ℝ)
    (hr : ∀ n, |r n| ≤ 1) (H n W : ℕ) (hH : 0 < H) (hW : 0 < W)
    (ε : ℝ) (hε0 : 0 ≤ ε) (hε1 : ε ≤ 1)
    (hblock : ∀ (b : ℕ) (β : ℝ),
      ‖∑ i ∈ range H, (r (H * b + i) : ℂ) *
        unitCharacter (((H * b + i : ℕ) : ℝ) * β)‖ ≤ ε * H) (β : ℝ) :
    ‖(∑ i ∈ range W, (r (n + i) : ℂ) * unitCharacter ((i : ℝ) * β)) / (W : ℂ)‖ ≤
      ε + 3 * (H : ℝ) / W := by
  have hWr : (0 : ℝ) < W := by exact_mod_cast hW
  have hnorm (k : ℕ) : ‖(r k : ℂ) * unitCharacter ((k : ℝ) * β)‖ ≤ 1 := by
    simpa only [norm_mul, unitCharacter_norm, mul_one, Complex.norm_real, Real.norm_eq_abs] using hr k
  have hbound := window_norm_bound_of_blocks
    (fun k => (r k : ℂ) * unitCharacter ((k : ℝ) * β)) hnorm H n W hH ε hε0 hε1
    (fun b => hblock b β)
  rw [norm_div, Complex.norm_natCast, window_fourier_shift_norm]
  apply (div_le_iff₀ hWr).mpr
  have heq : (ε + 3 * (H : ℝ) / W) * W = ε * W + 3 * H := by field_simp
  rw [heq]
  exact hbound

end Erdos335.IntermediateScale
