import Erdos335.WindowFourierNorm

/-!
# Fourier control after a short extension of a window
-/

set_option autoImplicit false

open Finset
open scoped BigOperators

namespace Erdos335.IntermediateScale

theorem windowFourierNorm_extend (r : ℕ → ℝ) (hr : ∀ n, |r n| ≤ 1)
    (n H V : ℕ) (hH : 0 < H) (hHV : H ≤ V) :
    windowFourierNorm r n V ≤ windowFourierNorm r n H + (V - H : ℕ) / (V : ℝ) := by
  have hV : 0 < V := hH.trans_le hHV
  have hHr : (0 : ℝ) < H := by exact_mod_cast hH
  have hVr : (0 : ℝ) < V := by exact_mod_cast hV
  apply windowFourierNorm_le_of_coefficients
  intro β
  let f : ℕ → ℂ := fun i => (r (n + i) : ℂ) * unitCharacter ((i : ℝ) * β)
  have hf (i : ℕ) : ‖f i‖ ≤ 1 := by
    simpa only [f, norm_mul, unitCharacter_norm, mul_one, Complex.norm_real, Real.norm_eq_abs] using hr (n + i)
  have hp : ‖∑ i ∈ range H, f i‖ ≤ windowFourierNorm r n H * H := by
    have h := le_ciSup (window_fourier_coefficients_bddAbove r n H) β
    rw [norm_div, Complex.norm_natCast] at h
    exact (div_le_iff₀ hHr).mp h
  have ht : ‖∑ i ∈ range (V - H), f (H + i)‖ ≤ (V - H : ℕ) := by
    exact (norm_sum_le _ _).trans ((sum_le_sum fun i hi => hf (H + i)).trans_eq (by simp))
  have hsum : (∑ i ∈ range V, f i) = (∑ i ∈ range H, f i) +
      ∑ i ∈ range (V - H), f (H + i) := by
    simpa only [Nat.add_sub_of_le hHV] using sum_range_add f H (V - H)
  rw [norm_div, Complex.norm_natCast]
  apply (div_le_iff₀ hVr).mpr
  calc
    _ = ‖∑ i ∈ range V, f i‖ := rfl
    _ ≤ windowFourierNorm r n H * H + (V - H : ℕ) := by
      rw [hsum]
      exact (norm_add_le _ _).trans (add_le_add hp ht)
    _ ≤ windowFourierNorm r n H * V + (V - H : ℕ) :=
      add_le_add (mul_le_mul_of_nonneg_left (by exact_mod_cast hHV) (windowFourierNorm_nonneg r n H)) le_rfl
    _ = _ := by field_simp

theorem windowFourierNorm_extend_ratio (r : ℕ → ℝ) (hr : ∀ n, |r n| ≤ 1)
    (n H V : ℕ) (hH : 0 < H) (hHV : H ≤ V) (ε : ℝ) (hε : 0 ≤ ε)
    (hsize : (V : ℝ) ≤ (1 + ε) * H) :
    windowFourierNorm r n V ≤ windowFourierNorm r n H + ε := by
  have hV : (0 : ℝ) < V := by exact_mod_cast hH.trans_le hHV
  have htail : ((V - H : ℕ) : ℝ) / V ≤ ε := by
    apply (div_le_iff₀ hV).mpr
    rw [Nat.cast_sub hHV]
    have hHVr : (H : ℝ) ≤ V := by exact_mod_cast hHV
    nlinarith [mul_nonneg hε (sub_nonneg.mpr hHVr)]
  exact (windowFourierNorm_extend r hr n H V hH hHV).trans (add_le_add le_rfl htail)

end Erdos335.IntermediateScale
