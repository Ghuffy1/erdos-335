import Erdos335.CyclicWindowDensities

/-!
# Comparing normalized counts at nearby lengths
-/

set_option autoImplicit false

open Filter Topology

namespace Erdos335.IntermediateScale

theorem prefix_average_nested_length_error (S : Set ℕ) (p q : ℕ)
    (hp : 0 < p) (hpq : p ≤ q) :
    |(prefixCount S q : ℝ) / q - (prefixCount S p : ℝ) / p| ≤ ((q - p : ℕ) : ℝ) / q := by
  have hq : 0 < q := hp.trans_le hpq
  have hpr : (0 : ℝ) < p := by exact_mod_cast hp
  have hqr : (0 : ℝ) < q := by exact_mod_cast hq
  have hmono : prefixCount S p ≤ prefixCount S q := prefixCount_mono S hpq
  have hinc : prefixCount S q ≤ prefixCount S p + (q - p) := by
    simpa only [Nat.add_sub_of_le hpq] using prefixCount_add_le S p (q - p)
  have hlo : (0 : ℝ) ≤ (prefixCount S p : ℝ) / p := by positivity
  have hhi : (prefixCount S p : ℝ) / p ≤ 1 :=
    (div_le_one hpr).mpr (by exact_mod_cast prefixCount_le S p)
  have hdelta : (0 : ℝ) ≤ (q - p : ℕ) := by positivity
  have hmonor : (prefixCount S p : ℝ) ≤ prefixCount S q := by exact_mod_cast hmono
  have hincr : (prefixCount S q : ℝ) ≤ (prefixCount S p : ℝ) + (q - p : ℕ) := by exact_mod_cast hinc
  have hprodlo := mul_nonneg hlo hdelta
  have hprodhi := mul_le_mul_of_nonneg_right hhi hdelta
  have hnum : |(prefixCount S q : ℝ) - prefixCount S p -
      ((prefixCount S p : ℝ) / p) * (q - p : ℕ)| ≤ (q - p : ℕ) := by
    rw [abs_le]
    constructor <;> nlinarith
  have heq : (prefixCount S q : ℝ) / q - (prefixCount S p : ℝ) / p =
      ((prefixCount S q : ℝ) - prefixCount S p -
        ((prefixCount S p : ℝ) / p) * (q - p : ℕ)) / q := by
    rw [Nat.cast_sub hpq]
    field_simp
    <;> ring
  rw [heq, abs_div, abs_of_pos hqr]
  exact div_le_div_of_nonneg_right hnum hqr.le

theorem prefix_average_length_error (S : Set ℕ) (H p q : ℕ)
    (hH : 0 < H) (hHp : H ≤ p) (hHq : H ≤ q) :
    |(prefixCount S p : ℝ) / p - (prefixCount S q : ℝ) / q| ≤ |(p : ℝ) - q| / H := by
  have hHr : (0 : ℝ) < H := by exact_mod_cast hH
  by_cases hpq : p ≤ q
  · have hb := prefix_average_nested_length_error S p q (hH.trans_le hHp) hpq
    have hd : ((q - p : ℕ) : ℝ) / q ≤ ((q - p : ℕ) : ℝ) / H :=
      div_le_div_of_nonneg_left (by positivity) hHr (by exact_mod_cast hHq)
    have heq : |(p : ℝ) - q| = ((q - p : ℕ) : ℝ) := by
      rw [abs_sub_comm, abs_of_nonneg (sub_nonneg.mpr (by exact_mod_cast hpq)), Nat.cast_sub hpq]
    simpa only [abs_sub_comm, heq] using hb.trans hd
  · have hqp : q ≤ p := le_of_not_ge hpq
    have hb := prefix_average_nested_length_error S q p (hH.trans_le hHq) hqp
    have hd : ((p - q : ℕ) : ℝ) / p ≤ ((p - q : ℕ) : ℝ) / H :=
      div_le_div_of_nonneg_left (by positivity) hHr (by exact_mod_cast hHp)
    have heq : |(p : ℝ) - q| = ((p - q : ℕ) : ℝ) := by
      rw [abs_of_nonneg (sub_nonneg.mpr (by exact_mod_cast hqp)), Nat.cast_sub hqp]
    simpa only [heq] using hb.trans hd

theorem cyclic_window_length_comparison
    (A : ℕ → Set ℕ) (start H : ℕ → ℕ) (p q : ℕ → ℕ+)
    (hH : ∀ s, 0 < H s) (hHp : ∀ s, H s ≤ (p s : ℕ)) (hHq : ∀ s, H s ≤ (q s : ℕ))
    (hnear : Tendsto (fun s => |((p s : ℕ) : ℝ) - (q s : ℕ)| / H s) atTop (𝓝 0)) :
    Tendsto (fun s => ((cyclicWindow (A s) (start s) (p s : ℕ)).card : ℝ) / (p s : ℕ) -
      ((cyclicWindow (A s) (start s) (q s : ℕ)).card : ℝ) / (q s : ℕ)) atTop (𝓝 0) := by
  rw [tendsto_iff_norm_sub_tendsto_zero]
  simp only [sub_zero, Real.norm_eq_abs]
  apply squeeze_zero (fun s => abs_nonneg _) (fun s => ?_) hnear
  simp only [cyclicWindow_card_eq_prefixCount]
  exact prefix_average_length_error (tailShift (A s) (start s)) (H s) (p s : ℕ) (q s : ℕ)
    (hH s) (hHp s) (hHq s)

end Erdos335.IntermediateScale
