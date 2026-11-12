import Erdos335.IntermediateCharacterMeans
import Mathlib.Analysis.Real.Pi.Bounds

/-!
# The intermediate-frequency exclusion

For a character with frequency strictly between `1/(C H)` and `C/H`, the
averages of lengths `C^2 H` and `floor(H/C^2)` are separated by at least one
half when `C ≥ 32` and the short length is positive. This supplies the
inclusion used after (8.26) in Ackelsberg--Richter with explicit constants.
-/

set_option autoImplicit false

open scoped BigOperators

namespace Erdos335.IntermediateScale

noncomputable def unitCharacter (β : ℝ) : ℂ :=
  Complex.exp (Complex.I * (2 * Real.pi * β : ℝ))

theorem unitCharacter_norm (β : ℝ) : ‖unitCharacter β‖ = 1 := by
  exact Complex.norm_exp_I_mul_ofReal _

theorem unitCharacter_sub_one_upper (β : ℝ) :
    ‖unitCharacter β - 1‖ ≤ 2 * Real.pi * |β| := by
  apply (Real.norm_exp_I_mul_ofReal_sub_one_le (x := 2 * Real.pi * β)).trans
  rw [Real.norm_eq_abs, abs_mul, abs_mul, abs_of_pos Real.pi_pos]
  norm_num

theorem unitCharacter_sub_one_lower (β : ℝ) (hβ : |β| ≤ 1 / 2) :
    4 * |β| ≤ ‖unitCharacter β - 1‖ := by
  have hpi : 0 < Real.pi := Real.pi_pos
  have hb : |Real.pi * β| ≤ Real.pi / 2 := by
    rw [abs_mul, abs_of_pos hpi]
    nlinarith
  have hsin := Real.mul_abs_le_abs_sin hb
  have hcancel : 2 / Real.pi * |Real.pi * β| = 2 * |β| := by
    rw [abs_mul, abs_of_pos hpi]
    field_simp
  rw [hcancel] at hsin
  rw [unitCharacter, Complex.norm_exp_I_mul_ofReal_sub_one]
  have heq : 2 * Real.pi * β / 2 = Real.pi * β := by ring
  rw [heq, Real.norm_eq_abs, abs_mul]
  norm_num
  linarith

theorem intermediate_frequency_separation (β : ℝ) (C H : ℕ)
    (hC : 32 ≤ C) (hH : C ^ 2 ≤ H) (hβ : |β| ≤ 1 / 2)
    (hlower : 1 / ((C : ℝ) * H) < |β|)
    (hupper : |β| < (C : ℝ) / H) :
    1 / 2 ≤ ‖characterMean (unitCharacter β) (C ^ 2 * H) -
      characterMean (unitCharacter β) (H / C ^ 2)‖ := by
  have hCnat : 0 < C := by omega
  have hCpos : (0 : ℝ) < C := by exact_mod_cast hCnat
  have hC32 : (32 : ℝ) ≤ C := by exact_mod_cast hC
  have hHnat : 0 < H := lt_of_lt_of_le (pow_pos hCnat _) hH
  have hHpos : (0 : ℝ) < H := by exact_mod_cast hHnat
  have hshort : 0 < H / C ^ 2 := Nat.div_pos hH (pow_pos hCnat _)
  have hlong : 0 < C ^ 2 * H := Nat.mul_pos (pow_pos hCnat _) hHnat
  have hβpos : 0 < |β| := (div_pos zero_lt_one (mul_pos hCpos hHpos)).trans hlower
  have hne : unitCharacter β ≠ 1 := by
    intro heq
    have hl := unitCharacter_sub_one_lower β hβ
    rw [heq, sub_self, norm_zero] at hl
    linarith
  apply characterMean_separation _ (unitCharacter_norm β) hne _ _ hshort hlong
  · have hdiv : ((H / C ^ 2 : ℕ) : ℝ) ≤ (H : ℝ) / (C : ℝ) ^ 2 := by
      have hd := Nat.cast_div_le (α := ℝ) (m := H) (n := C ^ 2)
      push_cast at hd
      exact hd
    calc
      ((H / C ^ 2 : ℕ) : ℝ) * ‖unitCharacter β - 1‖ ≤
          ((H : ℝ) / (C : ℝ) ^ 2) * (2 * Real.pi * |β|) := by
        gcongr
        exact unitCharacter_sub_one_upper β
      _ ≤ ((H : ℝ) / (C : ℝ) ^ 2) * (2 * Real.pi * ((C : ℝ) / H)) := by
        gcongr
      _ = 2 * Real.pi / C := by field_simp
      _ ≤ 1 / 4 := by
        apply (div_le_iff₀ hCpos).mpr
        have := Real.pi_lt_four
        linarith
  · have hmass : 1 < (C : ℝ) * H * |β| := by
      simpa only [mul_comm |β|] using (div_lt_iff₀ (mul_pos hCpos hHpos)).mp hlower
    have hnorm := unitCharacter_sub_one_lower β hβ
    have hbound : 4 * (C : ℝ) ≤ ((C ^ 2 * H : ℕ) : ℝ) * ‖unitCharacter β - 1‖ := by
      push_cast
      nlinarith [mul_nonneg (show 0 ≤ (C : ℝ) ^ 2 * H by positivity)
        (sub_nonneg.mpr hnorm), mul_nonneg hCpos.le (sub_nonneg.mpr hmass.le)]
    linarith

theorem close_character_means_frequency_dichotomy (β : ℝ) (C H : ℕ)
    (hC : 32 ≤ C) (hH : C ^ 2 ≤ H) (hβ : |β| ≤ 1 / 2)
    (hclose : ‖characterMean (unitCharacter β) (C ^ 2 * H) -
      characterMean (unitCharacter β) (H / C ^ 2)‖ < 1 / 2) :
    |β| ≤ 1 / ((C : ℝ) * H) ∨ (C : ℝ) / H ≤ |β| := by
  by_contra! h
  exact (not_lt_of_ge (intermediate_frequency_separation β C H hC hH hβ h.1 h.2)) hclose

end Erdos335.IntermediateScale
