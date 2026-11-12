import Erdos335.ShiftedTestBoundaries
import Mathlib.Tactic.FunProp
import Mathlib.Topology.Algebra.Order.Field
import Mathlib.Topology.Instances.Real.Lemmas

/-!
# Continuous approximations to quantization cells
-/

set_option autoImplicit false

open scoped Topology

namespace Erdos335.IntermediateScale

def unitRamp (x : ℝ) : ℝ := min 1 (max 0 x)

theorem unitRamp_bounds (x : ℝ) : unitRamp x ∈ Set.Icc (0 : ℝ) 1 :=
  ⟨le_min zero_le_one (le_max_left _ _), min_le_left _ _⟩

theorem unitRamp_zero {x : ℝ} (hx : x ≤ 0) : unitRamp x = 0 := by
  simp [unitRamp, max_eq_left hx]

theorem unitRamp_one {x : ℝ} (hx : 1 ≤ x) : unitRamp x = 1 := by
  exact min_eq_left (hx.trans (le_max_right _ _))

def softCell (M i : ℕ) (x : ℝ) : ℝ :=
  unitRamp (3 * (M : ℝ) * (x - i)) * unitRamp (3 * (M : ℝ) * ((i : ℝ) + 1 - x))

theorem softCell_continuous (M i : ℕ) : Continuous (softCell M i) := by
  unfold softCell unitRamp
  fun_prop

theorem softCell_bounds (M i : ℕ) (x : ℝ) : softCell M i x ∈ Set.Icc (0 : ℝ) 1 := by
  have hleft := unitRamp_bounds (3 * (M : ℝ) * (x - i))
  have hright := unitRamp_bounds (3 * (M : ℝ) * ((i : ℝ) + 1 - x))
  refine ⟨mul_nonneg hleft.1 hright.1, ?_⟩
  exact (mul_le_mul hleft.2 hright.2 hright.1 zero_le_one).trans_eq (one_mul _)

theorem softCell_zero_of_le (M i : ℕ) (x : ℝ) (hx : x ≤ i) : softCell M i x = 0 := by
  unfold softCell
  rw [unitRamp_zero (mul_nonpos_of_nonneg_of_nonpos (by positivity) (sub_nonpos.mpr hx)), zero_mul]

theorem softCell_zero_of_ge (M i : ℕ) (x : ℝ) (hx : (i : ℝ) + 1 ≤ x) : softCell M i x = 0 := by
  unfold softCell
  rw [unitRamp_zero (mul_nonpos_of_nonneg_of_nonpos (by positivity) (sub_nonpos.mpr hx)), mul_zero]

theorem softCell_eq_indicator (M i : ℕ) (hM : 0 < M) (x : ℝ) (hx : 0 ≤ x)
    (haway : ∀ z : ℤ, 1 / (3 * (M : ℝ)) ≤ |x - z|) :
    softCell M i x = if ⌊x⌋₊ = i then 1 else 0 := by
  have hMr : (0 : ℝ) < 3 * M := by positivity
  by_cases hi : ⌊x⌋₊ = i
  · simp only [hi, ite_true]
    obtain ⟨hlow, hhigh⟩ := (Nat.floor_eq_iff hx).mp hi
    have hleft := haway (i : ℤ)
    have hright := haway ((i : ℤ) + 1)
    simp only [Int.cast_natCast] at hleft
    simp only [Int.cast_add, Int.cast_natCast, Int.cast_one] at hright
    rw [abs_of_nonneg (sub_nonneg.mpr hlow)] at hleft
    rw [abs_of_nonpos (sub_nonpos.mpr hhigh.le), neg_sub] at hright
    have hl : 1 ≤ 3 * (M : ℝ) * (x - i) := by
      have h := (div_le_iff₀ hMr).mp hleft
      nlinarith
    have hr : 1 ≤ 3 * (M : ℝ) * ((i : ℝ) + 1 - x) := by
      have h := (div_le_iff₀ hMr).mp hright
      nlinarith
    rw [softCell, unitRamp_one hl, unitRamp_one hr, mul_one]
  · simp only [hi, ite_false]
    rcases lt_or_gt_of_ne hi with hlt | hgt
    · apply softCell_zero_of_le
      have hxlt := Nat.lt_floor_add_one x
      have hcast : (⌊x⌋₊ : ℝ) + 1 ≤ i := by exact_mod_cast hlt
      linarith
    · apply softCell_zero_of_ge
      have hfloor := Nat.floor_le hx
      have hcast : (i : ℝ) + 1 ≤ ⌊x⌋₊ := by exact_mod_cast hgt
      linarith

end Erdos335.IntermediateScale
