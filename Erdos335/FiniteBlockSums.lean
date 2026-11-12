import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Basic.Real.Basic
import Mathlib.Tactic.Ring

/-!
# Exact summation over equal-length integer blocks
-/

set_option autoImplicit false

open Finset
open scoped BigOperators

namespace Erdos335.IntermediateScale

theorem sum_full_blocks {E : Type*} [AddCommMonoid E] (v : ℕ → E) (H m : ℕ) :
    (∑ n ∈ range (H * m), v n) = ∑ b ∈ range m, ∑ i ∈ range H, v (H * b + i) := by
  induction m with
  | zero => simp
  | succ m hm =>
    rw [Nat.mul_succ, sum_range_add, hm, sum_range_succ]

theorem sum_full_blocks_eq_zero {E : Type*} [AddCommMonoid E]
    (v : ℕ → E) (H m : ℕ) (h : ∀ b < m, ∑ i ∈ range H, v (H * b + i) = 0) :
    ∑ n ∈ range (H * m), v n = 0 := by
  rw [sum_full_blocks]
  exact sum_eq_zero fun b hb => h b (mem_range.mp hb)

theorem sum_full_blocks_le (v : ℕ → ℝ) (H m : ℕ) (ε : ℝ)
    (h : ∀ b < m, ∑ i ∈ range H, v (H * b + i) ≤ ε * H) :
    ∑ n ∈ range (H * m), v n ≤ ε * (H * m : ℕ) := by
  rw [sum_full_blocks]
  calc
    _ ≤ ∑ _b ∈ range m, ε * H := sum_le_sum fun b hb => h b (mem_range.mp hb)
    _ = _ := by simp; ring

noncomputable def blockLift (H : ℕ) (hH : 0 < H) (s : ℕ → Fin H → ℝ) (n : ℕ) : ℝ :=
  s (n / H) ⟨n % H, Nat.mod_lt n hH⟩

theorem blockLift_apply (H : ℕ) (hH : 0 < H) (s : ℕ → Fin H → ℝ) (b : ℕ) (i : Fin H) :
    blockLift H hH s (H * b + i.val) = s b i := by
  have hdiv : (H * b + i.val) / H = b := by
    rw [Nat.mul_add_div hH, Nat.div_eq_of_lt i.isLt, add_zero]
  unfold blockLift
  rw [hdiv]
  congr 1
  apply Fin.ext
  simp [Nat.add_mod, Nat.mod_eq_of_lt i.isLt]

end Erdos335.IntermediateScale
