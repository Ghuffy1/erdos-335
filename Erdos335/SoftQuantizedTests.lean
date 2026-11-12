import Erdos335.SoftQuantizationCells

/-!
# Mean-square approximation of quantized tests by continuous cells
-/

set_option autoImplicit false

open Finset
open scoped BigOperators Classical Topology

namespace Erdos335.IntermediateScale

def softQuantizedCell (N M : ℕ) (i : Fin (2 * N + 1)) (v : ℝ) : ℝ :=
  softCell M i.val ((N : ℝ) * (v + 1))

theorem softQuantizedCell_continuous (N M : ℕ) (i : Fin (2 * N + 1)) :
    Continuous (softQuantizedCell N M i) :=
  (softCell_continuous M i.val).comp (by fun_prop)

theorem softQuantizedCell_exact (N M : ℕ) (hM : 0 < M)
    (i : Fin (2 * N + 1)) (v : ℝ) (hv : |v| ≤ 1)
    (haway : ¬nearQuantizationBoundary N M v) :
    softQuantizedCell N M i v = if quantizedIndex N v = i then 1 else 0 := by
  have hv' := abs_le.mp hv
  have hnonneg : 0 ≤ (N : ℝ) * (v + 1) := mul_nonneg (Nat.cast_nonneg _) (by linarith)
  have hfloor : ⌊(N : ℝ) * (v + 1)⌋₊ ≤ 2 * N := by
    have hf := Nat.floor_le hnonneg
    have hb : (⌊(N : ℝ) * (v + 1)⌋₊ : ℝ) ≤ 2 * N := by nlinarith
    exact_mod_cast hb
  have hindex : quantizedIndex N v = i ↔ ⌊(N : ℝ) * (v + 1)⌋₊ = i.val := by
    rw [Fin.ext_iff]
    change min _ _ = i.val ↔ _
    rw [min_eq_left hfloor]
  unfold softQuantizedCell
  rw [softCell_eq_indicator M i.val hM _ hnonneg]
  · simp only [hindex]
  · exact fun z => le_of_not_gt (fun hz => haway ⟨z, hz⟩)

theorem softQuantizedCell_error_sum_le {G : Type*} [Fintype G]
    (N M : ℕ) (hM : 0 < M) (i : Fin (2 * N + 1))
    (v : G → ℝ) (hv : ∀ x, |v x| ≤ 1) :
    (∑ x : G, (softQuantizedCell N M i (v x) -
      (if quantizedIndex N (v x) = i then (1 : ℝ) else 0)) ^ 2) ≤
      ((univ.filter fun x : G => nearQuantizationBoundary N M (v x)).card : ℝ) := by
  have hpoint (x : G) : (softQuantizedCell N M i (v x) -
      (if quantizedIndex N (v x) = i then (1 : ℝ) else 0)) ^ 2 ≤
        if nearQuantizationBoundary N M (v x) then 1 else 0 := by
    by_cases hb : nearQuantizationBoundary N M (v x)
    · rw [ite_eq_left hb]
      have hc := softCell_bounds M i.val ((N : ℝ) * (v x + 1))
      change softQuantizedCell N M i (v x) ∈ Set.Icc (0 : ℝ) 1 at hc
      split_ifs <;> nlinarith [hc.1, hc.2]
    · rw [ite_eq_right hb, softQuantizedCell_exact N M hM i (v x) (hv x) hb, sub_self, zero_pow (by omega : 2 ≠ 0)]
  calc
    _ ≤ ∑ x : G, if nearQuantizationBoundary N M (v x) then (1 : ℝ) else 0 :=
      sum_le_sum (fun x _ => hpoint x)
    _ = _ := by simp

end Erdos335.IntermediateScale
