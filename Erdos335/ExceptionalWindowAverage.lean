import Erdos335.AnnularParameterWindows
import Erdos335.WindowFourierNorm

/-!
# Averaging bounds with exceptional windows at the ends of a prefix
-/

set_option autoImplicit false

open Finset
open scoped BigOperators Classical

namespace Erdos335.IntermediateScale

theorem exceptional_average_bound (v : ℕ → ℝ) (N : ℕ) (hN : 0 < N)
    (E : Finset ℕ) (A : ℝ) (hA : 0 ≤ A)
    (hbound : ∀ n ∈ range N, v n ≤ 1)
    (hgood : ∀ n ∈ range N, n ∉ E → v n ≤ A) :
    (∑ n ∈ range N, v n) / N ≤ A + (E.card : ℝ) / N := by
  have hpoint (n : ℕ) (hn : n ∈ range N) : v n ≤ A + if n ∈ E then 1 else 0 := by
    by_cases h : n ∈ E
    · simpa only [h, ite_true] using (hbound n hn).trans (by linarith)
    · simpa only [h, ite_false, add_zero] using hgood n hn h
  have hcard : ((range N).filter (fun n => n ∈ E)).card ≤ E.card :=
    card_le_card fun n hn => (mem_filter.mp hn).2
  have hsum : (∑ n ∈ range N, v n) ≤ (N : ℝ) * A + E.card := by
    calc
      _ ≤ ∑ n ∈ range N, (A + if n ∈ E then (1 : ℝ) else 0) := sum_le_sum hpoint
      _ = (N : ℝ) * A + ((range N).filter (fun n => n ∈ E)).card := by
        simp only [sum_add_distrib, sum_const, card_range, nsmul_eq_mul,
          sum_ite, mul_one, mul_zero, add_zero]
      _ ≤ _ := by
        have hc : (((range N).filter (fun n => n ∈ E)).card : ℝ) ≤ E.card := by
          exact_mod_cast hcard
        exact add_le_add le_rfl hc
  have hNr : (0 : ℝ) < N := by exact_mod_cast hN
  calc
    _ ≤ ((N : ℝ) * A + E.card) / N := div_le_div_of_nonneg_right hsum hNr.le
    _ = _ := by field_simp

theorem edge_window_count (N L W : ℕ) :
    ((range N).filter (fun n => n < L ∨ N ≤ n + W)).card ≤ L + W := by
  let early := (range N).filter (fun n => n < L)
  let late := (range N).filter (fun n => N ≤ n + W)
  have hsub : (range N).filter (fun n => n < L ∨ N ≤ n + W) ⊆ early ∪ late := by
    intro n hn
    obtain ⟨hn, h | h⟩ := mem_filter.mp hn
    · exact mem_union_left _ (mem_filter.mpr ⟨hn, h⟩)
    · exact mem_union_right _ (mem_filter.mpr ⟨hn, h⟩)
  have hearly : early.card ≤ L := by
    calc
      _ ≤ (range L).card := card_le_card fun n hn => mem_range.mpr (mem_filter.mp hn).2
      _ = L := card_range L
  calc
    _ ≤ (early ∪ late).card := card_le_card hsub
    _ ≤ early.card + late.card := card_union_le _ _
    _ ≤ L + W := Nat.add_le_add hearly (terminal_window_count N W)

theorem windowFourierNorm_congr (r r' : ℕ → ℝ) (n W : ℕ)
    (heq : ∀ i < W, r (n + i) = r' (n + i)) :
    windowFourierNorm r n W = windowFourierNorm r' n W := by
  have hsum (β : ℝ) : (∑ i ∈ range W, (r (n + i) : ℂ) * unitCharacter ((i : ℝ) * β)) =
      ∑ i ∈ range W, (r' (n + i) : ℂ) * unitCharacter ((i : ℝ) * β) := by
    apply sum_congr rfl
    intro i hi
    rw [heq i (mem_range.mp hi)]
  simp only [windowFourierNorm, hsum]

end Erdos335.IntermediateScale
