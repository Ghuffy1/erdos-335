import Erdos335.VariableShiftAverages
import Erdos335.ExceptionalWindowAverage

/-!
# Transfer of approximate periods through a mean-square approximation
-/

set_option autoImplicit false

open Finset
open scoped BigOperators

namespace Erdos335.IntermediateScale

theorem exceptional_average_bound_scaled (v : ℕ → ℝ) (N : ℕ) (hN : 0 < N)
    (E : Finset ℕ) (A B : ℝ) (hA : 0 ≤ A) (hB : 0 ≤ B)
    (hbound : ∀ n ∈ range N, v n ≤ B)
    (hgood : ∀ n ∈ range N, n ∉ E → v n ≤ A) :
    (∑ n ∈ range N, v n) / N ≤ A + B * (E.card : ℝ) / N := by
  have hpoint (n : ℕ) (hn : n ∈ range N) : v n ≤ A + B * if n ∈ E then 1 else 0 := by
    by_cases he : n ∈ E
    · simpa only [he, ite_true, mul_one] using (hbound n hn).trans (by linarith)
    · simpa only [he, ite_false, mul_zero, add_zero] using hgood n hn he
  have hcard : ((range N).filter (fun n => n ∈ E)).card ≤ E.card :=
    Finset.card_le_card fun n hn => (mem_filter.mp hn).2
  have hsum : (∑ n ∈ range N, v n) ≤ (N : ℝ) * A + B * E.card := by
    calc
      _ ≤ ∑ n ∈ range N, (A + B * if n ∈ E then (1 : ℝ) else 0) := sum_le_sum hpoint
      _ = (N : ℝ) * A + B * ((range N).filter (fun n => n ∈ E)).card := by
        simp only [sum_add_distrib, sum_const, card_range, nsmul_eq_mul, ← mul_sum,
          sum_ite, sum_const, mul_one, mul_zero, add_zero]
      _ ≤ _ := add_le_add le_rfl (mul_le_mul_of_nonneg_left (by exact_mod_cast hcard) hB)
  have hNr : (0 : ℝ) < N := by exact_mod_cast hN
  exact (div_le_div_of_nonneg_right hsum hNr.le).trans_eq (by field_simp)

theorem approximation_translation_triangle (u v p q : ℂ) :
    ‖u - v‖ ≤ ‖u - p‖ + ‖p - q‖ + ‖v - q‖ := by
  have heq : u - v = ((u - p) + (p - q)) - (v - q) := by ring
  rw [heq]
  exact (norm_sub_le _ _).trans (add_le_add (norm_add_le _ _) le_rfl)

noncomputable def averagedWindowTranslationError (w : ℕ → ℂ) (Q : ℕ → ℕ) (N W : ℕ) : ℝ :=
  (∑ n ∈ range N, (∑ t ∈ range W, ‖w (n + t + Q n) - w (n + t)‖) / W) / N

theorem window_translation_error_transfer (w P : ℕ → ℂ) (Q : ℕ → ℕ)
    (N W : ℕ) (hN : 0 < N) (hW : 0 < W) (hQ : ∀ n, Q n ≤ 2 * W)
    (C δ A B : ℝ) (hδ : 0 ≤ δ) (hA : 0 ≤ A) (hB : 0 ≤ B)
    (he : ∀ n, ‖w n - P n‖ ≤ C)
    (herror : (∑ n ∈ range N, ‖w n - P n‖ ^ 2) / N ≤ δ ^ 2)
    (E : Finset ℕ)
    (hP : ∀ n ∈ range N, ∀ t < W, ‖P (n + t + Q n) - P (n + t)‖ ≤ B)
    (hPgood : ∀ n ∈ range N, n ∉ E →
      ∀ t < W, ‖P (n + t + Q n) - P (n + t)‖ ≤ A) :
    averagedWindowTranslationError w Q N W ≤
      4 * δ + A + B * (E.card : ℝ) / N + 10 * C * (W : ℝ) / N := by
  have hNr : (0 : ℝ) < N := by exact_mod_cast hN
  have hWr : (0 : ℝ) < W := by exact_mod_cast hW
  let e : ℕ → ℂ := fun n => w n - P n
  have hshift := variable_shifted_error_average_le e C δ he hδ Q N W hN hW hQ herror
  let : NeZero N := ⟨hN.ne'⟩
  have hl1 := finite_l1_of_mean_square (fun n : Fin N => e n.val) δ hδ
    (by simpa only [Fintype.card_fin, Finset.sum_range] using herror)
  have hl1' : (∑ n ∈ range N, ‖e n‖) / N ≤ δ := by
    apply (div_le_iff₀ hNr).mpr
    simpa only [Fintype.card_fin, Finset.sum_range] using hl1
  have hunshift := averaged_window_sum_le (fun n => ‖e n‖) C
    (fun n => ⟨norm_nonneg _, he n⟩) N W hN hW
  let v : ℕ → ℝ := fun n => (∑ t ∈ range W, ‖P (n + t + Q n) - P (n + t)‖) / W
  have hv (n : ℕ) (hn : n ∈ range N) : v n ≤ B := by
    apply (div_le_iff₀ hWr).mpr
    exact (sum_le_sum fun t ht => hP n hn t (mem_range.mp ht)).trans_eq (by simp; ring)
  have hvgood (n : ℕ) (hn : n ∈ range N) (hg : n ∉ E) : v n ≤ A := by
    apply (div_le_iff₀ hWr).mpr
    exact (sum_le_sum fun t ht => hPgood n hn hg t (mem_range.mp ht)).trans_eq (by simp; ring)
  have hpoly := exceptional_average_bound_scaled v N hN E A B hA hB hv hvgood
  have htotal : averagedWindowTranslationError w Q N W ≤
      ((∑ n ∈ range N, (∑ t ∈ range W, ‖e (n + t + Q n)‖) / W) / N) +
      ((∑ n ∈ range N, v n) / N) +
      ((∑ n ∈ range N, (∑ t ∈ range W, ‖e (n + t)‖) / W) / N) := by
    unfold averagedWindowTranslationError
    calc
      _ ≤ (∑ n ∈ range N, (∑ t ∈ range W,
          (‖e (n + t + Q n)‖ + ‖P (n + t + Q n) - P (n + t)‖ + ‖e (n + t)‖)) / W) / N := by
        apply div_le_div_of_nonneg_right _ hNr.le
        apply sum_le_sum
        intro n hn
        apply div_le_div_of_nonneg_right _ hWr.le
        exact sum_le_sum fun t ht => approximation_translation_triangle _ _ _ _
      _ = _ := by simp only [v, sum_add_distrib, add_div]
  have hunshift' := hunshift.trans (add_le_add hl1' (le_refl (C * (W : ℝ) / N)))
  calc
    _ ≤ (3 * δ + 9 * C * (W : ℝ) / N) + (A + B * (E.card : ℝ) / N) +
        (δ + C * (W : ℝ) / N) := htotal.trans (add_le_add (add_le_add hshift hpoly) hunshift')
    _ = _ := by ring

end Erdos335.IntermediateScale
