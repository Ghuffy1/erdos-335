import Erdos335.SoftQuantizedTests
import Mathlib.Data.Fintype.Pi

/-!
# Continuous product-cell approximation of a finite factor
-/

set_option autoImplicit false

open Finset
open scoped BigOperators Classical

namespace Erdos335.IntermediateScale

variable {I : Type*} [Fintype I]

noncomputable def softPattern (N M : ℕ) (v : I → ℝ) (r : I → Fin (2 * N + 1)) : ℝ :=
  ∏ i : I, softQuantizedCell N M (r i) (v i)

noncomputable def softPartitionModel (N M : ℕ) (c : (I → Fin (2 * N + 1)) → ℝ)
    (v : I → ℝ) : ℝ := ∑ r : I → Fin (2 * N + 1), c r * softPattern N M v r

theorem softPattern_bounds (N M : ℕ) (v : I → ℝ) (r : I → Fin (2 * N + 1)) :
    softPattern N M v r ∈ Set.Icc (0 : ℝ) 1 := by
  have hbound (i : I) := softCell_bounds M (r i).val ((N : ℝ) * (v i + 1))
  exact ⟨prod_nonneg (fun i _ => (hbound i).1),
    prod_le_one₀ (fun i _ => (hbound i).1) (fun i _ => (hbound i).2)⟩

theorem softPattern_exact (N M : ℕ) (hM : 0 < M) (v : I → ℝ)
    (hv : ∀ i, |v i| ≤ 1) (haway : ∀ i, ¬nearQuantizationBoundary N M (v i))
    (r : I → Fin (2 * N + 1)) :
    softPattern N M v r = if (fun i => quantizedIndex N (v i)) = r then 1 else 0 := by
  unfold softPattern
  by_cases heq : (fun i => quantizedIndex N (v i)) = r
  · rw [ite_eq_left heq]
    apply prod_eq_one
    intro i hi
    rw [softQuantizedCell_exact N M hM (r i) (v i) (hv i) (haway i)]
    simp [congrFun heq i]
  · rw [ite_eq_right heq]
    have hex : ∃ i, quantizedIndex N (v i) ≠ r i := by
      by_contra! h
      exact heq (funext h)
    obtain ⟨i, hi⟩ := hex
    apply prod_eq_zero (mem_univ i)
    rw [softQuantizedCell_exact N M hM (r i) (v i) (hv i) (haway i), ite_eq_right hi]

theorem softPartitionModel_bounds (N M : ℕ) (c : (I → Fin (2 * N + 1)) → ℝ)
    (hc : ∀ r, c r ∈ Set.Icc (0 : ℝ) 1) (v : I → ℝ) :
    softPartitionModel N M c v ∈ Set.Icc (0 : ℝ) (Fintype.card (I → Fin (2 * N + 1))) := by
  have hterm (r : I → Fin (2 * N + 1)) : c r * softPattern N M v r ∈ Set.Icc (0 : ℝ) 1 := by
    have h := softPattern_bounds N M v r
    exact ⟨mul_nonneg (hc r).1 h.1,
      (mul_le_mul (hc r).2 h.2 h.1 zero_le_one).trans_eq (one_mul _)⟩
  constructor
  · exact sum_nonneg fun r _ => (hterm r).1
  · calc
      _ ≤ ∑ _r : I → Fin (2 * N + 1), (1 : ℝ) := sum_le_sum fun r _ => (hterm r).2
      _ = _ := by simp

theorem softPartitionModel_exact (N M : ℕ) (hM : 0 < M)
    (c : (I → Fin (2 * N + 1)) → ℝ) (v : I → ℝ)
    (hv : ∀ i, |v i| ≤ 1) (haway : ∀ i, ¬nearQuantizationBoundary N M (v i)) :
    softPartitionModel N M c v = c (fun i => quantizedIndex N (v i)) := by
  unfold softPartitionModel
  simp_rw [softPattern_exact N M hM v hv haway]
  simp [mul_ite, eq_comm]

theorem softPartitionModel_error_sum_le {G : Type*} [Fintype G]
    (N M : ℕ) (hM : 0 < M) (c : (I → Fin (2 * N + 1)) → ℝ)
    (hc : ∀ r, c r ∈ Set.Icc (0 : ℝ) 1) (v : G → I → ℝ)
    (hv : ∀ x i, |v x i| ≤ 1) :
    (∑ x : G, (softPartitionModel N M c (v x) -
      c (fun i => quantizedIndex N (v x i))) ^ 2) ≤
    ((univ.filter (fun x : G => ∃ i, nearQuantizationBoundary N M (v x i))).card : ℝ) *
      ((Fintype.card (I → Fin (2 * N + 1)) : ℝ) + 1) ^ 2 := by
  let C : ℝ := Fintype.card (I → Fin (2 * N + 1))
  have hpoint (x : G) : (softPartitionModel N M c (v x) -
      c (fun i => quantizedIndex N (v x i))) ^ 2 ≤
      if ∃ i, nearQuantizationBoundary N M (v x i) then (C + 1) ^ 2 else 0 := by
    by_cases hbad : ∃ i, nearQuantizationBoundary N M (v x i)
    · rw [ite_eq_left hbad]
      have hm := softPartitionModel_bounds N M c hc (v x)
      have hl := hc (fun i => quantizedIndex N (v x i))
      have hC : 0 ≤ C := Nat.cast_nonneg _
      change softPartitionModel N M c (v x) ∈ Set.Icc (0 : ℝ) C at hm
      have habs : |softPartitionModel N M c (v x) - c (fun i => quantizedIndex N (v x i))| ≤ C + 1 := by
        apply abs_le.mpr
        constructor <;> linarith [hm.1, hm.2, hl.1, hl.2]
      have hs := pow_le_pow_left₀ (abs_nonneg _) habs 2
      simpa only [sq_abs] using hs
    · rw [ite_eq_right hbad, softPartitionModel_exact N M hM c (v x) (hv x)
        (by simpa only [not_exists] using hbad), sub_self]
      norm_num
  calc
    _ ≤ ∑ x : G, if ∃ i, nearQuantizationBoundary N M (v x i) then (C + 1) ^ 2 else 0 :=
      sum_le_sum fun x _ => hpoint x
    _ = _ := by simp [C, ← sum_filter]

end Erdos335.IntermediateScale
