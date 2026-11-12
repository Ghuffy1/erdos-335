import Erdos335.FiniteQuantizedRefinement
import Mathlib.Algebra.Order.Group.Unbundled.Int

/-!
# Choosing quantization boundaries with small exceptional mass
-/

set_option autoImplicit false

open Finset
open scoped BigOperators Classical

namespace Erdos335.IntermediateScale

noncomputable def boundaryGrid (x : ℝ) (M : ℕ) : Finset (Fin M) :=
  univ.filter fun j => ∃ z : ℤ, |(M : ℝ) * x + j.val - (M : ℝ) * z| < 1 / 3

theorem boundaryGrid_card_le_one (x : ℝ) (M : ℕ) : (boundaryGrid x M).card ≤ 1 := by
  apply card_le_one.mpr
  intro i hi j hj
  obtain ⟨z, hz⟩ := (mem_filter.mp hi).2
  obtain ⟨w, hw⟩ := (mem_filter.mp hj).2
  let t : ℤ := (i.val : ℤ) - j.val - (M : ℤ) * (z - w)
  have ht : |(t : ℝ)| < 1 := by
    have htriangle := abs_sub_le ((M : ℝ) * x + i.val - (M : ℝ) * z) 0
      ((M : ℝ) * x + j.val - (M : ℝ) * w)
    simp only [sub_zero, zero_sub, abs_neg] at htriangle
    have heq : (t : ℝ) = ((M : ℝ) * x + i.val - (M : ℝ) * z) -
        ((M : ℝ) * x + j.val - (M : ℝ) * w) := by dsimp [t]; push_cast; ring
    rw [heq]
    linarith
  have ht0 : t = 0 := Int.abs_lt_one_iff.mp (by exact_mod_cast ht)
  have hiM : (i.val : ℤ) < M := by exact_mod_cast i.isLt
  have hjM : (j.val : ℤ) < M := by exact_mod_cast j.isLt
  have hMp : (0 : ℤ) < M := by omega
  have hd : z - w = 0 := by
    by_contra hne
    rcases lt_or_gt_of_ne hne with hneg | hpos
    · have hle : z - w ≤ -1 := by omega
      have hmul := mul_le_mul_of_nonneg_left hle hMp.le
      dsimp [t] at ht0
      nlinarith
    · have hle : 1 ≤ z - w := by omega
      have hmul := mul_le_mul_of_nonneg_left hle hMp.le
      dsimp [t] at ht0
      nlinarith
  apply Fin.ext
  dsimp [t] at ht0
  rw [hd, mul_zero, sub_zero] at ht0
  exact_mod_cast sub_eq_zero.mp ht0

theorem exists_sparse_boundary_offset {G : Type*} [Fintype G]
    (u : G → ℝ) (M : ℕ) (hM : 0 < M) :
    ∃ j : Fin M, M * (univ.filter (fun x => j ∈ boundaryGrid (u x) M)).card ≤ Fintype.card G := by
  have htotal : (∑ j : Fin M, (univ.filter (fun x : G => j ∈ boundaryGrid (u x) M)).card) ≤
      Fintype.card G := by
    calc
      _ = ∑ x : G, (boundaryGrid (u x) M).card := by
        simp only [card_eq_sum_ones, sum_filter]
        rw [sum_comm]
        apply sum_congr rfl
        intro x hx
        simp
      _ ≤ ∑ _x : G, 1 := sum_le_sum fun x _ => boundaryGrid_card_le_one (u x) M
      _ = _ := by simp
  by_contra! hbad
  have hstrict : (∑ _j : Fin M, Fintype.card G) <
      ∑ j : Fin M, M * (univ.filter (fun x : G => j ∈ boundaryGrid (u x) M)).card := by
    apply sum_lt_sum (fun j _ => (hbad j).le)
    exact ⟨⟨0, hM⟩, mem_univ _, hbad ⟨0, hM⟩⟩
  simp only [sum_const, card_univ, Fintype.card_fin, smul_eq_mul, ← mul_sum] at hstrict
  have hle := Nat.mul_le_mul_left M htotal
  omega

end Erdos335.IntermediateScale
