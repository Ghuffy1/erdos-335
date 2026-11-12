import Erdos335.FiniteBoundaryGrid

/-!
# Boundary-avoiding shifts of bounded tests
-/

set_option autoImplicit false

open Finset
open scoped BigOperators Classical

namespace Erdos335.IntermediateScale

noncomputable def boundaryShift (N M : ℕ) (j : Fin M) : ℝ :=
  2 * j.val / ((N : ℝ) * M)

noncomputable def shiftedTest (N M : ℕ) (j : Fin M) (u : ℝ) : ℝ :=
  (u + boundaryShift N M j) / 2

def nearQuantizationBoundary (N M : ℕ) (u : ℝ) : Prop :=
  ∃ z : ℤ, |(N : ℝ) * (u + 1) - z| < 1 / (3 * (M : ℝ))

theorem boundaryShift_bounds (N M : ℕ) (hN : 2 ≤ N) (hM : 0 < M) (j : Fin M) :
    boundaryShift N M j ∈ Set.Icc (0 : ℝ) 1 := by
  have hNr : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hMr : (0 : ℝ) < M := by exact_mod_cast hM
  have hj : (j.val : ℝ) < M := by exact_mod_cast j.isLt
  have hN2 : (2 : ℝ) ≤ N := by exact_mod_cast hN
  refine ⟨by dsimp [boundaryShift]; positivity, ?_⟩
  apply (div_le_iff₀ (mul_pos hNr hMr)).mpr
  nlinarith

theorem shiftedTest_bound (N M : ℕ) (hN : 2 ≤ N) (hM : 0 < M)
    (j : Fin M) (u : ℝ) (hu : |u| ≤ 1) : |shiftedTest N M j u| ≤ 1 := by
  have hb := boundaryShift_bounds N M hN hM j
  have hu' := abs_le.mp hu
  apply abs_le.mpr
  dsimp [shiftedTest]
  constructor <;> linarith [hb.1, hb.2, hu'.1, hu'.2]

theorem shiftedTest_boundary_iff (N M : ℕ) (hN : 0 < N) (hM : 0 < M)
    (j : Fin M) (u : ℝ) :
    nearQuantizationBoundary N M (shiftedTest N M j u) ↔
      j ∈ boundaryGrid ((N : ℝ) * (u / 2 + 1)) M := by
  have hNr : (0 : ℝ) < N := by exact_mod_cast hN
  have hMr : (0 : ℝ) < M := by exact_mod_cast hM
  have heq (z : ℤ) : (M : ℝ) * ((N : ℝ) * (shiftedTest N M j u + 1) - z) =
      (M : ℝ) * ((N : ℝ) * (u / 2 + 1)) + j.val - (M : ℝ) * z := by
    dsimp [shiftedTest, boundaryShift]
    field_simp
    ring
  simp only [nearQuantizationBoundary, boundaryGrid, mem_filter, mem_univ, true_and]
  apply exists_congr
  intro z
  rw [← heq, abs_mul, abs_of_pos hMr]
  constructor
  · intro h
    have := (mul_lt_mul_iff_of_pos_left hMr).mpr h
    convert this using 1
    field_simp
  · intro h
    apply (lt_div_iff₀ (by positivity : (0 : ℝ) < 3 * M)).mpr
    nlinarith

theorem exists_boundary_avoiding_shift {G : Type*} [Fintype G]
    (u : G → ℝ) (N M : ℕ) (hN : 2 ≤ N) (hM : 0 < M) :
    ∃ j : Fin M,
      M * (univ.filter (fun x : G => nearQuantizationBoundary N M (shiftedTest N M j (u x)))).card ≤
        Fintype.card G := by
  obtain ⟨j, hj⟩ := exists_sparse_boundary_offset (fun x => (N : ℝ) * (u x / 2 + 1)) M hM
  refine ⟨j, ?_⟩
  simpa only [shiftedTest_boundary_iff N M (by omega) hM j] using hj

theorem shiftedTest_correlation {G : Type*} [Fintype G]
    (r u : G → ℝ) (N M : ℕ) (j : Fin M) (hr : ∑ x : G, r x = 0) :
    (∑ x : G, r x * shiftedTest N M j (u x)) = (∑ x : G, r x * u x) / 2 := by
  calc
    _ = (∑ x : G, r x * u x) / 2 + boundaryShift N M j / 2 * (∑ x : G, r x) := by
      rw [div_eq_mul_inv, sum_mul, mul_sum, ← sum_add_distrib]
      apply sum_congr rfl
      intro x hx
      dsimp [shiftedTest]
      ring
    _ = _ := by rw [hr, mul_zero, add_zero]

end Erdos335.IntermediateScale
