import Erdos335.FiniteTestRegularity
import Erdos335.ShiftedTestBoundaries

/-!
# Weak regularity with few points near every selected cell boundary
-/

set_option autoImplicit false

open Finset
open scoped BigOperators Classical

namespace Erdos335.IntermediateScale

theorem boundary_avoiding_test_regularity
    {G : Type*} [Fintype G] [Nonempty G]
    (f : G → ℝ) (hf : ∀ x, f x ∈ Set.Icc (0 : ℝ) 1)
    (allowed : Set (G → ℝ)) (hallowed : ∀ u ∈ allowed, ∀ x, |u x| ≤ 1)
    (ε : ℝ) (N D M : ℕ) (hN : 2 ≤ N) (hM : 0 < M)
    (hε : 1 / (N : ℝ) ≤ ε / 2)
    (hD : 1 < (D : ℝ) * (ε / 2 - 1 / (N : ℝ)) ^ 2) :
    ∃ S : Finset (G → ℝ), S.card ≤ D ∧
      (∀ v ∈ S, ∃ u ∈ allowed, ∃ j : Fin M, v = fun x => shiftedTest N M j (u x)) ∧
      (∀ v ∈ S, M * (univ.filter (fun x : G => nearQuantizationBoundary N M (v x))).card ≤
        Fintype.card G) ∧
      ∀ u ∈ allowed,
        |∑ x : G, (f x - finiteConditionalMean (testPartition N S) f x) * u x| ≤
          ε * Fintype.card G := by
  choose j hj using (fun u : G → ℝ => exists_boundary_avoiding_shift u N M hN hM)
  let shifted := fun u : G → ℝ => fun x => shiftedTest N M (j u) (u x)
  let shiftedAllowed := shifted '' allowed
  have hshifted : ∀ v ∈ shiftedAllowed, ∀ x, |v x| ≤ 1 := by
    rintro v ⟨u, hu, rfl⟩ x
    exact shiftedTest_bound N M hN hM (j u) (u x) (hallowed u hu x)
  obtain ⟨S, hS, hcard, htests⟩ := finite_test_regularity f hf shiftedAllowed hshifted
    (ε / 2) N D (by omega) hε hD
  refine ⟨S, hcard, ?_, ?_, ?_⟩
  · intro v hv
    obtain ⟨u, hu, hvu⟩ := hS hv
    exact ⟨u, hu, j u, hvu.symm⟩
  · intro v hv
    obtain ⟨u, hu, rfl⟩ := hS hv
    exact hj u
  · intro u hu
    have htest := htests (shifted u) ⟨u, hu, rfl⟩
    have hzero : (∑ x : G, (f x - finiteConditionalMean (testPartition N S) f x)) = 0 := by
      rw [sum_sub_distrib, finiteConditionalMean_sum]
      ring
    have hshift := shiftedTest_correlation
      (fun x => f x - finiteConditionalMean (testPartition N S) f x) u N M (j u) hzero
    change |∑ x : G, (f x - finiteConditionalMean (testPartition N S) f x) *
      shiftedTest N M (j u) (u x)| ≤ ε / 2 * Fintype.card G at htest
    rw [hshift, abs_div] at htest
    norm_num at htest
    linarith

end Erdos335.IntermediateScale
