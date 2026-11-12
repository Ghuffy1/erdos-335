import Erdos335.SoftPartitionApproximation
import Erdos335.FiniteTestRegularity

/-!
# Quantitative continuous approximation of a finite conditional average
-/

set_option autoImplicit false

open Finset
open scoped BigOperators Classical

namespace Erdos335.IntermediateScale

theorem finiteFiberMean_bounds {G K : Type*} [Fintype G] [Fintype K] [DecidableEq K]
    (π : G → K) (f : G → ℝ) (hf : ∀ x, f x ∈ Set.Icc (0 : ℝ) 1) (k : K) :
    finiteFiberMean π f k ∈ Set.Icc (0 : ℝ) 1 := by
  by_cases h : (finiteFiber π k).Nonempty
  · obtain ⟨x, hx⟩ := h
    have hπ : π x = k := (mem_filter.mp hx).2
    simpa only [finiteConditionalMean, hπ] using finiteConditionalMean_bounds π f hf x
  · have he : finiteFiber π k = ∅ := not_nonempty_iff_eq_empty.mp h
    simp [finiteFiberMean, he]

theorem boundary_union_card_bound {G I : Type*} [Fintype G] [Fintype I]
    (P : G → I → Prop) (M : ℕ)
    (hP : ∀ i, M * (univ.filter (fun x => P x i)).card ≤ Fintype.card G) :
    M * (univ.filter (fun x => ∃ i, P x i)).card ≤ Fintype.card I * Fintype.card G := by
  have heq : (univ.filter (fun x : G => ∃ i, P x i)) =
      univ.biUnion (fun i : I => univ.filter (fun x : G => P x i)) := by ext x; simp
  rw [heq]
  calc
    _ ≤ M * ∑ i : I, (univ.filter (fun x : G => P x i)).card :=
      Nat.mul_le_mul_left M card_biUnion_le
    _ = ∑ i : I, M * (univ.filter (fun x : G => P x i)).card := by rw [mul_sum]
    _ ≤ ∑ _i : I, Fintype.card G := sum_le_sum fun i _ => hP i
    _ = _ := by simp

theorem softPartitionModel_normalized_error {G I : Type*} [Fintype G] [Nonempty G] [Fintype I]
    (N M : ℕ) (hM : 0 < M) (c : (I → Fin (2 * N + 1)) → ℝ)
    (hc : ∀ r, c r ∈ Set.Icc (0 : ℝ) 1) (v : G → I → ℝ)
    (hv : ∀ x i, |v x i| ≤ 1)
    (hboundary : ∀ i, M * (univ.filter (fun x : G => nearQuantizationBoundary N M (v x i))).card ≤
      Fintype.card G) :
    (∑ x : G, (softPartitionModel N M c (v x) - c (fun i => quantizedIndex N (v x i))) ^ 2) /
      Fintype.card G ≤
      (Fintype.card I : ℝ) / M * ((Fintype.card (I → Fin (2 * N + 1)) : ℝ) + 1) ^ 2 := by
  have hsum := softPartitionModel_error_sum_le N M hM c hc v hv
  have hbad := boundary_union_card_bound (fun x i => nearQuantizationBoundary N M (v x i)) M hboundary
  have hGpos : (0 : ℝ) < Fintype.card G := by exact_mod_cast Fintype.card_pos
  have hMpos : (0 : ℝ) < M := by exact_mod_cast hM
  have hfrac : ((univ.filter (fun x : G => ∃ i, nearQuantizationBoundary N M (v x i))).card : ℝ) /
      Fintype.card G ≤ (Fintype.card I : ℝ) / M := by
    apply (div_le_div_iff₀ hGpos hMpos).mpr
    rw [mul_comm] at hbad
    exact_mod_cast hbad
  calc
    _ ≤ (((univ.filter (fun x : G => ∃ i, nearQuantizationBoundary N M (v x i))).card : ℝ) *
        ((Fintype.card (I → Fin (2 * N + 1)) : ℝ) + 1) ^ 2) / Fintype.card G :=
      div_le_div_of_nonneg_right hsum hGpos.le
    _ = (((univ.filter (fun x : G => ∃ i, nearQuantizationBoundary N M (v x i))).card : ℝ) /
        Fintype.card G) * ((Fintype.card (I → Fin (2 * N + 1)) : ℝ) + 1) ^ 2 := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_right hfrac (sq_nonneg _)

end Erdos335.IntermediateScale
