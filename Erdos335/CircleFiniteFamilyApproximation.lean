import Erdos335.CirclePolynomialApproximation
import Mathlib.Algebra.Order.Archimedean.Real.Basic

/-!
# Uniform finite bounds for a finite family of circle approximations
-/

set_option autoImplicit false

open Finset
open scoped BigOperators Classical

namespace Erdos335.IntermediateScale

theorem finite_family_circle_approximation {I : Type*} [Fintype I]
    (F : I → C(Circle, ℂ)) (ε : ℝ) (hε : 0 < ε) :
    ∃ (K : ℕ) (S : I → Finset ℤ) (w : I → ℤ → ℂ), 0 < K ∧
      (∀ i, (S i).card ≤ K) ∧
      (∀ i n, n ∈ S i → n.natAbs ≤ K ∧ ‖w i n‖ ≤ K) ∧
      ∀ i z, ‖F i z - ∑ n ∈ S i, w i n * (z : ℂ) ^ n‖ < ε := by
  choose S w hw using fun i => exists_circle_polynomial_approximation (F i) ε hε
  let B := fun i => (S i).card + ∑ n ∈ S i, (n.natAbs + ⌈‖w i n‖⌉₊) + 1
  let K := (∑ i : I, B i) + 1
  have hBK (i : I) : B i ≤ K := by
    exact (single_le_sum (fun _ _ => Nat.zero_le _) (mem_univ i)).trans (Nat.le_succ _)
  have hcard (i : I) : (S i).card ≤ B i := by dsimp [B]; omega
  have hterm (i : I) (n : ℤ) (hn : n ∈ S i) : n.natAbs + ⌈‖w i n‖⌉₊ ≤ B i := by
    have ht : n.natAbs + ⌈‖w i n‖⌉₊ ≤ ∑ m ∈ S i, (m.natAbs + ⌈‖w i m‖⌉₊) :=
      single_le_sum (f := fun m => m.natAbs + ⌈‖w i m‖⌉₊) (fun _ _ => Nat.zero_le _) hn
    dsimp [B]
    omega
  refine ⟨K, S, w, by dsimp [K]; omega, fun i => (hcard i).trans (hBK i), ?_, hw⟩
  intro i n hn
  have ht := (hterm i n hn).trans (hBK i)
  refine ⟨by omega, ?_⟩
  have hceil : ⌈‖w i n‖⌉₊ ≤ K := by omega
  exact (Nat.le_ceil ‖w i n‖).trans (by exact_mod_cast hceil)

end Erdos335.IntermediateScale
