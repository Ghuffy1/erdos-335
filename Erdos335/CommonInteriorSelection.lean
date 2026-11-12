import Erdos335.InteriorSmallAverage
import Mathlib.Topology.Algebra.Order.Field
import Mathlib.Algebra.BigOperators.Field

/-!
# One interior start for finitely many vanishing error averages
-/

set_option autoImplicit false

open Filter Topology Finset
open scoped BigOperators

namespace Erdos335.IntermediateScale

theorem exists_common_small_interior_positions {I : Type*} [Fintype I]
    (e : I → ℕ → ℕ → ℝ) (he : ∀ i s n, 0 ≤ e i s n)
    (N T : ℕ → ℕ) (hN : ∀ s, 0 < N s)
    (hT : Tendsto (fun s => (T s : ℝ) / N s) atTop (𝓝 0))
    (hmean : ∀ i, Tendsto (fun s => (∑ n ∈ range (N s), e i s n) / N s) atTop (𝓝 0)) :
    ∃ n : ℕ → ℕ, (∀ s, n s < N s) ∧
      (∀ᶠ s in atTop, n s + T s ≤ N s) ∧
      ∀ i, Tendsto (fun s => e i s (n s)) atTop (𝓝 0) := by
  let f : ℕ → ℕ → ℝ := fun s n => ∑ i, e i s n
  have hf : ∀ s n, 0 ≤ f s n := fun s n => sum_nonneg (fun i hi => he i s n)
  have hfm : Tendsto (fun s => (∑ n ∈ range (N s), f s n) / N s) atTop (𝓝 0) := by
    have ht := tendsto_finset_sum (univ : Finset I) (fun i hi => hmean i)
    have heq (s : ℕ) : (∑ n ∈ range (N s), f s n) / N s =
        ∑ i, (∑ n ∈ range (N s), e i s n) / N s := by
      dsimp only [f]
      rw [sum_comm]
      simp only [sum_div]
    simpa only [heq, sum_const_zero] using ht
  obtain ⟨n, hn, hinside, hsmall⟩ := exists_small_interior_positions f hf N T hN hT hfm
  refine ⟨n, hn, hinside, ?_⟩
  intro i
  apply squeeze_zero (fun s => he i s (n s)) (fun s => ?_) hsmall
  exact single_le_sum (fun j hj => he j s (n s)) (mem_univ i)

end Erdos335.IntermediateScale
