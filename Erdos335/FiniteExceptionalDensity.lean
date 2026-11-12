import Erdos335.FrequencyBandDensity
import Mathlib.Topology.Algebra.Monoid

/-!
# Finite unions of exceptional sets of vanishing density
-/

set_option autoImplicit false

open Filter Topology Finset
open scoped BigOperators

namespace Erdos335.IntermediateScale

theorem finite_union_density_tendsto_zero {I : Type*} [Fintype I]
    (N : ℕ → ℕ) (S : I → ℕ → Finset ℕ)
    (hS : ∀ i, Tendsto (fun s => ((S i s).card : ℝ) / N s) atTop (𝓝 0)) :
    Tendsto (fun s => (((univ : Finset I).biUnion (fun i => S i s)).card : ℝ) / N s)
      atTop (𝓝 0) := by
  classical
  have hsum : Tendsto (fun s => ∑ i : I, ((S i s).card : ℝ) / N s) atTop (𝓝 0) := by
    simpa only [sum_const_zero] using tendsto_finsetSum (univ : Finset I) (fun i hi => hS i)
  apply squeeze_zero (fun s => by positivity) ?_ hsum
  intro s
  have hcard : (((univ : Finset I).biUnion (fun i => S i s)).card : ℝ) ≤
      ∑ i : I, (S i s).card := by exact_mod_cast (card_biUnion_le (s := univ) (t := fun i => S i s))
  simpa only [Nat.cast_sum, sum_div] using
    div_le_div_of_nonneg_right hcard (Nat.cast_nonneg (N s) : (0 : ℝ) ≤ N s)

end Erdos335.IntermediateScale
