import Erdos335

set_option autoImplicit false

open Filter Topology
open scoped Pointwise

namespace Erdos335.Challenge

attribute [local instance] Classical.propDecidable

/-- A direct statement using positive prefix counts and explicit integer sums. -/
noncomputable def OriginalPair (A B : Set ℕ) : Prop := by
  classical
  exact (∀ n ∈ A, 0 < n) ∧ (∀ n ∈ B, 0 < n) ∧
    ∃ a b : ℝ, 0 < a ∧ 0 < b ∧
      Tendsto (fun N : ℕ =>
        (((Finset.Icc 1 N).filter (fun n => n ∈ A)).card : ℝ) / N) atTop (𝓝 a) ∧
      Tendsto (fun N : ℕ =>
        (((Finset.Icc 1 N).filter (fun n => n ∈ B)).card : ℝ) / N) atTop (𝓝 b) ∧
      Tendsto (fun N : ℕ =>
        (((Finset.Icc 1 N).filter (fun n => ∃ x ∈ A, ∃ y ∈ B, x + y = n)).card : ℝ) /
          N) atTop (𝓝 (a + b))

theorem original_pair_iff (A B : Set ℕ) :
    IsErdos335Pair A B ↔ OriginalPair A B := by
  rfl

theorem density_uses_positive_prefixes (A : Set ℕ) (a : ℝ) :
    HasDensity A a ↔ Tendsto
      (fun N : ℕ => (((Finset.Icc 1 N).filter (fun n => n ∈ A)).card : ℝ) / N)
        atTop (𝓝 a) := by
  classical
  rfl

end Erdos335.Challenge

#check @Erdos335.Challenge.original_pair_iff
#print axioms Erdos335.Challenge.original_pair_iff
#check @Erdos335.Challenge.density_uses_positive_prefixes
#print axioms Erdos335.Challenge.density_uses_positive_prefixes

-- Closed stronger periodic-summand refinement.
example : Erdos335.Proposed.PeriodicRefinedSolution :=
  Erdos335.Proposed.full_periodic_classification
