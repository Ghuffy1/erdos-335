import Erdos335.PeriodicRefinementLowNecessity

/-!
# Full classification and original positive-interval count formulation

Private proof development. Verification status is recorded separately.
The declarations combine the positive-gap and Low-branch results.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Filter Set Topology
open scoped Pointwise

noncomputable section

namespace Erdos335.Proposed

theorem full_periodic_classification : PeriodicRefinedSolution :=
  periodicRefinedSolution_of_low_periodic_summand low_periodic_summand_necessity

attribute [local instance] Classical.propDecidable

theorem full_periodic_classification_original_positive_counts
    (A B : Set ℕ) (a b : ℝ)
    (hApos : A ⊆ Set.Ioi 0) (hBpos : B ⊆ Set.Ioi 0) (ha : 0 < a) (hb : 0 < b)
    (hA : Tendsto (fun N : ℕ =>
      ((((Finset.Icc 1 N).filter (fun n => n ∈ A)).card : ℝ) / N)) atTop (𝓝 a))
    (hB : Tendsto (fun N : ℕ =>
      ((((Finset.Icc 1 N).filter (fun n => n ∈ B)).card : ℝ) / N)) atTop (𝓝 b)) :
    (Tendsto (fun N : ℕ =>
      ((((Finset.Icc 1 N).filter (fun n => n ∈ A + B)).card : ℝ) / N)) atTop (𝓝 (a + b))) ↔
      (gamma A B = a + b ∨ (a + b < gamma A B ∧
        (BohrBranch A B ∨ TwoTemplateBranch A B ∨ SparseSectionBranch A B))) := by
  have hdA : HasDensity A a := by simpa only [HasDensity, count] using hA
  have hdB : HasDensity B b := by simpa only [HasDensity, count] using hB
  simpa only [HasDensity, count, PeriodicRefinedClassified] using
    full_periodic_classification A B a b hApos hBpos ha hb hdA hdB

end Erdos335.Proposed

end
