import Erdos335.FullPositiveGapAssembly
import Erdos335.LowGapNecessity

/-!
# Full classification and original positive-interval count formulation

Private proof development. Verification status is recorded separately.
The declarations combine the positive-gap and Low-branch results.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000

open Filter Set Topology
open scoped Pointwise

noncomputable section

namespace Erdos335.Proposed

theorem low_positive_gap_necessity : LowPositiveGapNecessity := by
  intro A B a b δA δB _ _ ha hb hdA hdB hdC hgap hδA hδB hcapA hcapB hlow
  exact low_gap_classified_of_either A B a b δA δB ha hb hδA hδB
    hdA hdB hdC hgap hlow hcapA hcapB

theorem positive_gap_necessity : PositiveGapNecessity :=
  positiveGapNecessity_of_low_positive_gap_necessity low_positive_gap_necessity

theorem full_classification : FullSolution :=
  fullSolution_of_positive_gap_necessity positive_gap_necessity

attribute [local instance] Classical.propDecidable

/-- Formulation using literal counts in the original intervals [1,N]. -/
theorem full_classification_original_positive_counts
    (A B : Set ℕ) (a b : ℝ)
    (hApos : A ⊆ Set.Ioi 0) (hBpos : B ⊆ Set.Ioi 0)
    (ha : 0 < a) (hb : 0 < b)
    (hA : Tendsto (fun N : ℕ =>
      ((((Finset.Icc 1 N).filter (fun n => n ∈ A)).card : ℝ) / N)) atTop (𝓝 a))
    (hB : Tendsto (fun N : ℕ =>
      ((((Finset.Icc 1 N).filter (fun n => n ∈ B)).card : ℝ) / N)) atTop (𝓝 b)) :
    (Tendsto (fun N : ℕ =>
      ((((Finset.Icc 1 N).filter (fun n => n ∈ A + B)).card : ℝ) / N))
        atTop (𝓝 (a + b))) ↔
      (gamma A B = a + b ∨ (a + b < gamma A B ∧
        (BohrBranch A B ∨ SingletonBranch A B ∨ MaskBranch A B (a + b)))) := by
  have hdA : HasDensity A a := by
    simpa only [HasDensity, count] using hA
  have hdB : HasDensity B b := by
    simpa only [HasDensity, count] using hB
  simpa only [HasDensity, count, Classified] using
    (full_classification A B a b hApos hBpos ha hb hdA hdB)

end Erdos335.Proposed

end
