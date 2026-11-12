import Erdos335.PeriodicCoreMaskBranch
import Erdos335.PeriodicSummandFrame
import Erdos335.NullFrameClassification

/-!
# The complete necessity reduction for an ordinary periodic summand
-/

set_option autoImplicit false

open Filter Set Topology
open scoped Pointwise

namespace Erdos335.Proposed

theorem periodic_summand_classified
    (A B : Set ℕ) (a b : ℝ) (hA : A ⊆ Set.Ioi 0) (hB : B ⊆ Set.Ioi 0)
    (ha : 0 < a) (hb : 0 < b) (hdA : HasDensity A a) (hdB : HasDensity B b)
    (hdC : HasDensity (A + B) (a + b)) (hgap : a + b < gamma A B)
    (m : ℕ+) (P : Finset (ZMod (m : ℕ))) (hAP : DensityEquivalent A (periodicSet P)) :
    SingletonBranch A B ∨ MaskBranch A B (a + b) := by
  let U := residues (m : ℕ) B + P
  have hholes : Negligible (periodicSet U \ (A + B)) := by
    apply negligible_periodic_diff_of_singletons
    intro w hw
    have hh := missing_left_baseline_singleton (A := B) (B := A) hAP hw
    simpa only [add_comm B A] using hh
  have hbound : (U.card : ℝ) / (m : ℕ) ≤ a + b := by
    have hh := (hdC.sdiff_of_negligible_reverse (hasDensity_periodicSet U) hholes).nonneg
    linarith
  by_cases hstrict : (U.card : ℝ) / (m : ℕ) < a + b
  · have hstrict' : ((P + residues (m : ℕ) B).card : ℝ) / (m : ℕ) < a + b := by
      simpa only [U, add_comm P (residues (m : ℕ) B)] using hstrict
    obtain ⟨f, x, _, hzero, hactive, hxpos, hxlt⟩ := periodic_summand_strict_finite_frame A B a b
      hA hB ha hb hdA hdB hdC hgap m P hAP hstrict'
    exact f.null_left_classified hA hB a b x hdA hdB hdC hzero hactive hxpos hxlt
  · exact Or.inr (periodic_summand_saturated_maskBranch A B a b hA hB ha hb hdA hdB hdC hgap
      m P hAP (le_antisymm hbound (not_lt.mp hstrict)))

end Erdos335.Proposed
