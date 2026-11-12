import Erdos335.PositiveGapReduction
import Erdos335.HighGapNecessity

/-!
# Positive-gap assembly from the Low branch and its High complement

Private proof development. Verification status is recorded separately.
LowPositiveGapNecessity states the Low-branch interface. The implications
here combine that interface with high_gap_bohr_branch.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000

open Filter Set Topology
open scoped Pointwise

noncomputable section

namespace Erdos335.Proposed

def LowResidueCapacityGap (A : Set ℕ) (a Δ : ℝ) : Prop :=
  ∀ η : ℝ, Δ < η → ∃ k : ℕ+,
    ((residues (k : ℕ) A).card : ℝ) / (k : ℕ) < a + η

/-- The classification interface when either input is Low. -/
def LowPositiveGapNecessity : Prop :=
  ∀ (A B : Set ℕ) (a b δA δB : ℝ), A ⊆ Set.Ioi 0 → B ⊆ Set.Ioi 0 →
    0 < a → 0 < b → HasDensity A a → HasDensity B b →
    HasDensity (A + B) (a + b) → a + b < gamma A B → 0 < δA → 0 < δB →
    (∀ h : ℕ+, a + δA ≤ ((residues (h : ℕ) A).card : ℝ) / (h : ℕ)) →
    (∀ h : ℕ+, b + δB ≤ ((residues (h : ℕ) B).card : ℝ) / (h : ℕ)) →
    (LowResidueCapacityGap A a (gamma A B - (a + b)) ∨
      LowResidueCapacityGap B b (gamma A B - (a + b))) →
      Classified A B (a + b)

theorem not_low_residue_capacity_gap
    (A : Set ℕ) (a Δ : ℝ) (hnot : ¬LowResidueCapacityGap A a Δ) :
    ∃ η : ℝ, Δ < η ∧ ∀ h : ℕ+,
      a + η ≤ ((residues (h : ℕ) A).card : ℝ) / (h : ℕ) := by
  unfold LowResidueCapacityGap at hnot
  push_neg at hnot
  exact hnot

theorem positiveGapNecessity_of_low_positive_gap_necessity
    (hlow : LowPositiveGapNecessity) : PositiveGapNecessity := by
  intro A B a b δA δB hA hB ha hb hdA hdB hdC hgap hδA hδB hcapA hcapB
  by_cases hlowA : LowResidueCapacityGap A a (gamma A B - (a + b))
  · exact hlow A B a b δA δB hA hB ha hb hdA hdB hdC hgap hδA hδB
      hcapA hcapB (Or.inl hlowA)
  by_cases hlowB : LowResidueCapacityGap B b (gamma A B - (a + b))
  · exact hlow A B a b δA δB hA hB ha hb hdA hdB hdC hgap hδA hδB
      hcapA hcapB (Or.inr hlowB)
  obtain ⟨ηA, hηA, hcapA'⟩ :=
    not_low_residue_capacity_gap A a (gamma A B - (a + b)) hlowA
  obtain ⟨ηB, hηB, hcapB'⟩ :=
    not_low_residue_capacity_gap B b (gamma A B - (a + b)) hlowB
  have hhighA : gamma A B < a + b + ηA := by linarith
  have hhighB : gamma A B < a + b + ηB := by linarith
  let U : Ultrafilter ℕ := Ultrafilter.of atTop
  have hU : (U : Filter ℕ) ≤ atTop := Ultrafilter.of_le atTop
  have hbohr := high_gap_bohr_branch U hU A B hA hB a b ηA ηB ha hb
    hdA hdB hdC hgap hhighA hhighB hcapA' hcapB'
  exact Or.inr ⟨hgap, Or.inl hbohr⟩

theorem fullSolution_of_low_positive_gap_necessity
    (hlow : LowPositiveGapNecessity) : FullSolution :=
  fullSolution_of_positive_gap_necessity
    (positiveGapNecessity_of_low_positive_gap_necessity hlow)

end Erdos335.Proposed

end
