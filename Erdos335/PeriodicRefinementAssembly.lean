import Erdos335.PeriodicRefinementSpecification
import Erdos335.FullPositiveGapAssembly

/-!
# Assembly of the stronger classification from the Low-branch theorem

The parameter is the explicit local-to-global obligation.  The final closed
theorem is obtained by supplying its independently constructed inhabitant.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Filter Set Topology
open scoped Pointwise

noncomputable section

namespace Erdos335.Proposed

def HasPeriodicSummand (A B : Set ℕ) : Prop :=
  ∃ (m : ℕ+) (P : Finset (ZMod (m : ℕ))),
    DensityEquivalent A (periodicSet P) ∨ DensityEquivalent B (periodicSet P)

theorem HasPeriodicSummand.swap {A B : Set ℕ} (h : HasPeriodicSummand A B) :
    HasPeriodicSummand B A := by
  obtain ⟨m, P, hp⟩ := h
  exact ⟨m, P, hp.symm⟩

def LowPeriodicSummandNecessity : Prop :=
  ∀ (A B : Set ℕ) (a b δA δB : ℝ), A ⊆ Set.Ioi 0 → B ⊆ Set.Ioi 0 →
    0 < a → 0 < b → HasDensity A a → HasDensity B b →
    HasDensity (A + B) (a + b) → a + b < gamma A B → 0 < δA → 0 < δB →
    (∀ h : ℕ+, a + δA ≤ ((residues (h : ℕ) A).card : ℝ) / (h : ℕ)) →
    (∀ h : ℕ+, b + δB ≤ ((residues (h : ℕ) B).card : ℝ) / (h : ℕ)) →
    LowResidueCapacityGap A a (gamma A B - (a + b)) → HasPeriodicSummand A B

theorem refined_classified_of_periodic_summand
    (A B : Set ℕ) (a b : ℝ) (hA : A ⊆ Set.Ioi 0) (hB : B ⊆ Set.Ioi 0)
    (ha : 0 < a) (hb : 0 < b) (hdA : HasDensity A a) (hdB : HasDensity B b)
    (hdC : HasDensity (A + B) (a + b)) (hgap : a + b < gamma A B)
    (hperiodic : HasPeriodicSummand A B) : PeriodicRefinedClassified A B (a + b) := by
  have hterminal := (periodic_summand_refinement_iff_of_either A B a b hA hB ha hb
    hdA hdB hgap hperiodic).mp hdC
  exact Or.inr ⟨hgap, Or.inr hterminal⟩

theorem refined_classified_of_regular_capacity
    (A B : Set ℕ) (a b : ℝ) (hA : A ⊆ Set.Ioi 0) (hB : B ⊆ Set.Ioi 0)
    (ha : 0 < a) (hb : 0 < b) (hdA : HasDensity A a) (hdB : HasDensity B b)
    (hdC : HasDensity (A + B) (a + b)) (hgap : a + b < gamma A B)
    (hregular : ∀ ε : ℝ, 0 < ε → ∃ k : ℕ+,
      ((residues (k : ℕ) A).card : ℝ) / (k : ℕ) ≤ a + ε) :
    PeriodicRefinedClassified A B (a + b) := by
  have hperiodic := exists_periodic_summand_of_regular_capacity A B a b hA hB ha hb
    hdA hdB hdC hgap hregular
  apply refined_classified_of_periodic_summand A B a b hA hB ha hb hdA hdB hdC hgap
  rcases hperiodic with ⟨m, P, hP⟩ | ⟨m, P, hP⟩
  · exact ⟨m, P, Or.inl hP⟩
  · exact ⟨m, P, Or.inr hP⟩

theorem periodicRefinedSolution_of_low_periodic_summand
    (hlow : LowPeriodicSummandNecessity) : PeriodicRefinedSolution := by
  intro A B a b hA hB ha hb hdA hdB
  constructor
  · intro hdC
    rcases eq_or_lt_of_le (density_sum_le_gamma hA hB hdC) with heq | hgap
    · exact Or.inl heq.symm
    by_cases hregularA : ∀ ε : ℝ, 0 < ε → ∃ k : ℕ+,
        ((residues (k : ℕ) A).card : ℝ) / (k : ℕ) ≤ a + ε
    · exact refined_classified_of_regular_capacity A B a b hA hB ha hb hdA hdB hdC hgap hregularA
    have hgamma : gamma B A = gamma A B := by
      unfold gamma modularCapacity
      simp only [add_comm]
    have hCswap : HasDensity (B + A) (b + a) := by simpa only [add_comm] using hdC
    have hgapSwap : b + a < gamma B A := by simpa only [hgamma, add_comm b a] using hgap
    by_cases hregularB : ∀ ε : ℝ, 0 < ε → ∃ k : ℕ+,
        ((residues (k : ℕ) B).card : ℝ) / (k : ℕ) ≤ b + ε
    · have hperiodic := exists_periodic_summand_of_regular_capacity B A b a hB hA hb ha
        hdB hdA hCswap hgapSwap hregularB
      apply refined_classified_of_periodic_summand A B a b hA hB ha hb hdA hdB hdC hgap
      rcases hperiodic with ⟨m, P, hP⟩ | ⟨m, P, hP⟩
      · exact ⟨m, P, Or.inr hP⟩
      · exact ⟨m, P, Or.inl hP⟩
    push_neg at hregularA hregularB
    obtain ⟨δA, hδA, hcapA⟩ := hregularA
    obtain ⟨δB, hδB, hcapB⟩ := hregularB
    by_cases hlowA : LowResidueCapacityGap A a (gamma A B - (a + b))
    · exact refined_classified_of_periodic_summand A B a b hA hB ha hb hdA hdB hdC hgap
        (hlow A B a b δA δB hA hB ha hb hdA hdB hdC hgap hδA hδB
          (fun k => (hcapA k).le) (fun k => (hcapB k).le) hlowA)
    by_cases hlowB : LowResidueCapacityGap B b (gamma A B - (a + b))
    · have hlowSwap : LowResidueCapacityGap B b (gamma B A - (b + a)) := by
        simpa only [hgamma, add_comm b a] using hlowB
      have hp := hlow B A b a δB δA hB hA hb ha hdB hdA hCswap hgapSwap hδB hδA
        (fun k => (hcapB k).le) (fun k => (hcapA k).le) hlowSwap
      exact refined_classified_of_periodic_summand A B a b hA hB ha hb hdA hdB hdC hgap hp.swap
    obtain ⟨ηA, hηA, hcapA'⟩ :=
      not_low_residue_capacity_gap A a (gamma A B - (a + b)) hlowA
    obtain ⟨ηB, hηB, hcapB'⟩ :=
      not_low_residue_capacity_gap B b (gamma A B - (a + b)) hlowB
    let U : Ultrafilter ℕ := Ultrafilter.of atTop
    have hU : (U : Filter ℕ) ≤ atTop := Ultrafilter.of_le atTop
    have hbohr := high_gap_bohr_branch U hU A B hA hB a b ηA ηB ha hb hdA hdB hdC hgap
      (by linarith) (by linarith) hcapA' hcapB'
    exact Or.inr ⟨hgap, Or.inl hbohr⟩
  · intro hclassified
    exact hclassified.hasDensity hA hB hdA hdB

end Erdos335.Proposed

end
