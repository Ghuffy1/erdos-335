import Erdos335.RegularClassification

/-!
# The remaining full-proof obligation after the regular-input case

The argument supplied to the theorem below is an unproved remaining case.
This module supplies no inhabitant of PositiveGapNecessity or FullSolution.
-/

set_option autoImplicit false

open Filter Set Topology
open scoped Pointwise

namespace Erdos335.Proposed

def PositiveGapNecessity : Prop :=
  ∀ (A B : Set ℕ) (a b δA δB : ℝ), A ⊆ Set.Ioi 0 → B ⊆ Set.Ioi 0 →
    0 < a → 0 < b → HasDensity A a → HasDensity B b →
    HasDensity (A + B) (a + b) → a + b < gamma A B → 0 < δA → 0 < δB →
    (∀ h : ℕ+, a + δA ≤ ((residues (h : ℕ) A).card : ℝ) / (h : ℕ)) →
    (∀ h : ℕ+, b + δB ≤ ((residues (h : ℕ) B).card : ℝ) / (h : ℕ)) →
      Classified A B (a + b)

theorem fullSolution_of_positive_gap_necessity (hpositive : PositiveGapNecessity) : FullSolution := by
  intro A B a b hA hB ha hb hdA hdB
  constructor
  · intro hdC
    rcases eq_or_lt_of_le (density_sum_le_gamma hA hB hdC) with heq | hgap
    · exact Or.inl heq.symm
    by_cases hregularA : ∀ ε : ℝ, 0 < ε → ∃ k : ℕ+,
        ((residues (k : ℕ) A).card : ℝ) / (k : ℕ) ≤ a + ε
    · exact (classification_iff_of_regular_capacity A B a b hA hB ha hb hdA hdB hregularA).mp hdC
    by_cases hregularB : ∀ ε : ℝ, 0 < ε → ∃ k : ℕ+,
        ((residues (k : ℕ) B).card : ℝ) / (k : ℕ) ≤ b + ε
    · have hgamma : gamma B A = gamma A B := by
        unfold gamma modularCapacity
        congr 1
        funext h
        rw [add_comm]
      have hC : HasDensity (B + A) (b + a) := by simpa only [add_comm] using hdC
      have hgap' : b + a < gamma B A := by simpa only [hgamma, add_comm b a] using hgap
      rcases regular_summand_strict_classification B A b a hB hA hb ha hdB hdA hC hgap' hregularB with hs | hm
      · exact Or.inr ⟨hgap, Or.inr (Or.inl hs.swap)⟩
      · exact Or.inr ⟨hgap, Or.inr (Or.inr (by simpa only [add_comm b a] using hm.swap))⟩
    · push_neg at hregularA hregularB
      obtain ⟨δA, hδA, hcapA⟩ := hregularA
      obtain ⟨δB, hδB, hcapB⟩ := hregularB
      exact hpositive A B a b δA δB hA hB ha hb hdA hdB hdC hgap hδA hδB
        (fun h => (hcapA h).le) (fun h => (hcapB h).le)
  · intro hc
    exact hc.hasDensity hA hB hdA hdB

end Erdos335.Proposed
