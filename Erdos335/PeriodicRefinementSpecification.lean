import Erdos335.PeriodicRefinementTwoTemplatesBranch
import Erdos335.Sufficiency

/-!
# The stronger periodic-summand classification

The exceptional summands remain literal sets in both packing alternatives.
The sparse terminal records its minimum, its exact set gcd, and the full
infinite-union escape test whenever the exceptional set is infinite.
-/

set_option autoImplicit false

open Filter Set Topology
open scoped Pointwise

namespace Erdos335.Proposed

def PeriodicRefinedClassified (A B : Set ℕ) (s : ℝ) : Prop :=
  gamma A B = s ∨
    (s < gamma A B ∧ (BohrBranch A B ∨ TwoTemplateBranch A B ∨ SparseSectionBranch A B))

def PeriodicRefinedSolution : Prop :=
  ∀ (A B : Set ℕ) (a b : ℝ), A ⊆ Set.Ioi 0 → B ⊆ Set.Ioi 0 →
    0 < a → 0 < b → HasDensity A a → HasDensity B b →
      (HasDensity (A + B) (a + b) ↔ PeriodicRefinedClassified A B (a + b))

theorem PeriodicRefinedClassified.hasDensity
    {A B : Set ℕ} {a b : ℝ} (h : PeriodicRefinedClassified A B (a + b))
    (hA : A ⊆ Set.Ioi 0) (hB : B ⊆ Set.Ioi 0)
    (hdA : HasDensity A a) (hdB : HasDensity B b) : HasDensity (A + B) (a + b) := by
  rcases h with hregular | ⟨hgap, hbohr | htemplates | hsparse⟩
  · exact (show Classified A B (a + b) from Or.inl hregular).hasDensity hA hB hdA hdB
  · exact (show Classified A B (a + b) from Or.inr ⟨hgap, Or.inl hbohr⟩).hasDensity hA hB hdA hdB
  · exact htemplates.hasDensity hA hB hdA hdB
  · exact hsparse.hasDensity hA hB hdA hdB

end Erdos335.Proposed
