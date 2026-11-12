import Erdos335.LoebHull

/-!
# Internal inner approximation

Taking complements in internal outer approximation yields internal subsets
of a measurable set with arbitrarily small measure loss.
-/

set_option autoImplicit false

open Filter Set Topology MeasureTheory
open scoped ENNReal symmDiff

namespace Erdos335.Loeb

theorem exists_internal_inner_approximation
    {X : ℕ → Type*} [∀ n, Finite (X n)] [∀ n, Nonempty (X n)]
    (U : Ultrafilter ℕ) (hU : (U : Filter ℕ) ≤ atTop)
    (S : Set ((U : Filter ℕ).Product X)) (hS : MeasurableSet[loebMeasurableSpace U] S)
    (ε : ℝ≥0∞) (hε : 0 < ε) :
    ∃ A ∈ internalSets U, A ⊆ S ∧ loebMeasure U hU (S ∆ A) < ε := by
  obtain ⟨B, hBi, hSB, herror⟩ := exists_internal_approximation U hU Sᶜ hS.compl ε hε
  refine ⟨Bᶜ, (isSetAlgebra_internalSets U).compl_mem hBi, ?_, ?_⟩
  · simpa only [compl_compl] using compl_subset_compl.mpr hSB
  · have heq : S ∆ Bᶜ = Sᶜ ∆ B := by
      ext x
      simp only [Set.symmDiff_def, Set.mem_union, Set.mem_sdiff, Set.mem_compl_iff]
      tauto
    rw [heq]
    exact herror

end Erdos335.Loeb
