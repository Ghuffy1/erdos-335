import Erdos335.CompactOpenIndex
import Erdos335.LoebSubgroupIndex
import Mathlib.MeasureTheory.Group.Measure

/-!
# Small open subgroups or an open connected subgroup

The Haar probability of an open subgroup is the reciprocal of its
finite index. Unbounded indices therefore give arbitrarily small
positive open subgroups. Bounded indices give an open connected subgroup.
-/

set_option autoImplicit false

open Filter Set Topology MeasureTheory
open scoped ENNReal

noncomputable section

namespace Erdos335.Loeb

variable {G : Type*} [AddGroup G] [TopologicalSpace G] [IsTopologicalAddGroup G] [CompactSpace G]
  [MeasurableSpace G] [BorelSpace G]

theorem haar_measure_open_addSubgroup
    (μ : Measure G) [IsProbabilityMeasure μ] [μ.IsAddLeftInvariant] (H : OpenAddSubgroup G) :
    μ (H : Set G) = 1 / (H.toAddSubgroup.index : ℝ≥0∞) := by
  have : H.toAddSubgroup.FiniteIndex := AddSubgroup.finiteIndex_of_finite_quotient
  have hzero : (H.toAddSubgroup.index : ℝ≥0∞) ≠ 0 := by
    exact_mod_cast (AddSubgroup.FiniteIndex.index_ne_zero (H := H.toAddSubgroup))
  have hfinite : (H.toAddSubgroup.index : ℝ≥0∞) ≠ ∞ := by finiteness
  have hid := H.toAddSubgroup.index_mul_measure H.isOpen.measurableSet μ
  rw [measure_univ] at hid
  change (H.toAddSubgroup.index : ℝ≥0∞) * μ (H : Set G) = 1 at hid
  calc
    μ (H : Set G) = (H.toAddSubgroup.index : ℝ≥0∞)⁻¹ *
        ((H.toAddSubgroup.index : ℝ≥0∞) * μ (H : Set G)) := by
      rw [← mul_assoc, ENNReal.inv_mul_cancel hzero hfinite, one_mul]
    _ = 1 / (H.toAddSubgroup.index : ℝ≥0∞) := by rw [hid, mul_one, one_div]

theorem compact_open_subgroups_small_or_connected
    (μ : Measure G) [IsProbabilityMeasure μ] [μ.IsAddLeftInvariant] :
    (∀ ε : ℝ≥0∞, 0 < ε → ∃ H : OpenAddSubgroup G,
      0 < μ (H : Set G) ∧ μ (H : Set G) < ε) ∨
      ∃ H : OpenAddSubgroup G, ConnectedSpace H := by
  rcases open_addSubgroup_indices_unbounded_or_connected G with hsmall | hconnected
  · left
    intro ε hε
    obtain ⟨D, hD⟩ := exists_nat_reciprocal_lt ε hε
    obtain ⟨H, hH⟩ := hsmall D
    refine ⟨H, ?_, ?_⟩
    · rw [haar_measure_open_addSubgroup μ H, one_div]
      exact ENNReal.inv_pos.mpr (by finiteness)
    · rw [haar_measure_open_addSubgroup μ H]
      apply lt_of_le_of_lt ?_ hD
      simpa only [one_div] using ENNReal.inv_le_inv.mpr
        (show ((D + 1 : ℕ) : ℝ≥0∞) ≤ (H.toAddSubgroup.index : ℝ≥0∞) by
          exact_mod_cast (Nat.succ_le_iff.mpr hH))
  · exact Or.inr hconnected

end Erdos335.Loeb

end
