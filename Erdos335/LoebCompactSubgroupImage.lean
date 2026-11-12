import Erdos335.LoebCompactInternalImage
import Erdos335.LoebPositiveSubgroups
import Erdos335.LoebSubgroupIndex
import Mathlib.Topology.Algebra.Group.ClosedSubgroup

/-!
# Compact open images of positive Loeb subgroups

A positive measurable subgroup of a cyclic Loeb group is internal and
has finite index. Its image in a compact ultralimit factor is compact,
and its image in the range of that factor is open.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Filter Set Topology MeasureTheory

noncomputable section

namespace Erdos335.Loeb

local instance compactSubgroupImageLoebSpace (U : Ultrafilter ℕ) (q : ℕ → ℕ+) :
    MeasurableSpace ((U : Filter ℕ).Product (fun n => ZMod (q n : ℕ))) := loebMeasurableSpace U

variable {E : Type*} [AddCommGroup E] [MetricSpace E] [CompactSpace E] [IsTopologicalAddGroup E]

theorem isCompact_image_positive_loeb_subgroup
    (U : Ultrafilter ℕ) (hU : (U : Filter ℕ) ≤ atTop) (q : ℕ → ℕ+)
    (H : AddSubgroup ((U : Filter ℕ).Product (fun n => ZMod (q n : ℕ))))
    (hHm : MeasurableSet (H : Set ((U : Filter ℕ).Product (fun n => ZMod (q n : ℕ)))))
    (hHpos : 0 < loebMeasure (X := fun n => ZMod (q n : ℕ)) U hU (H : Set _))
    (f : ∀ n, ZMod (q n : ℕ) →+ E) :
    IsCompact (ultralimitAddHom U f '' (H : Set ((U : Filter ℕ).Product (fun n => ZMod (q n : ℕ))))) := by
  obtain ⟨h, p, _, hker, _⟩ := positive_measurable_subgroup_is_natural_finite_kernel U hU q H hHm hHpos
  rw [← hker, finiteQuotient_ker]
  exact isCompact_image_internalAddSubgroup U hU (fun n => (p n).ker) f

theorem isCompact_image_positive_loeb_subgroup_rangeRestrict
    (U : Ultrafilter ℕ) (hU : (U : Filter ℕ) ≤ atTop) (q : ℕ → ℕ+)
    (H : AddSubgroup ((U : Filter ℕ).Product (fun n => ZMod (q n : ℕ))))
    (hHm : MeasurableSet (H : Set ((U : Filter ℕ).Product (fun n => ZMod (q n : ℕ)))))
    (hHpos : 0 < loebMeasure (X := fun n => ZMod (q n : ℕ)) U hU (H : Set _))
    (f : ∀ n, ZMod (q n : ℕ) →+ E) :
    IsCompact ((ultralimitAddHom U f).rangeRestrict ''
      (H : Set ((U : Filter ℕ).Product (fun n => ZMod (q n : ℕ))))) := by
  let φ := ultralimitAddHom U f
  let π := φ.rangeRestrict
  have : CompactSpace φ.range := isCompact_iff_compactSpace.mp (isCompact_range_ultralimitAddHom U hU f)
  have hc := isCompact_image_positive_loeb_subgroup U hU q H hHm hHpos f
  have heq : π '' (H : Set ((U : Filter ℕ).Product (fun n => ZMod (q n : ℕ)))) =
      Subtype.val ⁻¹' (φ '' (H : Set ((U : Filter ℕ).Product (fun n => ZMod (q n : ℕ))))) := by
    ext y
    constructor
    · rintro ⟨x, hx, hxy⟩
      exact ⟨x, hx, congrArg Subtype.val hxy⟩
    · rintro ⟨x, hx, hxy⟩
      exact ⟨x, hx, Subtype.ext hxy⟩
  rw [heq]
  exact (hc.isClosed.preimage continuous_subtype_val).isCompact

theorem isOpen_map_positive_loeb_subgroup_rangeRestrict
    (U : Ultrafilter ℕ) (hU : (U : Filter ℕ) ≤ atTop) (q : ℕ → ℕ+)
    (H : AddSubgroup ((U : Filter ℕ).Product (fun n => ZMod (q n : ℕ))))
    (hHm : MeasurableSet (H : Set ((U : Filter ℕ).Product (fun n => ZMod (q n : ℕ)))))
    (hHpos : 0 < loebMeasure (X := fun n => ZMod (q n : ℕ)) U hU (H : Set _))
    (f : ∀ n, ZMod (q n : ℕ) →+ E) :
    IsOpen (H.map (ultralimitAddHom U f).rangeRestrict : Set (ultralimitAddHom U f).range) := by
  let φ := ultralimitAddHom U f
  let π := φ.rangeRestrict
  have : H.FiniteIndex := ⟨(positive_measurable_subgroup_index U hU q H hHm hHpos).1.ne'⟩
  have : (H.map π).FiniteIndex := AddSubgroup.FiniteIndex.map_of_surjective H φ.rangeRestrict_surjective
  have hc : IsCompact (H.map π : Set φ.range) :=
    isCompact_image_positive_loeb_subgroup_rangeRestrict U hU q H hHm hHpos f
  exact (H.map π).isOpen_of_isClosed_of_finiteIndex hc.isClosed

end Erdos335.Loeb

end
