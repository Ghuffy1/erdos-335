import Erdos335.CompactStabilizerQuotient
import Erdos335.CompactEssentialPeriods
import Mathlib.Topology.Algebra.Group.Quotient

/-!
# Quotienting by the full almost-everywhere stabilizer
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Filter Set MeasureTheory
open scoped Pointwise

noncomputable section

namespace Erdos335.Loeb

theorem exists_aestabilizer_quotient_representative
    {G : Type*} [AddCommGroup G] [TopologicalSpace G] [IsTopologicalAddGroup G]
    [CompactSpace G] [T2Space G] [MeasurableSpace G] [BorelSpace G] [MeasurableAdd₂ G]
    (μ : Measure G) [IsFiniteMeasure μ] [μ.InnerRegularCompactLTTop] [μ.IsAddLeftInvariant]
    (S : Set G) (hS : MeasurableSet S) (H : AddSubgroup G)
    (hH : H = AddAction.aestabilizer G μ S)
    [MeasurableSpace (G ⧸ H)] [BorelSpace (G ⧸ H)] :
    ∃ T : Set (G ⧸ H), IsSigmaCompact T ∧ MeasurableSet T ∧
      (QuotientAddGroup.mk' H) ⁻¹' T =ᵐ[μ] S ∧
      ∀ t : G ⧸ H, t +ᵥ T =ᵐ[Measure.map (QuotientAddGroup.mk' H) μ] T → t = 0 := by
  have : IsClosed (H : Set G) := by
    rw [hH]
    exact isClosed_aestabilizer μ S hS
  apply exists_aperiodic_quotient_representative μ (QuotientAddGroup.mk' H)
    QuotientAddGroup.continuous_mk (QuotientAddGroup.mk'_surjective H) S hS
  exact (QuotientAddGroup.ker_mk' H).trans hH

end Erdos335.Loeb

end
