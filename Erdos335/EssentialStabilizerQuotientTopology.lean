import Erdos335.CompactEssentialPeriods
import Mathlib.Topology.Algebra.Group.Quotient
import Mathlib.Topology.MetricSpace.Polish
import Mathlib.Topology.Metrizable.Urysohn

/-!
# Topology of the essential-stabilizer quotient
-/

set_option autoImplicit false

open Set MeasureTheory

namespace Erdos335.Loeb

theorem essential_stabilizer_quotient_polish
    {K : Type*} [AddCommGroup K] [TopologicalSpace K] [IsTopologicalAddGroup K]
    [CompactSpace K] [T2Space K] [SecondCountableTopology K]
    [MeasurableSpace K] [BorelSpace K] [MeasurableAdd₂ K]
    (μ : Measure K) [IsFiniteMeasure μ] [μ.InnerRegularCompactLTTop] [μ.IsAddLeftInvariant]
    (S : Set K) (hS : MeasurableSet S) :
    PolishSpace (K ⧸ AddAction.aestabilizer K μ S) := by
  have : IsClosed (AddAction.aestabilizer K μ S : Set K) := isClosed_aestabilizer μ S hS
  have : T2Space (K ⧸ AddAction.aestabilizer K μ S) := inferInstance
  letI : MetricSpace (K ⧸ AddAction.aestabilizer K μ S) :=
    TopologicalSpace.metrizableSpaceMetric (K ⧸ AddAction.aestabilizer K μ S)
  infer_instance

end Erdos335.Loeb
