import Mathlib.Topology.Instances.AddCircle.DenseSubgroup
import Mathlib.Topology.Separation.Connected
import Mathlib.Data.ZMod.QuotientGroup
import Mathlib.Analysis.Normed.Group.AddCircle

/-!
# Nontrivial circle homomorphisms from connected compact groups
-/

set_option autoImplicit false

open Set

namespace Erdos335.Loeb

theorem continuous_circle_hom_surjective_of_ne_zero
    {G : Type*} [AddGroup G] [TopologicalSpace G] [CompactSpace G] [ConnectedSpace G]
    {p : ℝ} [Fact (0 < p)] (φ : G →+ AddCircle p) (hφ : Continuous φ) (hne : φ ≠ 0) :
    Function.Surjective φ := by
  classical
  have hdense : Dense (φ.range : Set (AddCircle p)) := by
    apply AddCircle.dense_addSubgroup_iff_ne_zmultiples.mpr
    intro a ha heq
    have : Finite φ.range := by
      rw [heq]
      exact finite_zmultiples.mpr (addOrderOf_ne_zero_iff.mp ha)
    have : PreconnectedSpace φ.range :=
      Subtype.preconnectedSpace (isPreconnected_range hφ)
    have : DiscreteTopology φ.range := inferInstance
    have : Subsingleton φ.range := PreconnectedSpace.trivial_of_discrete
    apply hne
    ext x
    exact congrArg Subtype.val (Subsingleton.elim
      (⟨φ x, mem_range_self x⟩ : φ.range) ⟨0, φ.range.zero_mem⟩)
  change Dense (Set.range φ) at hdense
  have hclosed : IsClosed (Set.range φ) := (isCompact_range hφ).isClosed
  intro y
  have hy : y ∈ Set.range φ := by
    rw [← hclosed.closure_eq, hdense.closure_eq]
    trivial
  exact hy

end Erdos335.Loeb
