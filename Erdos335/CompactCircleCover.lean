import Erdos335.CompactCircleEquiv
import Mathlib.Topology.Covering.Quotient
import Mathlib.Topology.Homotopy.Lifting

/-!
# Circle-valued homomorphisms with finite kernel are covering maps
-/

set_option autoImplicit false

open Set Topology

namespace Erdos335.Loeb

theorem isCoveringMap_of_finite_circle_kernel
    {G : Type*} [AddCommGroup G] [TopologicalSpace G] [IsTopologicalAddGroup G]
    [CompactSpace G] [ConnectedSpace G] [T2Space G]
    (φ : G →+ AddCircle (1 : ℝ)) (hφ : Continuous φ) (hne : φ ≠ 0)
    [Finite φ.ker] : IsCoveringMap φ := by
  have : Fact (0 < (1 : ℝ)) := ⟨zero_lt_one⟩
  have hsurj := continuous_circle_hom_surjective_of_ne_zero φ hφ hne
  have hquot : IsQuotientMap φ := IsQuotientMap.of_surjective_continuous hsurj hφ
  have hdisc : IsDiscrete (φ.ker : Set G) := (Set.toFinite _).isDiscrete
  exact (hquot.isAddQuotientCoveringMap_of_isDiscrete_ker_addMonoidHom hdisc).isCoveringMap

end Erdos335.Loeb
