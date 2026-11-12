import Mathlib.Topology.Algebra.OpenSubgroup
import Mathlib.Topology.Connected.Clopen
import Mathlib.Tactic

/-!
# Connected compact groups and open subgroups
-/

set_option autoImplicit false

open Set Topology

namespace Erdos335.Loeb

theorem connectedSpace_of_no_proper_open_addSubgroup
    {G : Type*} [AddGroup G] [TopologicalSpace G] [IsTopologicalAddGroup G] [CompactSpace G]
    (hopen : ∀ H : OpenAddSubgroup G, H = ⊤) : ConnectedSpace G := by
  have hfull (S : Set G) (hS : IsClopen S) (hzero : (0 : G) ∈ S) : S = univ := by
    obtain ⟨H, hH⟩ := IsTopologicalAddGroup.exist_openAddSubgroup_sub_clopen_nhds_of_zero hS hzero
    rw [hopen H] at hH
    exact univ_subset_iff.mp hH
  apply connectedSpace_iff_clopen.mpr
  refine ⟨inferInstance, fun S hS => ?_⟩
  by_cases hzero : (0 : G) ∈ S
  · exact Or.inr (hfull S hS hzero)
  · left
    have hSc := hfull Sᶜ hS.compl hzero
    ext x
    change (x ∈ S) ↔ False
    constructor
    · intro hx
      have hxc : x ∈ Sᶜ := by rw [hSc]; trivial
      exact hxc hx
    · exact False.elim

end Erdos335.Loeb
