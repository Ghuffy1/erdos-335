import Erdos335.CompactOpenSubgroups
import Mathlib.GroupTheory.Index
import Mathlib.Data.Nat.Find

/-!
# Minimal open subgroups in a compact group

Bounded indices give a minimal open subgroup, which is connected.
-/

set_option autoImplicit false

open Set Topology

namespace Erdos335.Loeb

variable {G : Type*} [AddGroup G] [TopologicalSpace G] [IsTopologicalAddGroup G] [CompactSpace G]

theorem exists_minimal_open_addSubgroup_of_bounded_index
    (D : ℕ) (hD : ∀ H : OpenAddSubgroup G, H.toAddSubgroup.index ≤ D) :
    ∃ H : OpenAddSubgroup G, ∀ K : OpenAddSubgroup G, K ≤ H → K = H := by
  classical
  let P (n : ℕ) := ∃ H : OpenAddSubgroup G, H.toAddSubgroup.index = n
  have htop : P 1 := by
    refine ⟨⊤, ?_⟩
    change (⊤ : AddSubgroup G).index = 1
    exact AddSubgroup.index_top
  have hD1 : 1 ≤ D := by
    have h := hD (⊤ : OpenAddSubgroup G)
    change (⊤ : AddSubgroup G).index ≤ D at h
    simpa only [AddSubgroup.index_top] using h
  obtain ⟨H, hH⟩ := Nat.findGreatest_spec (P := P) hD1 htop
  refine ⟨H, fun K hKH => ?_⟩
  have hmax : K.toAddSubgroup.index ≤ Nat.findGreatest P D :=
    Nat.le_findGreatest (hD K) ⟨K, rfl⟩
  by_contra hne
  have hproper : K.toAddSubgroup < H.toAddSubgroup := lt_of_le_of_ne hKH
    (fun heq => hne (OpenAddSubgroup.toAddSubgroup_injective heq))
  have : Finite (G ⧸ K.toAddSubgroup) := K.toAddSubgroup.quotient_finite_of_isOpen K.isOpen
  have : K.toAddSubgroup.FiniteIndex := AddSubgroup.finiteIndex_of_finite_quotient
  have hlt := AddSubgroup.index_strictAnti hproper
  rw [hH] at hlt
  exact (not_lt_of_ge hmax) hlt

theorem connectedSpace_of_minimal_open_addSubgroup
    (H : OpenAddSubgroup G)
    (hmin : ∀ K : OpenAddSubgroup G, K ≤ H → K = H) : ConnectedSpace H := by
  have : CompactSpace H := isCompact_iff_compactSpace.mp H.isClosed.isCompact
  have : IsTopologicalAddGroup H := IsInducing.subtypeVal.isTopologicalAddGroup H.toAddSubgroup.subtype
  apply connectedSpace_of_no_proper_open_addSubgroup
  intro L
  let Jsub := L.toAddSubgroup.map H.toAddSubgroup.subtype
  have hJopen : IsOpen (Jsub : Set G) := by
    change IsOpen (Subtype.val '' (L : Set H))
    exact H.isOpen.isOpenMap_subtype_val _ L.isOpen
  let J : OpenAddSubgroup G := ⟨Jsub, hJopen⟩
  have hJH : J ≤ H := by
    rintro x ⟨y, _, rfl⟩
    exact y.property
  have hJeq : J = H := hmin J hJH
  apply top_unique
  intro x _
  have hxJ : (x : G) ∈ J := by rw [hJeq]; exact x.property
  obtain ⟨y, hy, hyx⟩ := hxJ
  have hyEq : y = x := Subtype.ext hyx
  rwa [hyEq] at hy

theorem open_addSubgroup_indices_unbounded_or_connected
    (G : Type*) [AddGroup G] [TopologicalSpace G] [IsTopologicalAddGroup G] [CompactSpace G] :
    (∀ D : ℕ, ∃ H : OpenAddSubgroup G, D < H.toAddSubgroup.index) ∨
      ∃ H : OpenAddSubgroup G, ConnectedSpace H := by
  classical
  by_cases h : ∃ D : ℕ, ∀ H : OpenAddSubgroup G, H.toAddSubgroup.index ≤ D
  · right
    obtain ⟨D, hD⟩ := h
    obtain ⟨H, hH⟩ := exists_minimal_open_addSubgroup_of_bounded_index D hD
    exact ⟨H, connectedSpace_of_minimal_open_addSubgroup H hH⟩
  · left
    push Not at h
    exact h

end Erdos335.Loeb
