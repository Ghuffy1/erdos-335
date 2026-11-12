import Erdos335.CompactDysonTransform
import Mathlib.Topology.Compactness.SigmaCompact
import Mathlib.Topology.Algebra.Group.Compact

/-!
# Sigma-compactness along Dyson iteration
-/

set_option autoImplicit false

open Set
open scoped Pointwise

namespace Erdos335.Loeb

variable {G : Type*} [AddCommGroup G] [TopologicalSpace G]
variable [IsTopologicalAddGroup G] [T2Space G]

omit [AddCommGroup G] [IsTopologicalAddGroup G] in
theorem measurableSet_of_sigmaCompact [MeasurableSpace G] [BorelSpace G]
    (S : Set G) (hS : IsSigmaCompact S) : MeasurableSet S := by
  obtain ⟨C, hC, hCS⟩ := hS
  rw [← hCS]
  exact MeasurableSet.iUnion (fun n => (hC n).measurableSet)

omit [T2Space G] in
theorem isSigmaCompact_add_sets (A B : Set G)
    (hA : IsSigmaCompact A) (hB : IsSigmaCompact B) : IsSigmaCompact (A + B) := by
  obtain ⟨C, hC, hCA⟩ := hA
  obtain ⟨D, hD, hDB⟩ := hB
  have heq : (⋃ p : ℕ × ℕ, C p.1 + D p.2) = A + B := by
    ext z
    constructor
    · intro hz
      obtain ⟨p, x, hx, y, hy, rfl⟩ := mem_iUnion.mp hz
      exact add_mem_add (hCA ▸ mem_iUnion.mpr ⟨p.1, hx⟩) (hDB ▸ mem_iUnion.mpr ⟨p.2, hy⟩)
    · rintro ⟨x, hx, y, hy, rfl⟩
      obtain ⟨n, hn⟩ := mem_iUnion.mp (hCA.symm ▸ hx)
      obtain ⟨m, hm⟩ := mem_iUnion.mp (hDB.symm ▸ hy)
      exact mem_iUnion.mpr ⟨(n, m), add_mem_add hn hm⟩
  rw [← heq]
  exact isSigmaCompact_iUnion_of_isCompact _ (fun p => (hC p.1).add (hD p.2))

theorem isSigmaCompact_dysonGroup (A B : Set G)
    (hA : IsSigmaCompact A) (hB : IsSigmaCompact B) (e : G) :
    IsSigmaCompact (dysonGroupLeft A B e) ∧ IsSigmaCompact (dysonGroupRight A B e) := by
  obtain ⟨C, hC, hCA⟩ := hA
  obtain ⟨D, hD, hDB⟩ := hB
  have hleft : (⋃ n, C n ∪ (e +ᵥ D n)) = dysonGroupLeft A B e := by
    ext x
    constructor
    · intro hx
      obtain ⟨n, hx | ⟨y, hy, rfl⟩⟩ := mem_iUnion.mp hx
      · exact Or.inl (hCA ▸ mem_iUnion.mpr ⟨n, hx⟩)
      · exact Or.inr ⟨y, hDB ▸ mem_iUnion.mpr ⟨n, hy⟩, rfl⟩
    · rintro (hx | ⟨y, hy, rfl⟩)
      · obtain ⟨n, hn⟩ := mem_iUnion.mp (hCA.symm ▸ hx)
        exact mem_iUnion.mpr ⟨n, Or.inl hn⟩
      · obtain ⟨n, hn⟩ := mem_iUnion.mp (hDB.symm ▸ hy)
        exact mem_iUnion.mpr ⟨n, Or.inr ⟨y, hn, rfl⟩⟩
  have hright : (⋃ p : ℕ × ℕ, D p.1 ∩ ((-e) +ᵥ C p.2)) = dysonGroupRight A B e := by
    ext x
    constructor
    · intro hx
      obtain ⟨p, hxD, y, hyC, hyx⟩ := mem_iUnion.mp hx
      refine ⟨hDB ▸ mem_iUnion.mpr ⟨p.1, hxD⟩, ?_⟩
      have hy : e + x = y := by
        rw [← hyx]
        simp only [vadd_eq_add, add_neg_cancel_left]
      change e + x ∈ A
      rw [hy]
      exact hCA ▸ mem_iUnion.mpr ⟨p.2, hyC⟩
    · rintro ⟨hxB, hxA⟩
      obtain ⟨n, hn⟩ := mem_iUnion.mp (hDB.symm ▸ hxB)
      obtain ⟨m, hm⟩ := mem_iUnion.mp (hCA.symm ▸ hxA)
      exact mem_iUnion.mpr ⟨(n, m), hn, e + x, hm, by simp [vadd_eq_add]⟩
  constructor
  · rw [← hleft]
    exact isSigmaCompact_iUnion_of_isCompact _ (fun n =>
      (hC n).union ((hD n).image (continuous_const.add continuous_id)))
  · rw [← hright]
    exact isSigmaCompact_iUnion_of_isCompact _ (fun p =>
      (hD p.1).inter ((hC p.2).image (continuous_const.add continuous_id)))

end Erdos335.Loeb
