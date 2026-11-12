import Mathlib.Algebra.Group.Pointwise.Finset.Basic
import Mathlib.GroupTheory.QuotientGroup.Defs
import Mathlib.Tactic.Abel

/-!
# The largest union of kernel cosets contained in a finite set
-/

set_option autoImplicit false

open Set
open scoped Pointwise Classical

namespace Erdos335

noncomputable def kernelCore {G H : Type*} [AddCommGroup G] [Fintype G]
    [AddCommGroup H] (φ : G →+ H) (R : Finset G) : Finset G :=
  Finset.univ.filter (fun x => ∀ k ∈ φ.ker, x + k ∈ R)

theorem mem_kernelCore {G H : Type*} [AddCommGroup G] [Fintype G]
    [AddCommGroup H] (φ : G →+ H) (R : Finset G) (x : G) :
    x ∈ kernelCore φ R ↔ ∀ k ∈ φ.ker, x + k ∈ R := by
  simp only [kernelCore, Finset.mem_filter, Finset.mem_univ, true_and]

theorem kernelCore_subset {G H : Type*} [AddCommGroup G] [Fintype G]
    [AddCommGroup H] (φ : G →+ H) (R : Finset G) : kernelCore φ R ⊆ R := by
  intro x hx
  simpa only [add_zero] using (mem_kernelCore φ R x).mp hx 0 φ.ker.zero_mem

theorem kernelCore_preimage_image {G H : Type*} [AddCommGroup G] [Fintype G]
    [AddCommGroup H] [DecidableEq H] (φ : G →+ H) (R : Finset G) :
    φ ⁻¹' ((kernelCore φ R).image φ : Set H) = (kernelCore φ R : Set G) := by
  ext x
  constructor
  · intro hx
    obtain ⟨y, hy, hyx⟩ := Finset.mem_image.mp hx
    apply (mem_kernelCore φ R x).mpr
    intro k hk
    have hdiff : x - y + k ∈ φ.ker := by
      change φ (x - y + k) = 0
      rw [map_add, map_sub, hyx, sub_self, zero_add]
      exact hk
    have hm := (mem_kernelCore φ R y).mp hy (x - y + k) hdiff
    convert hm using 1 <;> abel
  · intro hx
    exact Finset.mem_image.mpr ⟨x, hx, rfl⟩

end Erdos335
