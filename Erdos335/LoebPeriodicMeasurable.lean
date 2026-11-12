import Erdos335.LoebNaturalKernels
import Erdos335.LoebFiniteFunctions

/-!
# Internal sets from finite-quotient periods

A set saturated by a finite quotient kernel is the pullback of its finite
image, hence internal. This applies to every natural cyclic kernel.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Filter Set
open scoped Pointwise

namespace Erdos335.Loeb

theorem exists_internalSet_of_finiteQuotient_period
    {I F : Type*} {X : I → Type*} [∀ i, AddCommGroup (X i)]
    [AddCommGroup F] [Finite F]
    (U : Ultrafilter I) (p : ∀ i, X i →+ F)
    (C : Set ((U : Filter I).Product X))
    (hC : C + ((finiteQuotient U p).ker : Set _) = C) :
    ∃ A : ∀ i, Set (X i), internalSet U A = C := by
  let q := finiteQuotient U p
  have hpre : q ⁻¹' (q '' C) = C := by
    apply subset_antisymm
    · rintro x ⟨y, hy, hxy⟩
      have hk : x - y ∈ q.ker := by
        change q (x - y) = 0
        rw [map_sub, hxy, sub_self]
      have hx : x ∈ C + (q.ker : Set _) := ⟨y, hy, x - y, hk, by abel⟩
      rwa [hC] at hx
    · exact subset_preimage_image q C
  have hfun : finiteFunction U (fun i => p i) = (q : (U : Filter I).Product X → F) := by
    funext x
    induction x using Quotient.inductionOn with
    | h a => rfl
  refine ⟨fun i => (p i) ⁻¹' (q '' C), ?_⟩
  rw [← finiteFunction_preimage, hfun, hpre]

theorem exists_internalSet_of_natural_kernel_period
    (U : Ultrafilter ℕ) (q : ℕ → ℕ+) (h : ℕ+)
    (C : Set ((U : Filter ℕ).Product (fun n => ZMod (q n : ℕ))))
    (hC : C + (naturalCyclicKernel U q h : Set _) = C) :
    ∃ A : ∀ n, Set (ZMod (q n : ℕ)), internalSet U A = C := by
  classical
  by_cases hp : ∃ p : ∀ n, ZMod (q n : ℕ) →+ ZMod (h : ℕ),
      ∀ᶠ i in U, ∀ n : ℕ, p i (n : ZMod (q i : ℕ)) = (n : ZMod (h : ℕ))
  · rw [naturalCyclicKernel_eq U q h hp.choose hp.choose_spec] at hC
    exact exists_internalSet_of_finiteQuotient_period U hp.choose C hC
  · rw [naturalCyclicKernel, dite_eq_right hp, AddSubgroup.coe_top] at hC
    by_cases hne : C.Nonempty
    · obtain ⟨c, hc⟩ := hne
      have heq : C = univ := by
        apply eq_univ_iff_forall.mpr
        intro x
        have hx : x ∈ C + univ := ⟨c, hc, x - c, mem_univ _, by abel⟩
        rwa [hC] at hx
      exact ⟨fun _ => univ, (internalSet_univ U).trans heq.symm⟩
    · have heq : C = ∅ := not_nonempty_iff_eq_empty.mp hne
      exact ⟨fun _ => ∅, (internalSet_empty U).trans heq.symm⟩

end Erdos335.Loeb
