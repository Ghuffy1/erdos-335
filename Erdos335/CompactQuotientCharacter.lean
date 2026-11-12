import Mathlib.Topology.Algebra.Group.Quotient
import Mathlib.Analysis.Complex.Circle
import Mathlib.Algebra.Group.AddChar

/-!
# Descending a continuous circle character to a quotient
-/

set_option autoImplicit false

open Set

namespace Erdos335.Loeb

theorem exists_continuous_quotient_character
    {G : Type*} [AddCommGroup G] [TopologicalSpace G] [IsTopologicalAddGroup G]
    (H : AddSubgroup G) (χ : AddChar G Circle) (hχ : Continuous χ)
    (hH : ∀ h ∈ H, χ h = 1) :
    ∃ ψ : (G ⧸ H) →+ Additive Circle,
      Continuous ψ ∧ ψ.comp (QuotientAddGroup.mk' H) = χ.toAddMonoidHom := by
  have hker : H ≤ χ.toAddMonoidHom.ker := by
    intro h hh
    change χ h = 1
    exact hH h hh
  let ψ := QuotientAddGroup.lift H χ.toAddMonoidHom hker
  refine ⟨ψ, ?_, QuotientAddGroup.lift_comp_mk' H χ.toAddMonoidHom hker⟩
  apply (QuotientAddGroup.isQuotientMap_mk H).continuous_iff.mpr
  have hcompose : ψ ∘ QuotientAddGroup.mk = χ.toAddMonoidHom := by
    funext x
    exact QuotientAddGroup.lift_mk' H hker x
  rw [hcompose]
  exact hχ

end Erdos335.Loeb
