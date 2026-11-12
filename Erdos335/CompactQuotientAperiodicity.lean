import Erdos335.StabilizerPullback
import Mathlib.MeasureTheory.Group.AEStabilizer

/-!
# Essential aperiodicity after quotienting by the full stabilizer
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Filter Set MeasureTheory
open scoped Pointwise

namespace Erdos335.Loeb

theorem quotient_representative_has_trivial_ae_stabilizer
    {G K : Type*} [AddCommGroup G] [AddCommGroup K]
    [MeasurableSpace G] [MeasurableSpace K] [MeasurableAdd₂ G]
    (μ : Measure G) [μ.IsAddLeftInvariant]
    (φ : G →+ K) (hφ : Measurable φ) (hsurj : Function.Surjective φ)
    (S : Set G) (T : Set K) (hmodel : φ ⁻¹' T =ᵐ[μ] S)
    (hker : φ.ker = AddAction.aestabilizer G μ S) :
    ∀ t : K, t +ᵥ T =ᵐ[Measure.map φ μ] T → t = 0 := by
  intro t ht
  obtain ⟨g, rfl⟩ := hsurj t
  have hpre : φ ⁻¹' (φ g +ᵥ T) =ᵐ[μ] φ ⁻¹' T := ae_of_ae_map hφ.aemeasurable ht
  rw [preimage_vadd_addHom φ T g] at hpre
  have hgperiod : g +ᵥ S =ᵐ[μ] S :=
    ((vadd_set_ae_eq g).2 hmodel.symm).trans (hpre.trans hmodel)
  have hgker : g ∈ φ.ker := by
    rw [hker]
    exact hgperiod
  exact hgker

end Erdos335.Loeb
