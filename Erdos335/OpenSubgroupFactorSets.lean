import Erdos335.LoebOpenSubgroupCoordinates
import Erdos335.SubgroupAEMeasure

/-!
# Pullback sets in an open-subgroup factor
-/

set_option autoImplicit false

open Set Filter MeasureTheory
open scoped Pointwise

namespace Erdos335.Loeb

theorem image_preimage_subgroup_factor
    {X Y K : Type*} [AddCommGroup X] [AddCommGroup Y] [AddCommGroup K]
    (H : AddSubgroup K) (e : X →+ Y) (φ : Y →+ K) (ψ : X →+ H)
    (hcomm : H.subtype.comp ψ = φ.comp e) (hrange : Set.range e = φ ⁻¹' (H : Set K))
    (C : Set K) (hC : C ⊆ H) :
    e '' (ψ ⁻¹' (H.subtype ⁻¹' C)) = φ ⁻¹' C := by
  have heq (x : X) : (ψ x : K) = φ (e x) := DFunLike.congr_fun hcomm x
  ext y
  constructor
  · rintro ⟨x, hx, rfl⟩
    change φ (e x) ∈ C
    rw [← heq]
    exact hx
  · intro hy
    have hyrange : y ∈ Set.range e := by
      rw [hrange]
      exact hC hy
    obtain ⟨x, rfl⟩ := hyrange
    refine ⟨x, ?_, rfl⟩
    change (ψ x : K) ∈ C
    rw [heq]
    exact hy

theorem subgroup_factor_preimage_add
    {X K : Type*} [AddCommGroup X] [AddCommGroup K]
    (H : AddSubgroup K) (ψ : X →+ H) (hsurj : Function.Surjective ψ)
    (C D : Set K) (hC : C ⊆ H) (hD : D ⊆ H) :
    ψ ⁻¹' (H.subtype ⁻¹' (C + D)) =
      (ψ ⁻¹' (H.subtype ⁻¹' C)) + (ψ ⁻¹' (H.subtype ⁻¹' D)) := by
  have h := subgroup_preimage_add H C D hC hD
  change H.subtype ⁻¹' (C + D) = (H.subtype ⁻¹' C) + (H.subtype ⁻¹' D) at h
  rw [h, preimage_add_of_surjective_addHom ψ hsurj]

end Erdos335.Loeb
