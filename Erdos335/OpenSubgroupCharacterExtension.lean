import Erdos335.CircleCharacterMeasure
import Mathlib.Algebra.Category.Grp.Injective
import Mathlib.Topology.Algebra.OpenSubgroup

/-!
# Extending a circle character from an open subgroup
-/

set_option autoImplicit false

open Set Filter
open scoped Topology

noncomputable section

namespace Erdos335.Loeb

theorem exists_continuous_circle_character_extension
    {G : Type*} [AddCommGroup G] [TopologicalSpace G] [IsTopologicalAddGroup G]
    (H : OpenAddSubgroup G) (χ : H →+ AddCircle (1 : ℝ)) (hχ : Continuous χ) :
    ∃ φ : G →+ AddCircle (1 : ℝ), Continuous φ ∧ φ.comp H.toAddSubgroup.subtype = χ := by
  have : Fact (0 < (1 : ℝ)) := ⟨zero_lt_one⟩
  obtain ⟨φ, hφ⟩ := (Module.Baer.of_divisible (AddCircle (1 : ℝ))).extension_property_addMonoidHom
    H.toAddSubgroup.subtype Subtype.coe_injective χ
  refine ⟨φ, ?_, hφ⟩
  apply continuous_of_continuousAt_zero φ
  have hcomp : (fun x : H => φ x) = χ := by
    funext x
    exact DFunLike.congr_fun hφ x
  have hzero : ContinuousAt (φ ∘ (Subtype.val : H → G)) (0 : H) := by
    change ContinuousAt (fun x : H => φ x) (0 : H)
    rw [hcomp]
    exact hχ.continuousAt
  exact H.isOpen.isOpenEmbedding_subtypeVal.continuousAt_iff.mp hzero

theorem exists_surjective_continuous_circle_character_extension
    {G : Type*} [AddCommGroup G] [TopologicalSpace G] [IsTopologicalAddGroup G]
    (H : OpenAddSubgroup G) (χ : H →+ AddCircle (1 : ℝ))
    (hχ : Continuous χ) (hχsurj : Function.Surjective χ) :
    ∃ φ : G →+ AddCircle (1 : ℝ), Continuous φ ∧ Function.Surjective φ ∧
      φ.comp H.toAddSubgroup.subtype = χ := by
  obtain ⟨φ, hφ, hrestrict⟩ := exists_continuous_circle_character_extension H χ hχ
  refine ⟨φ, hφ, ?_, hrestrict⟩
  intro z
  obtain ⟨x, hx⟩ := hχsurj z
  exact ⟨x, (DFunLike.congr_fun hrestrict x).trans hx⟩

end Erdos335.Loeb

end
