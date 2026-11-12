import Erdos335.ConnectedCircleHom
import Mathlib.Analysis.SpecialFunctions.Complex.CircleAddChar
import Mathlib.Topology.Homeomorph.Lemmas

/-!
# Additive circle models and surjective continuous characters
-/

set_option autoImplicit false

open Set

noncomputable section

namespace Erdos335.Loeb

theorem exists_unitCircle_addEquiv :
    ∃ e : AddCircle (1 : ℝ) ≃+ Additive Circle, Continuous e ∧ Continuous e.symm := by
  let f : AddCircle (1 : ℝ) →+ Additive Circle := AddCircle.toCircle_addChar.toAddMonoidHom
  have hinj : Function.Injective f := by
    intro x y hxy
    apply AddCircle.injective_toCircle one_ne_zero
    exact hxy
  have hsurj : Function.Surjective f := by
    intro y
    obtain ⟨x, hx⟩ := (AddCircle.homeomorphCircle (one_ne_zero : (1 : ℝ) ≠ 0)).surjective y.toMul
    refine ⟨x, ?_⟩
    change AddCircle.toCircle x = y.toMul
    simpa only [AddCircle.homeomorphCircle_apply] using hx
  let e := AddEquiv.ofBijective f ⟨hinj, hsurj⟩
  have he : Continuous e := AddCircle.continuous_toCircle
  exact ⟨e, he, he.continuous_symm_of_equiv_compact_to_t2⟩

theorem continuous_additiveCircle_hom_surjective_of_ne_zero
    {G : Type*} [AddGroup G] [TopologicalSpace G] [CompactSpace G] [ConnectedSpace G]
    (φ : G →+ Additive Circle) (hφ : Continuous φ) (hne : φ ≠ 0) :
    Function.Surjective φ := by
  obtain ⟨e, _, heinv⟩ := exists_unitCircle_addEquiv
  let ψ : G →+ AddCircle (1 : ℝ) := e.symm.toAddMonoidHom.comp φ
  have hψ : Continuous ψ := heinv.comp hφ
  have hψne : ψ ≠ 0 := by
    intro hz
    apply hne
    apply DFunLike.ext
    intro x
    change φ x = 0
    apply e.symm.injective
    have hx := DFunLike.congr_fun hz x
    change e.symm (φ x) = 0 at hx
    simpa only [map_zero] using hx
  have : Fact (0 < (1 : ℝ)) := ⟨zero_lt_one⟩
  have hsurj := continuous_circle_hom_surjective_of_ne_zero ψ hψ hψne
  intro y
  obtain ⟨x, hx⟩ := hsurj (e.symm y)
  exact ⟨x, e.symm.injective hx⟩

end Erdos335.Loeb

end
