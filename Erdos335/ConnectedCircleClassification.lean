import Erdos335.CompactRealLiftKernel
import Mathlib.GroupTheory.QuotientGroup.Basic

/-!
# A connected compact finite cover of a circle is a circle
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Topology

namespace Erdos335.Loeb

theorem exists_circle_addEquiv_of_finite_character_kernel
    {G : Type*} [AddCommGroup G] [TopologicalSpace G] [IsTopologicalAddGroup G]
    [CompactSpace G] [ConnectedSpace G] [T2Space G]
    (φ : G →+ AddCircle (1 : ℝ)) (hφ : Continuous φ) (hne : φ ≠ 0)
    [Finite φ.ker] :
    ∃ e : G ≃+ AddCircle (1 : ℝ), Continuous e ∧ Continuous e.symm := by
  obtain ⟨f, hf, hlift⟩ := exists_real_hom_lift_of_circle_cover φ hφ hne
  have hsurj := real_hom_lift_of_circle_cover_surjective φ hφ hne f hf hlift
  obtain ⟨n, hn, hker⟩ := exists_positive_integer_period_of_real_lift φ f hlift
  have hnreal : (n : ℝ) ≠ 0 := by exact_mod_cast hn.ne'
  let e : AddCircle (n : ℝ) ≃+ G :=
    (QuotientAddGroup.quotientAddEquivOfEq hker.symm).trans
      (QuotientAddGroup.quotientKerEquivOfSurjective f hsurj)
  have hemk (x : ℝ) : e (x : AddCircle (n : ℝ)) = f x := by
    simp [e, QuotientAddGroup.quotientKerEquivOfSurjective,
      QuotientAddGroup.quotientKerEquivOfRightInverse]
  have he : Continuous e := by
    apply (QuotientAddGroup.isQuotientMap_mk (AddSubgroup.zmultiples (n : ℝ))).continuous_iff.mpr
    simpa only [Function.comp_def, hemk] using hf
  let s : AddCircle (1 : ℝ) ≃+ AddCircle (n : ℝ) :=
    AddCircle.equivAddCircle 1 (n : ℝ) one_ne_zero hnreal
  have hs : Continuous s := AddCircle.continuous_equivAddCircle _ _ _ _
  let g := s.trans e
  have hg : Continuous g := he.comp hs
  have hginv : Continuous g.symm := hg.continuous_symm_of_equiv_compact_to_t2
  exact ⟨g.symm, hginv, hg⟩

end Erdos335.Loeb
