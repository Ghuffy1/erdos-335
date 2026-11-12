import Erdos335.CircleArcCutTransfer
import Erdos335.CompactDysonTransform

/-!
# The complement of a proper open circle arc
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set MeasureTheory
open scoped Pointwise

namespace Erdos335.Loeb

theorem unitCircle_compl_openArc
    (a b : ℝ) (hab : a < b) (hb : b < a + 1) :
    (((↑) : ℝ → AddCircle (1 : ℝ)) '' Ioo a b)ᶜ =
      ((↑) : ℝ → AddCircle (1 : ℝ)) '' Icc b (a + 1) := by
  have : Fact (0 < (1 : ℝ)) := ⟨zero_lt_one⟩
  have hcover : ((↑) : ℝ → AddCircle (1 : ℝ)) '' Icc a (a + 1) = univ :=
    AddCircle.coe_image_Icc_eq (p := (1 : ℝ)) a
  have haI : a ∈ Ico a (a + 1) := ⟨le_rfl, by linarith⟩
  ext z
  constructor
  · intro hz
    have hzcover : z ∈ ((↑) : ℝ → AddCircle (1 : ℝ)) '' Icc a (a + 1) := by
      rw [hcover]
      exact mem_univ z
    obtain ⟨x, hx, hxz⟩ := hzcover
    by_cases hxa : x = a
    · subst x
      refine ⟨a + 1, ⟨hb.le, le_rfl⟩, ?_⟩
      rw [AddCircle.coe_add_period]
      exact hxz
    · have hax : a < x := lt_of_le_of_ne hx.1 (Ne.symm hxa)
      have hbx : b ≤ x := by
        by_contra hn
        exact hz ⟨x, ⟨hax, lt_of_not_ge hn⟩, hxz⟩
      exact ⟨x, ⟨hbx, hx.2⟩, hxz⟩
  · rintro ⟨x, hx, rfl⟩ ⟨y, hy, heq⟩
    have hyI : y ∈ Ico a (a + 1) := ⟨hy.1.le, hy.2.trans hb⟩
    by_cases hxtop : x = a + 1
    · subst x
      rw [AddCircle.coe_add_period] at heq
      have hya : y = a := (AddCircle.coe_eq_coe_iff_of_mem_Ico hyI haI).mp heq
      exact hy.1.ne' hya
    · have hxI : x ∈ Ico a (a + 1) := ⟨(hab.trans_le hx.1).le,
        lt_of_le_of_ne hx.2 hxtop⟩
      have hyx : y = x := (AddCircle.coe_eq_coe_iff_of_mem_Ico hyI hxI).mp heq
      exact (not_lt_of_ge hx.1) (hyx ▸ hy.2)

theorem unitCircle_complement_ae_closedArc
    (S : Set (AddCircle (1 : ℝ))) (c : AddCircle (1 : ℝ))
    (a b : ℝ) (hab : a < b) (hb : b < a + 1)
    (hS : c +ᵥ S =ᵐ[volume] (((↑) : ℝ → AddCircle (1 : ℝ)) '' Ioo a b)) :
    c +ᵥ Sᶜ =ᵐ[volume] (((↑) : ℝ → AddCircle (1 : ℝ)) '' Icc b (a + 1)) := by
  have hcompl : (c +ᵥ S)ᶜ =ᵐ[volume]
      (((↑) : ℝ → AddCircle (1 : ℝ)) '' Ioo a b)ᶜ := by
    filter_upwards [hS] with x hx
    exact congrArg Not hx
  have hleft : (c +ᵥ S)ᶜ = c +ᵥ Sᶜ := by
    simp only [vadd_set_eq_neg_preimage, preimage_compl]
  rwa [hleft, unitCircle_compl_openArc a b hab hb] at hcompl

end Erdos335.Loeb
