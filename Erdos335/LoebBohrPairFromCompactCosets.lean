import Erdos335.LoebInternalBohrPair

/-!
# Internal Bohr pair data from a compact circle-coset model
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter MeasureTheory
open scoped ENNReal Pointwise

noncomputable section

namespace Erdos335.Loeb

local instance bohrPairFromCosetsLoebSpace (U : Ultrafilter ℕ) (q : ℕ → ℕ+) :
    MeasurableSpace ((U : Filter ℕ).Product (fun n => ZMod (q n : ℕ))) := loebMeasurableSpace U
local instance bohrPairFromCosetsCircleSpace : MeasurableSpace (Additive Circle) := borel (Additive Circle)
local instance bohrPairFromCosetsCircleBorel : BorelSpace (Additive Circle) := ⟨rfl⟩

theorem exists_internalBohrPairData_of_compact_cosets
    (U : Ultrafilter ℕ) (hU : (U : Filter ℕ) ≤ atTop) (q : ℕ → ℕ+)
    (F : ℕ → ∀ n, ZMod (q n : ℕ) →+ Additive Circle)
    [CompactSpace (countableUltralimitHom U F).range]
    {L : Type*} [AddCommGroup L] [TopologicalSpace L] [IsTopologicalAddGroup L]
    [CompactSpace L] [T2Space L] [MeasurableSpace L] [BorelSpace L]
    (ψ : (countableUltralimitHom U F).range →+ L)
    (hψ : Continuous ψ) (hψsurj : Function.Surjective ψ)
    (A B : Set ((U : Filter ℕ).Product (fun n => ZMod (q n : ℕ))))
    (H : OpenAddSubgroup L) (e : H ≃+ AddCircle (1 : ℝ)) (he : Continuous e)
    (u v : L) (x y : AddCircle (1 : ℝ)) (s t : ℝ) (hs : 0 < s) (ht : 0 < t) (hst : s + t < 1)
    (hAsub : A ⊆ (ψ.comp (countableUltralimitHom U F).rangeRestrict) ⁻¹'
      (u +ᵥ ((Subtype.val : H → L) '' (e ⁻¹' (x +ᵥ (((↑) : ℝ → AddCircle (1 : ℝ)) '' Icc 0 s))))))
    (hBsub : B ⊆ (ψ.comp (countableUltralimitHom U F).rangeRestrict) ⁻¹'
      (v +ᵥ ((Subtype.val : H → L) '' (e ⁻¹' (y +ᵥ (((↑) : ℝ → AddCircle (1 : ℝ)) '' Icc 0 t))))))
    (hAmodel : A =ᵐ[loebMeasure U hU] (ψ.comp (countableUltralimitHom U F).rangeRestrict) ⁻¹'
      (u +ᵥ ((Subtype.val : H → L) '' (e ⁻¹' (x +ᵥ (((↑) : ℝ → AddCircle (1 : ℝ)) '' Icc 0 s))))))
    (hBmodel : B =ᵐ[loebMeasure U hU] (ψ.comp (countableUltralimitHom U F).rangeRestrict) ⁻¹'
      (v +ᵥ ((Subtype.val : H → L) '' (e ⁻¹' (y +ᵥ (((↑) : ℝ → AddCircle (1 : ℝ)) '' Icc 0 t)))))) :
    Nonempty (InternalBohrPairData U hU q A B) := by
  obtain ⟨m, p, hpnat, γ, hγ, hγsurj, hγrestrict, ρ, hρ, hker, hsets⟩ :=
    exists_internal_character_for_open_circle_cosets U hU q F ψ hψ hψsurj H e he
  let θ := ψ.comp (countableUltralimitHom U F).rangeRestrict
  have hθsurj : Function.Surjective θ := hψsurj.comp (countableUltralimitHom U F).rangeRestrict_surjective
  obtain ⟨a, ha⟩ := hθsurj u
  obtain ⟨b, hb⟩ := hθsurj v
  have ha' : (ψ.comp (countableUltralimitHom U F).rangeRestrict) a = u := ha
  have hb' : (ψ.comp (countableUltralimitHom U F).rangeRestrict) b = v := hb
  have hsetA : θ ⁻¹' (u +ᵥ ((Subtype.val : H → L) ''
      (e ⁻¹' (x +ᵥ (((↑) : ℝ → AddCircle (1 : ℝ)) '' Icc 0 s))))) =
      internalBohrCoset U q m p ρ a (γ u + x) s := by
    simpa only [ha', vadd_vadd, internalBohrCoset] using
      hsets a (x +ᵥ (((↑) : ℝ → AddCircle (1 : ℝ)) '' Icc 0 s))
  have hsetB : θ ⁻¹' (v +ᵥ ((Subtype.val : H → L) ''
      (e ⁻¹' (y +ᵥ (((↑) : ℝ → AddCircle (1 : ℝ)) '' Icc 0 t))))) =
      internalBohrCoset U q m p ρ b (γ v + y) t := by
    simpa only [hb', vadd_vadd, internalBohrCoset] using
      hsets b (y +ᵥ (((↑) : ℝ → AddCircle (1 : ℝ)) '' Icc 0 t))
  refine ⟨{
    modulus := m
    residue := p
    natural_residue := hpnat
    character := ρ
    character_surjective := ?_
    left_anchor := a
    right_anchor := b
    left_start := γ u + x
    right_start := γ v + y
    left_length := s
    right_length := t
    left_positive := hs
    right_positive := ht
    length_sum_lt_one := hst
    left_containment := ?_
    right_containment := ?_
    left_model := ?_
    right_model := ?_
  }⟩
  · rw [← hρ]
    exact hγsurj.comp hθsurj
  · rw [← hsetA]
    exact hAsub
  · rw [← hsetB]
    exact hBsub
  · rw [← hsetA]
    exact hAmodel
  · rw [← hsetB]
    exact hBmodel

end Erdos335.Loeb

end
