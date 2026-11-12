import Erdos335.LoebQuotientDetectingCharacter
import Erdos335.CompactCircleEquiv

/-!
# Separating quotient points and nontrivial quotient subgroups by characters
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Filter Set Topology MeasureTheory
open scoped Pointwise

noncomputable section

namespace Erdos335.Loeb

variable {X : ℕ → Type*} [∀ n, AddCommGroup (X n)] [∀ n, Fintype (X n)]

local instance quotientSubgroupLoebSpace (U : Ultrafilter ℕ) :
    MeasurableSpace ((U : Filter ℕ).Product X) := loebMeasurableSpace U
local instance quotientSubgroupCircleSpace : MeasurableSpace (Additive Circle) :=
    borel (Additive Circle)
local instance quotientSubgroupCircleBorel : BorelSpace (Additive Circle) := ⟨rfl⟩

theorem exists_quotient_character_separating_zero
    (U : Ultrafilter ℕ) (hU : (U : Filter ℕ) ≤ atTop)
    (F : ℕ → ∀ n, X n →+ Additive Circle)
    [CompactSpace (countableUltralimitHom U F).range]
    (S : Set (countableUltralimitHom U F).range) (hS : MeasurableSet S)
    (H : AddSubgroup (countableUltralimitHom U F).range)
    (hH : ∀ s, s ∈ H ↔
      s +ᵥ S =ᵐ[Measure.map (countableUltralimitHom U F).rangeRestrict (loebMeasure U hU)] S)
    (y : (countableUltralimitHom U F).range ⧸ H) (hy : y ≠ 0) :
    ∃ ψ : ((countableUltralimitHom U F).range ⧸ H) →+ Additive Circle,
      Continuous ψ ∧ ψ y ≠ 0 := by
  obtain ⟨t, ht⟩ := QuotientAddGroup.mk'_surjective H y
  have hnot : ¬ t +ᵥ S =ᵐ[Measure.map (countableUltralimitHom U F).rangeRestrict
      (loebMeasure U hU)] S := by
    intro hp
    apply hy
    rw [← ht]
    exact (QuotientAddGroup.eq_zero_iff t).mpr ((hH t).mpr hp)
  obtain ⟨ψ, hψ, hvalue⟩ := exists_quotient_character_detecting_nonperiod U hU F S hS H
    (fun s hs => (hH s).mp hs) t hnot
  exact ⟨ψ, hψ, ht ▸ hvalue⟩

theorem exists_nontrivial_character_on_quotient_subgroup
    (U : Ultrafilter ℕ) (hU : (U : Filter ℕ) ≤ atTop)
    (F : ℕ → ∀ n, X n →+ Additive Circle)
    [CompactSpace (countableUltralimitHom U F).range]
    (S : Set (countableUltralimitHom U F).range) (hS : MeasurableSet S)
    (H : AddSubgroup (countableUltralimitHom U F).range)
    (hH : ∀ s, s ∈ H ↔
      s +ᵥ S =ᵐ[Measure.map (countableUltralimitHom U F).rangeRestrict (loebMeasure U hU)] S)
    (J : AddSubgroup ((countableUltralimitHom U F).range ⧸ H)) [Nontrivial J] :
    ∃ χ : J →+ AddCircle (1 : ℝ), Continuous χ ∧ χ ≠ 0 := by
  obtain ⟨x, hx⟩ := exists_ne (0 : J)
  have hxval : (x : (countableUltralimitHom U F).range ⧸ H) ≠ 0 := by
    intro hzero
    apply hx
    exact Subtype.ext hzero
  obtain ⟨ψ, hψ, hvalue⟩ := exists_quotient_character_separating_zero U hU F S hS H hH x hxval
  obtain ⟨e, _, heinv⟩ := exists_unitCircle_addEquiv
  let χ : J →+ AddCircle (1 : ℝ) := e.symm.toAddMonoidHom.comp (ψ.comp J.subtype)
  refine ⟨χ, heinv.comp (hψ.comp continuous_subtype_val), ?_⟩
  intro hz
  apply hvalue
  apply e.symm.injective
  have hzero := DFunLike.congr_fun hz x
  change e.symm (ψ x) = 0 at hzero
  simpa only [map_zero] using hzero

end Erdos335.Loeb

end
