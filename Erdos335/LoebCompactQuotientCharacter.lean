import Erdos335.LoebCompactPeriodCharacter
import Erdos335.CompactQuotientCharacter

/-!
# A nontrivial continuous character on a compact stabilizer quotient
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Filter Set Topology MeasureTheory
open scoped Pointwise

noncomputable section

namespace Erdos335.Loeb

variable {X : ℕ → Type*} [∀ n, AddCommGroup (X n)] [∀ n, Fintype (X n)]

local instance compactQuotientCharacterLoebSpace (U : Ultrafilter ℕ) :
    MeasurableSpace ((U : Filter ℕ).Product X) := loebMeasurableSpace U
local instance compactQuotientCharacterCircleSpace : MeasurableSpace (Additive Circle) :=
    borel (Additive Circle)
local instance compactQuotientCharacterCircleBorel : BorelSpace (Additive Circle) := ⟨rfl⟩

theorem exists_nontrivial_quotient_character_of_essential_periods
    (U : Ultrafilter ℕ) (hU : (U : Filter ℕ) ≤ atTop)
    (F : ℕ → ∀ n, X n →+ Additive Circle)
    [CompactSpace (countableUltralimitHom U F).range]
    (S : Set (countableUltralimitHom U F).range) (hS : MeasurableSet S)
    (hSpos : 0 < Measure.map (countableUltralimitHom U F).rangeRestrict (loebMeasure U hU) S)
    (hSlt : Measure.map (countableUltralimitHom U F).rangeRestrict (loebMeasure U hU) S < 1)
    (H : AddSubgroup (countableUltralimitHom U F).range)
    (hHperiod : ∀ t ∈ H,
      t +ᵥ S =ᵐ[Measure.map (countableUltralimitHom U F).rangeRestrict (loebMeasure U hU)] S) :
    ∃ ψ : ((countableUltralimitHom U F).range ⧸ H) →+ Additive Circle,
      Continuous ψ ∧ ψ ≠ 0 := by
  obtain ⟨p, hp, hne, _, hperiod⟩ := exists_nontrivial_internal_period_character U hU F S hS hSpos hSlt
  obtain ⟨χ, hχ⟩ := internalCharacterFunctions_addChar U F p hp
  have hχcont : Continuous χ := by
    apply continuous_induced_rng.mpr
    change Continuous (fun x => (χ x : ℂ))
    simpa only [hχ] using p.continuous
  have hHχ : ∀ t ∈ H, χ t = 1 := by
    intro t ht
    apply Subtype.ext
    exact (hχ t).trans (hperiod t (hHperiod t ht))
  obtain ⟨ψ, hψcont, hcompose⟩ := exists_continuous_quotient_character H χ hχcont hHχ
  refine ⟨ψ, hψcont, ?_⟩
  intro hzero
  apply hne
  have hχzero : χ.toAddMonoidHom = 0 := by
    simpa [hzero] using hcompose.symm
  ext x
  have hx : χ x = 1 := DFunLike.congr_fun hχzero x
  exact (hχ x).symm.trans (congrArg (fun z : Circle => (z : ℂ)) hx)

end Erdos335.Loeb

end
