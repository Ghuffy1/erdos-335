import Erdos335.LoebDetectingCharacter
import Erdos335.CompactQuotientCharacter

/-!
# Characters separating a non-period in an essential-stabilizer quotient
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Filter Set Topology MeasureTheory
open scoped Pointwise

noncomputable section

namespace Erdos335.Loeb

variable {X : ℕ → Type*} [∀ n, AddCommGroup (X n)] [∀ n, Fintype (X n)]

local instance quotientDetectingLoebSpace (U : Ultrafilter ℕ) :
    MeasurableSpace ((U : Filter ℕ).Product X) := loebMeasurableSpace U
local instance quotientDetectingCircleSpace : MeasurableSpace (Additive Circle) :=
    borel (Additive Circle)
local instance quotientDetectingCircleBorel : BorelSpace (Additive Circle) := ⟨rfl⟩

theorem exists_quotient_character_detecting_nonperiod
    (U : Ultrafilter ℕ) (hU : (U : Filter ℕ) ≤ atTop)
    (F : ℕ → ∀ n, X n →+ Additive Circle)
    [CompactSpace (countableUltralimitHom U F).range]
    (S : Set (countableUltralimitHom U F).range) (hS : MeasurableSet S)
    (H : AddSubgroup (countableUltralimitHom U F).range)
    (hHperiod : ∀ s ∈ H,
      s +ᵥ S =ᵐ[Measure.map (countableUltralimitHom U F).rangeRestrict (loebMeasure U hU)] S)
    (t : (countableUltralimitHom U F).range)
    (ht : ¬ t +ᵥ S =ᵐ[Measure.map (countableUltralimitHom U F).rangeRestrict
      (loebMeasure U hU)] S) :
    ∃ ψ : ((countableUltralimitHom U F).range ⧸ H) →+ Additive Circle,
      Continuous ψ ∧ ψ (QuotientAddGroup.mk' H t) ≠ 0 := by
  obtain ⟨p, hp, hpt, _, hperiod⟩ := exists_internal_character_detecting_nonperiod U hU F S hS t ht
  obtain ⟨χ, hχ⟩ := internalCharacterFunctions_addChar U F p hp
  have hχcont : Continuous χ := by
    apply continuous_induced_rng.mpr
    change Continuous (fun x => (χ x : ℂ))
    simpa only [hχ] using p.continuous
  have hHχ : ∀ s ∈ H, χ s = 1 := by
    intro s hs
    apply Subtype.ext
    exact (hχ s).trans (hperiod s (hHperiod s hs))
  obtain ⟨ψ, hψ, hcomp⟩ := exists_continuous_quotient_character H χ hχcont hHχ
  refine ⟨ψ, hψ, ?_⟩
  intro hzero
  have hvalue := DFunLike.congr_fun hcomp t
  change ψ (QuotientAddGroup.mk' H t) = χ t at hvalue
  have hχone : χ t = 1 := hvalue.symm.trans hzero
  exact hpt ((hχ t).symm.trans (congrArg (fun z : Circle => (z : ℂ)) hχone))

end Erdos335.Loeb

end
