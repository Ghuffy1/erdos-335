import Erdos335.LoebTranslationStructure
import Erdos335.LoebNullExtensionBackground
import Erdos335.LoebIrreducibleCore
import Erdos335.LoebNonextendible

/-!
# Translation of pair hypotheses and quasi-periodic pair data
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Filter Set MeasureTheory
open scoped Pointwise ENNReal

noncomputable section

namespace Erdos335.Loeb

variable {X : ℕ → Type*} [∀ n, AddCommGroup (X n)] [∀ n, Fintype (X n)]

local instance pairTranslationLoebSpace (U : Ultrafilter ℕ) :
    MeasurableSpace ((U : Filter ℕ).Product X) := loebMeasurableSpace U

theorem loeb_irreducible_translate_right
    (U : Ultrafilter ℕ) (hU : (U : Filter ℕ) ≤ atTop)
    (A B : Set ((U : Filter ℕ).Product X))
    (hirr : MeasureIrreducible (loebMeasure U hU) (internalInnerMeasure U hU) A B)
    (e : (U : Filter ℕ).Product X) :
    MeasureIrreducible (loebMeasure U hU) (internalInnerMeasure U hU) A (e +ᵥ B) := by
  intro P Q hPm hQm hPA hQB hPmass hQmass
  let T := (-e) +ᵥ Q
  have hTm : MeasurableSet T := measurable_loeb_translate U hU Q hQm (-e)
  have hTB : T ⊆ B := by
    rintro x ⟨y, hy, rfl⟩
    obtain ⟨b, hb, rfl⟩ := hQB hy
    simpa only [vadd_eq_add, neg_add_cancel_left] using hb
  have hTmass : loebMeasure U hU T = loebMeasure U hU B := by
    rw [show loebMeasure U hU T = loebMeasure U hU Q from loebMeasure_image_add_left U hU (-e) Q,
      hQmass, show loebMeasure U hU (e +ᵥ B) = loebMeasure U hU B from loebMeasure_image_add_left U hU e B]
  have hPT : P + T = (-e) +ᵥ (P + Q) := add_vadd_set_eq (-e) P Q
  calc
    internalInnerMeasure U hU (P + Q) = internalInnerMeasure U hU (P + T) := by
      rw [hPT, internalInnerMeasure_vadd]
    _ = internalInnerMeasure U hU (A + B) := hirr P T hPm hTm hPA hTB hPmass hTmass
    _ = internalInnerMeasure U hU (A + (e +ᵥ B)) := by
      rw [add_vadd_set_eq, internalInnerMeasure_vadd]

theorem loeb_nonextendible_translate_right
    (U : Ultrafilter ℕ) (hU : (U : Filter ℕ) ≤ atTop)
    (A B : Set ((U : Filter ℕ).Product X))
    (hne : MeasureNonextendible (loebMeasure U hU) (internalInnerMeasure U hU) A B)
    (e : (U : Filter ℕ).Product X) :
    MeasureNonextendible (loebMeasure U hU) (internalInnerMeasure U hU) A (e +ᵥ B) := by
  intro P Q hPm hQm hAP hBQ hsame
  let T := (-e) +ᵥ Q
  have hTm : MeasurableSet T := measurable_loeb_translate U hU Q hQm (-e)
  have hBT : B ⊆ T := by
    intro b hb
    refine ⟨e + b, hBQ ⟨b, hb, rfl⟩, ?_⟩
    change -e + (e + b) = b
    exact neg_add_cancel_left e b
  have hPT : P + T = (-e) +ᵥ (P + Q) := add_vadd_set_eq (-e) P Q
  have hsame' : internalInnerMeasure U hU (P + T) = internalInnerMeasure U hU (A + B) := by
    rw [hPT, internalInnerMeasure_vadd, hsame, add_vadd_set_eq, internalInnerMeasure_vadd]
  have h := hne P T hPm hTm hAP hBT hsame'
  rw [show loebMeasure U hU T = loebMeasure U hU Q from loebMeasure_image_add_left U hU (-e) Q] at h
  rwa [show loebMeasure U hU (e +ᵥ B) = loebMeasure U hU B from loebMeasure_image_add_left U hU e B]

def QuasiPeriodicPairData.loebTranslateRight
    (U : Ultrafilter ℕ) (hU : (U : Filter ℕ) ≤ atTop)
    {A B : Set ((U : Filter ℕ).Product X)}
    (p : QuasiPeriodicPairData (loebMeasure U hU) (internalInnerMeasure U hU) A B)
    (t : (U : Filter ℕ).Product X) :
    QuasiPeriodicPairData (loebMeasure U hU) (internalInnerMeasure U hU) A (t +ᵥ B) where
  period := p.period
  period_measurable := p.period_measurable
  period_positive := p.period_positive
  left := p.left
  right := p.right.loebTranslate U hU t
  nonempty_background := p.nonempty_background.elim Or.inl (fun h => Or.inr (h.image _))
  unique_expression := by
    rintro x hx y ⟨b, hb, rfl⟩ hxy
    have hxy' : x + b ∈ (p.left.anchor + p.right.anchor) +ᵥ
        (p.period : Set ((U : Filter ℕ).Product X)) := by
      obtain ⟨k, hk, hkxy⟩ := hxy
      refine ⟨k, hk, ?_⟩
      change (p.left.anchor + (t + p.right.anchor)) + k = x + (t + b) at hkxy
      change (p.left.anchor + p.right.anchor) + k = x + b
      apply add_left_cancel (a := t)
      calc
        t + ((p.left.anchor + p.right.anchor) + k) = (p.left.anchor + (t + p.right.anchor)) + k := by abel
        _ = x + (t + b) := hkxy
        _ = t + (x + b) := by abel
    obtain ⟨hx', hb'⟩ := p.unique_expression x hx b hb hxy'
    refine ⟨hx', ?_⟩
    obtain ⟨k, hk, hkb⟩ := hb'
    refine ⟨k, hk, ?_⟩
    change p.right.anchor + k = b at hkb
    change (t + p.right.anchor) + k = t + b
    rw [add_assoc, hkb]
  active_identity := by
    change internalInnerMeasure U hU (p.left.active + (t +ᵥ p.right.active)) =
      loebMeasure U hU p.left.active + loebMeasure U hU (t +ᵥ p.right.active)
    rw [add_vadd_set_eq, internalInnerMeasure_vadd,
      show loebMeasure U hU (t +ᵥ p.right.active) = loebMeasure U hU p.right.active from
        loebMeasure_image_add_left U hU t p.right.active]
    exact p.active_identity

end Erdos335.Loeb

end
