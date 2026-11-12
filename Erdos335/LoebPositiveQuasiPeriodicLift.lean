import Erdos335.LoebNullExtensionBackground
import Erdos335.LoebNullExtensionUnique
import Erdos335.LoebNullExtensionInner
import Erdos335.LoebQuasiPeriodicExtensionData

/-!
# Lifting a positive quasi-periodic measurable core

For a nonextendible measurable core with two positive active pieces,
full-measure extensions preserving the sum's inner measure retain the
quasi-periodic decomposition. This is the measurable-core positive-piece
branch of Griesmer's Lemma 10.13.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Filter Set Topology MeasureTheory
open scoped Pointwise ENNReal

noncomputable section

namespace Erdos335.Loeb

local instance positiveQuasiPeriodicLiftLoebSpace (U : Ultrafilter ℕ) (q : ℕ → ℕ+) :
    MeasurableSpace ((U : Filter ℕ).Product (fun n => ZMod (q n : ℕ))) := loebMeasurableSpace U

theorem loeb_positive_quasiPeriodic_core_lift
    (U : Ultrafilter ℕ) (hU : (U : Filter ℕ) ≤ atTop) (q : ℕ → ℕ+)
    (A B A' B' : Set ((U : Filter ℕ).Product (fun n => ZMod (q n : ℕ))))
    (p : QuasiPeriodicPairData (loebMeasure U hU) (internalInnerMeasure U hU) A B)
    (hA'm : MeasurableSet A') (hB'm : MeasurableSet B')
    (hAA' : A ⊆ A') (hBB' : B ⊆ B')
    (hAmass : loebMeasure U hU A' = loebMeasure U hU A)
    (hBmass : loebMeasure U hU B' = loebMeasure U hU B)
    (hAactive : 0 < loebMeasure U hU p.left.active)
    (hBactive : 0 < loebMeasure U hU p.right.active)
    (hne : MeasureNonextendible (loebMeasure U hU) (internalInnerMeasure U hU) A B)
    (hCm : MeasurableSet (A + B))
    (hnotperiod : ¬ (A + B) + (p.period : Set _) =ᵐ[loebMeasure U hU] A + B)
    (hfull : internalInnerMeasure U hU (A' + B') = loebMeasure U hU (A + B)) :
    ∃ r : QuasiPeriodicPairData (loebMeasure U hU) (internalInnerMeasure U hU) A' B',
      r.period = p.period ∧ r.left.active =ᵐ[loebMeasure U hU] p.left.active ∧
      r.right.active =ᵐ[loebMeasure U hU] p.right.active := by
  obtain ⟨hAbackground, hBbackground⟩ := loeb_quasiPeriodic_null_extension_backgrounds U hU q A B A' B' p
    hAA' hBB' hAactive hBactive hne hCm hnotperiod hfull
  obtain ⟨left, hleftactive, hleftbackground, hleftanchor, hleftAE, _⟩ :=
    exists_quasiPeriodicDecomposition_of_null_extension U hU q p.period A A' p.left
      p.period_measurable hA'm hAA' hAmass hAbackground
  obtain ⟨right, hrightactive, hrightbackground, hrightanchor, hrightAE, _⟩ :=
    exists_quasiPeriodicDecomposition_of_null_extension U hU q p.period B B' p.right
      p.period_measurable hB'm hBB' hBmass hBbackground
  have hunique := loeb_quasiPeriodic_null_extension_unique_expression U hU q A B A' B' p
    hAA' hBB' hBactive hne hCm hnotperiod hfull
  have hinner : internalInnerMeasure U hU (A' + B') = internalInnerMeasure U hU (A + B) :=
    hfull.trans (internalInnerMeasure_eq U hU (A + B) hCm).symm
  have hactive := loeb_quasiPeriodic_extension_active_inner U hU q A B A' B' p hAA' hBB' hinner
  have hidentity : internalInnerMeasure U hU (left.active + right.active) =
      loebMeasure U hU left.active + loebMeasure U hU right.active := by
    rw [measure_congr hleftAE, measure_congr hrightAE, hleftactive, hrightactive]
    exact hactive.trans p.active_identity
  have hbackground : left.background.Nonempty ∨ right.background.Nonempty := by
    rcases p.nonempty_background with ⟨x, hx⟩ | ⟨x, hx⟩
    · left
      rw [hleftbackground]
      have hxold := p.left.background_eq_sdiff_coset ▸ hx
      exact ⟨x, hAA' hxold.1, hxold.2⟩
    · right
      rw [hrightbackground]
      have hxold := p.right.background_eq_sdiff_coset ▸ hx
      exact ⟨x, hBB' hxold.1, hxold.2⟩
  let r : QuasiPeriodicPairData (loebMeasure U hU) (internalInnerMeasure U hU) A' B' := {
    period := p.period
    period_measurable := p.period_measurable
    period_positive := p.period_positive
    left := left
    right := right
    nonempty_background := hbackground
    unique_expression := by simpa only [hleftanchor, hrightanchor] using hunique
    active_identity := hidentity
  }
  exact ⟨r, rfl, hleftAE, hrightAE⟩

end Erdos335.Loeb

end
