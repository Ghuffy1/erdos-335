import Erdos335.LoebQuasiPeriodicLifting
import Erdos335.LoebInnerAbsorption

/-!
# Backgrounds of null extensions of a quasi-periodic core
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Filter Set Topology MeasureTheory
open scoped Pointwise ENNReal

noncomputable section

namespace Erdos335.Loeb

variable {X : ℕ → Type*} [∀ n, AddCommGroup (X n)] [∀ n, Fintype (X n)]

local instance nullBackgroundLoebSpace (U : Ultrafilter ℕ) :
    MeasurableSpace ((U : Filter ℕ).Product X) := loebMeasurableSpace U

theorem measurable_loeb_translate
    (U : Ultrafilter ℕ) (hU : (U : Filter ℕ) ≤ atTop)
    (S : Set ((U : Filter ℕ).Product X)) (hS : MeasurableSet S) (g : (U : Filter ℕ).Product X) :
    MeasurableSet (g +ᵥ S) := by
  have heq : g +ᵥ S = (fun x => -g + x) ⁻¹' S := by
    ext x
    constructor
    · rintro ⟨y, hy, rfl⟩
      simpa only [mem_preimage, vadd_eq_add, neg_add_cancel_left] using hy
    · intro hx
      exact ⟨-g + x, hx, by simp [vadd_eq_add]⟩
  rw [heq]
  exact hS.preimage (measurable_add_left U hU (-g))

theorem loeb_translation_sdiff_zero_of_full_inner
    (U : Ultrafilter ℕ) (hU : (U : Filter ℕ) ≤ atTop)
    (A B A' B' : Set ((U : Filter ℕ).Product X))
    (hBm : MeasurableSet B) (hCm : MeasurableSet (A + B))
    (hAA' : A ⊆ A') (hBB' : B ⊆ B')
    (hfull : internalInnerMeasure U hU (A' + B') = loebMeasure U hU (A + B))
    (g : (U : Filter ℕ).Product X) (hg : g ∈ A') :
    loebMeasure U hU ((g +ᵥ B) \ (A + B)) = 0 := by
  apply loeb_measure_sdiff_zero_of_full_inner U hU (A' + B') (A + B) (g +ᵥ B)
    hCm (measurable_loeb_translate U hU B hBm g) (add_subset_add hAA' hBB')
  · rintro x ⟨b, hb, rfl⟩
    exact add_mem_add hg (hBB' hb)
  · exact hfull

theorem loeb_quasiPeriodic_null_extension_backgrounds
    (U : Ultrafilter ℕ) (hU : (U : Filter ℕ) ≤ atTop) (q : ℕ → ℕ+)
    (A B A' B' : Set ((U : Filter ℕ).Product (fun n => ZMod (q n : ℕ))))
    (p : QuasiPeriodicPairData (loebMeasure U hU) (internalInnerMeasure U hU) A B)
    (hAA' : A ⊆ A') (hBB' : B ⊆ B')
    (hAactive : 0 < loebMeasure U hU p.left.active)
    (hBactive : 0 < loebMeasure U hU p.right.active)
    (hne : MeasureNonextendible (loebMeasure U hU) (internalInnerMeasure U hU) A B)
    (hCm : MeasurableSet (A + B))
    (hnotperiod : ¬ (A + B) + (p.period : Set _) =ᵐ[loebMeasure U hU] A + B)
    (hfull : internalInnerMeasure U hU (A' + B') = loebMeasure U hU (A + B)) :
    let G := (U : Filter ℕ).Product (fun n => ZMod (q n : ℕ))
    let Abackground := A' \ (p.left.anchor +ᵥ (p.period : Set G))
    let Bbackground := B' \ (p.right.anchor +ᵥ (p.period : Set G))
    loebMeasure U hU ((Abackground + (p.period : Set G)) \ Abackground) = 0 ∧
      loebMeasure U hU ((Bbackground + (p.period : Set G)) \ Bbackground) = 0 := by
  have hAm : MeasurableSet A := p.left.partition.symm ▸
    (p.left.background_measurable.union p.left.active_measurable)
  have hBm : MeasurableSet B := p.right.partition.symm ▸
    (p.right.background_measurable.union p.right.active_measurable)
  have hleft := loeb_quasiPeriodic_extension_background U hU q A B A' p hAA' hBactive hne hnotperiod
    (loeb_translation_sdiff_zero_of_full_inner U hU A B A' B' hBm hCm hAA' hBB' hfull)
  have hfullSwap : internalInnerMeasure U hU (B' + A') = loebMeasure U hU (B + A) := by
    simpa only [add_comm] using hfull
  have hnotperiodSwap : ¬ (B + A) + (p.swap.period : Set _) =ᵐ[loebMeasure U hU] B + A := by
    simpa only [QuasiPeriodicPairData.swap, add_comm A B] using hnotperiod
  have hright := loeb_quasiPeriodic_extension_background U hU q B A B' p.swap hBB' hAactive hne.swap hnotperiodSwap
    (loeb_translation_sdiff_zero_of_full_inner U hU B A B' A' hAm
      (by simpa only [add_comm] using hCm) hBB' hAA' hfullSwap)
  exact ⟨hleft, hright⟩

end Erdos335.Loeb

end
