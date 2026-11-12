import Erdos335.LoebQuasiPeriodicAbsorption
import Erdos335.LoebFullCosetPeriod

/-!
# Periodic backgrounds under null extensions

For a nonextendible quasi-periodic core with a positive opposite active
piece, every admissible new background coset is already full in measure.
Finite coset representatives make the enlarged background essentially
periodic.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Filter Set Topology MeasureTheory
open scoped Pointwise ENNReal

noncomputable section

namespace Erdos335.Loeb

theorem MeasureNonextendible.swap
    {G : Type*} [AddCommGroup G] [MeasurableSpace G]
    {μ : Measure G} {inner : Set G → ℝ≥0∞} {A B : Set G}
    (h : MeasureNonextendible μ inner A B) : MeasureNonextendible μ inner B A := by
  intro B' A' hBm hAm hB hA hsame
  have hsame' : inner (A' + B') = inner (A + B) := by simpa only [add_comm] using hsame
  simpa only [add_comm] using h A' B' hAm hBm hA hB hsame'

local instance quasiPeriodicLiftingLoebSpace (U : Ultrafilter ℕ) (q : ℕ → ℕ+) :
    MeasurableSpace ((U : Filter ℕ).Product (fun n => ZMod (q n : ℕ))) := loebMeasurableSpace U

theorem loeb_quasiPeriodic_extension_background
    (U : Ultrafilter ℕ) (hU : (U : Filter ℕ) ≤ atTop) (q : ℕ → ℕ+)
    (A B A' : Set ((U : Filter ℕ).Product (fun n => ZMod (q n : ℕ))))
    (p : QuasiPeriodicPairData (loebMeasure U hU) (internalInnerMeasure U hU) A B)
    (hAA' : A ⊆ A') (hBactive : 0 < loebMeasure U hU p.right.active)
    (hne : MeasureNonextendible (loebMeasure U hU) (internalInnerMeasure U hU) A B)
    (hnotperiod : ¬ (A + B) + (p.period : Set _) =ᵐ[loebMeasure U hU] A + B)
    (htranslations : ∀ g ∈ A', loebMeasure U hU ((g +ᵥ B) \ (A + B)) = 0) :
    let G := (U : Filter ℕ).Product (fun n => ZMod (q n : ℕ))
    let background := A' \ (p.left.anchor +ᵥ (p.period : Set G))
    loebMeasure U hU ((background + (p.period : Set G)) \ background) = 0 := by
  let G := (U : Filter ℕ).Product (fun n => ZMod (q n : ℕ))
  let μ := loebMeasure (X := fun n => ZMod (q n : ℕ)) U hU
  let background := A' \ (p.left.anchor +ᵥ (p.period : Set G))
  apply loeb_essential_period_of_full_cosets U hU q p.period p.period_measurable p.period_positive background
  intro g hg
  have hzero := loeb_nonextendible_quasiPeriodic_translate U hU q A B p g hg.2
    hBactive hne hnotperiod (htranslations g hg.1)
  apply measure_mono_null _ hzero
  rintro x ⟨hxcoset, hxout⟩
  refine ⟨hxcoset, ?_⟩
  intro hxA
  apply hxout
  refine ⟨hAA' hxA, ?_⟩
  rintro ⟨l, hl, hlx⟩
  obtain ⟨k, hk, hkx⟩ := hxcoset
  apply hg.2
  refine ⟨l - k, p.period.sub_mem hl hk, ?_⟩
  change p.left.anchor + l = x at hlx
  change g + k = x at hkx
  change p.left.anchor + (l - k) = g
  calc
    _ = (p.left.anchor + l) - k := by abel
    _ = (g + k) - k := by rw [hlx, ← hkx]
    _ = g := by simp

end Erdos335.Loeb

end
