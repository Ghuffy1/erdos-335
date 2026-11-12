import Erdos335.LoebCoarsenedPeriod
import Erdos335.LoebIrreducibleCore
import Erdos335.LoebQuasiPeriodicBackground

/-!
# Lifting a core with a null active piece

Removing the null active piece leaves an essentially periodic input.
Its sum has an essentially periodic finite-index stabilizer, and the
irreducible periodic-core lifting theorem applies.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Filter Set Topology MeasureTheory
open scoped Pointwise ENNReal

noncomputable section

namespace Erdos335.Loeb

theorem MeasureIrreducible.swap
    {G : Type*} [AddCommGroup G] [MeasurableSpace G]
    {μ : Measure G} {inner : Set G → ℝ≥0∞} {A B : Set G}
    (h : MeasureIrreducible μ inner A B) : MeasureIrreducible μ inner B A := by
  intro B₀ A₀ hBm hAm hB hA hBmass hAmass
  simpa only [add_comm] using h A₀ B₀ hAm hBm hA hB hAmass hBmass

local instance zeroActiveCoreLoebSpace (U : Ultrafilter ℕ) (q : ℕ → ℕ+) :
    MeasurableSpace ((U : Filter ℕ).Product (fun n => ZMod (q n : ℕ))) := loebMeasurableSpace U

theorem loeb_zero_left_active_core_lift
    (U : Ultrafilter ℕ) (hU : (U : Filter ℕ) ≤ atTop) (q : ℕ → ℕ+)
    (A B A' B' : Set ((U : Filter ℕ).Product (fun n => ZMod (q n : ℕ))))
    (p : QuasiPeriodicPairData (loebMeasure U hU) (internalInnerMeasure U hU) A B)
    (hA'm : MeasurableSet A') (hB'm : MeasurableSet B')
    (hA'pos : 0 < loebMeasure U hU A') (hB'pos : 0 < loebMeasure U hU B')
    (hAA' : A ⊆ A') (hBB' : B ⊆ B')
    (hAmass : loebMeasure U hU A' = loebMeasure U hU A)
    (hBmass : loebMeasure U hU B' = loebMeasure U hU B)
    (hirr : MeasureIrreducible (loebMeasure U hU) (internalInnerMeasure U hU) A' B')
    (hfull : internalInnerMeasure U hU (A' + B') = loebMeasure U hU A' + loebMeasure U hU B')
    (hzero : loebMeasure U hU p.left.active = 0) :
    ∃ K : AddSubgroup ((U : Filter ℕ).Product (fun n => ZMod (q n : ℕ))),
      MeasurableSet (K : Set ((U : Filter ℕ).Product (fun n => ZMod (q n : ℕ)))) ∧
      0 < loebMeasure (X := fun n => ZMod (q n : ℕ)) U hU (K : Set _) ∧
      ((A' + B') + (K : Set _) =ᵐ[loebMeasure U hU] A' + B' ∨
        ∃ r : QuasiPeriodicPairData (loebMeasure U hU) (internalInnerMeasure U hU) A' B',
          loebMeasure U hU r.left.active = 0 ∧ loebMeasure U hU r.right.active = 0) := by
  let G := (U : Filter ℕ).Product (fun n => ZMod (q n : ℕ))
  let μ := loebMeasure (X := fun n => ZMod (q n : ℕ)) U hU
  let C := p.left.background + B
  let K := AddAction.stabilizer G (C + (p.period : Set G))
  have hBgSub : p.left.background ⊆ A := subset_union_left.trans p.left.partition.ge
  have hMissing : μ (A \ p.left.background) = 0 := by
    apply measure_mono_null _ hzero
    rintro x ⟨hx, hxout⟩
    exact (p.left.partition ▸ hx).resolve_left hxout
  have hAeq : A =ᵐ[μ] p.left.background :=
    (ae_le_set.mpr hMissing).antisymm hBgSub.eventuallySubset
  have hBgMass : μ p.left.background = μ A := (measure_congr hAeq).symm
  have hBm : MeasurableSet B := p.right.partition.symm ▸
    (p.right.background_measurable.union p.right.active_measurable)
  obtain ⟨_, hCperiod⟩ := loeb_sum_with_essentially_periodic_summand U hU q p.period
    p.period_measurable p.period_positive B p.left.background p.left.background_periodic
  have hCperiod' : C + (p.period : Set G) =ᵐ[μ] C := by
    simpa only [C, add_comm B p.left.background] using hCperiod
  obtain ⟨hKm, hKpos, hKeq⟩ := loeb_saturation_stabilizer U hU q p.period
    p.period_measurable p.period_positive C
  have hCorePeriod : μ ((C + (K : Set G)) \ C) = 0 := by
    rw [hKeq]
    exact ae_le_set.mp hCperiod'.le
  have hK : K = AddAction.stabilizer G (C + (K : Set G)) := by rw [hKeq]
  refine ⟨K, hKm, hKpos, ?_⟩
  exact loeb_irreducible_periodic_core_lift U hU q K p.left.background B A' B'
    hKm hKpos p.left.background_measurable hBm hA'm hB'm hA'pos hB'pos
    (hBgSub.trans hAA') hBB' (hAmass.trans hBgMass.symm) hBmass hirr hfull hCorePeriod hK

theorem loeb_null_active_core_lift
    (U : Ultrafilter ℕ) (hU : (U : Filter ℕ) ≤ atTop) (q : ℕ → ℕ+)
    (A B A' B' : Set ((U : Filter ℕ).Product (fun n => ZMod (q n : ℕ))))
    (p : QuasiPeriodicPairData (loebMeasure U hU) (internalInnerMeasure U hU) A B)
    (hA'm : MeasurableSet A') (hB'm : MeasurableSet B')
    (hA'pos : 0 < loebMeasure U hU A') (hB'pos : 0 < loebMeasure U hU B')
    (hAA' : A ⊆ A') (hBB' : B ⊆ B')
    (hAmass : loebMeasure U hU A' = loebMeasure U hU A)
    (hBmass : loebMeasure U hU B' = loebMeasure U hU B)
    (hirr : MeasureIrreducible (loebMeasure U hU) (internalInnerMeasure U hU) A' B')
    (hfull : internalInnerMeasure U hU (A' + B') = loebMeasure U hU A' + loebMeasure U hU B')
    (hzero : loebMeasure U hU p.left.active = 0 ∨ loebMeasure U hU p.right.active = 0) :
    ∃ K : AddSubgroup ((U : Filter ℕ).Product (fun n => ZMod (q n : ℕ))),
      MeasurableSet (K : Set ((U : Filter ℕ).Product (fun n => ZMod (q n : ℕ)))) ∧
      0 < loebMeasure (X := fun n => ZMod (q n : ℕ)) U hU (K : Set _) ∧
      ((A' + B') + (K : Set _) =ᵐ[loebMeasure U hU] A' + B' ∨
        ∃ r : QuasiPeriodicPairData (loebMeasure U hU) (internalInnerMeasure U hU) A' B',
          loebMeasure U hU r.left.active = 0 ∧ loebMeasure U hU r.right.active = 0) := by
  rcases hzero with hleft | hright
  · exact loeb_zero_left_active_core_lift U hU q A B A' B' p hA'm hB'm hA'pos hB'pos
      hAA' hBB' hAmass hBmass hirr hfull hleft
  · have hfullSwap : internalInnerMeasure U hU (B' + A') = loebMeasure U hU B' + loebMeasure U hU A' := by
      simpa only [add_comm] using hfull
    obtain ⟨K, hKm, hKpos, hcase⟩ := loeb_zero_left_active_core_lift U hU q B A B' A' p.swap
      hB'm hA'm hB'pos hA'pos hBB' hAA' hBmass hAmass hirr.swap hfullSwap hright
    refine ⟨K, hKm, hKpos, ?_⟩
    rcases hcase with hperiod | ⟨r, hrleft, hrright⟩
    · exact Or.inl (by simpa only [add_comm B' A'] using hperiod)
    · exact Or.inr ⟨r.swap, hrright, hrleft⟩

end Erdos335.Loeb

end
