import Erdos335.LoebStrictBackground
import Erdos335.LoebEssentialStabilizer

/-!
# Pair recovery from a positive quasi-periodic input

The background period can be enlarged to its maximal essential period
while the positive active part remains separated. Irreducibility then
forces a strict background sum, whose stabilizer recovers the pair.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Filter Set MeasureTheory
open scoped Pointwise ENNReal

noncomputable section

namespace Erdos335.Loeb

local instance positiveQuasiPeriodicLoebSpace (U : Ultrafilter ℕ) (q : ℕ → ℕ+) :
    MeasurableSpace ((U : Filter ℕ).Product (fun n => ZMod (q n : ℕ))) := loebMeasurableSpace U

def QuasiPeriodicDecomposition.loebEnlargePeriod
    (U : Ultrafilter ℕ) (hU : (U : Filter ℕ) ≤ atTop) (q : ℕ → ℕ+)
    {A : Set ((U : Filter ℕ).Product (fun n => ZMod (q n : ℕ)))}
    {H : AddSubgroup ((U : Filter ℕ).Product (fun n => ZMod (q n : ℕ)))}
    (p : QuasiPeriodicDecomposition (loebMeasure U hU) H A)
    (K : AddSubgroup ((U : Filter ℕ).Product (fun n => ZMod (q n : ℕ))))
    (hHK : H ≤ K) (hActpos : 0 < loebMeasure U hU p.active)
    (hKperiod : loebMeasure U hU ((p.background + (K : Set _)) \ p.background) = 0) :
    QuasiPeriodicDecomposition (loebMeasure U hU) K A := {
  p with
  active_subset_coset := by
    intro x hx
    obtain ⟨k, hk, hkx⟩ := p.active_subset_coset hx
    exact ⟨k, hHK hk, hkx⟩
  separated := by
    apply Set.disjoint_left.mpr
    rintro z ⟨x, hx, k, hk, rfl⟩ hz
    have hparts : Disjoint p.background p.active := by
      apply Set.disjoint_left.mpr
      intro y hyBg hyAct
      exact Set.disjoint_left.mp p.separated ⟨y, hyAct, 0, H.zero_mem, add_zero y⟩ hyBg
    have hsub : p.active ⊆ (p.background + (K : Set _)) \ p.background := by
      intro y hy
      refine ⟨?_, fun hyBg => Set.disjoint_left.mp hparts hyBg hy⟩
      obtain ⟨kx, hkx, hkxx⟩ := p.active_subset_coset hx
      obtain ⟨ky, hky, hkyy⟩ := p.active_subset_coset hy
      refine ⟨x + k, hz, (ky - kx) - k, K.sub_mem (hHK (H.sub_mem hky hkx)) hk, ?_⟩
      change p.anchor + kx = x at hkxx
      change p.anchor + ky = y at hkyy
      change (x + k) + ((ky - kx) - k) = y
      rw [← hkxx, ← hkyy]
      abel
    exact hActpos.ne' (measure_mono_null hsub hKperiod)
  background_periodic := hKperiod
}

theorem loeb_quasiPeriodic_pair_of_positive_background_data
    (U : Ultrafilter ℕ) (hU : (U : Filter ℕ) ≤ atTop) (q : ℕ → ℕ+)
    (A B : Set ((U : Filter ℕ).Product (fun n => ZMod (q n : ℕ))))
    (H : AddSubgroup ((U : Filter ℕ).Product (fun n => ZMod (q n : ℕ))))
    (hHm : MeasurableSet (H : Set ((U : Filter ℕ).Product (fun n => ZMod (q n : ℕ)))))
    (hHpos : 0 < loebMeasure (X := fun n => ZMod (q n : ℕ)) U hU (H : Set _))
    (p : QuasiPeriodicDecomposition (loebMeasure U hU) H A)
    (hBm : MeasurableSet B) (hSm : MeasurableSet (A + B))
    (hBgpos : 0 < loebMeasure U hU p.background)
    (hActpos : 0 < loebMeasure U hU p.active) (hBpos : 0 < loebMeasure U hU B)
    (hfull : loebMeasure U hU (A + B) = loebMeasure U hU A + loebMeasure U hU B)
    (hirr : MeasureIrreducible (loebMeasure U hU) (internalInnerMeasure U hU) A B)
    (hne : MeasureNonextendible (loebMeasure U hU) (internalInnerMeasure U hU) A B)
    (hnotperiod : ¬ ∃ L : AddSubgroup ((U : Filter ℕ).Product (fun n => ZMod (q n : ℕ))),
      MeasurableSet (L : Set ((U : Filter ℕ).Product (fun n => ZMod (q n : ℕ)))) ∧
      0 < loebMeasure (X := fun n => ZMod (q n : ℕ)) U hU (L : Set _) ∧
      (A + B) + (L : Set _) =ᵐ[loebMeasure U hU] A + B) :
    ∃ r : QuasiPeriodicPairData (loebMeasure U hU) (internalInnerMeasure U hU) A B,
      H ≤ r.period ∧ r.left.active = p.active ∧ r.left.background = p.background := by
  obtain ⟨K, hKm, hKpos, hHK, hKperiod, hmax⟩ := loeb_exists_maximal_essential_period U hU q
    p.background p.background_measurable H hHm hHpos p.background_periodic
  let p' := p.loebEnlargePeriod U hU q K hHK hActpos hKperiod
  have hsmall := loeb_background_sum_strict_of_irreducible U hU q A B K hKm hKpos p'
    hBm hSm hActpos hfull hirr hnotperiod
  have hnotexact : ¬ ∃ L : AddSubgroup ((U : Filter ℕ).Product (fun n => ZMod (q n : ℕ))),
      MeasurableSet (L : Set ((U : Filter ℕ).Product (fun n => ZMod (q n : ℕ)))) ∧
      0 < loebMeasure (X := fun n => ZMod (q n : ℕ)) U hU (L : Set _) ∧
      (A + B) + (L : Set _) = A + B := by
    rintro ⟨L, hLm, hLpos, hperiod⟩
    apply hnotperiod
    refine ⟨L, hLm, hLpos, ?_⟩
    rw [hperiod]
  have hstab := loeb_background_stabilizer_eq_of_maximal_period U hU q A B K hKm hKpos p'
    hBm hBgpos hBpos hsmall hne (fun L _ _ hL => hmax L hL) hnotexact
  obtain ⟨r, hrK, hrA, hrBg⟩ := loeb_quasiPeriodic_pair_of_strict_background_data U hU q
    A B K hKm hKpos p' hBm hSm hBgpos hActpos hBpos hsmall hstab hfull hne hnotexact
  refine ⟨r, ?_, hrA, hrBg⟩
  rw [hrK]
  exact hHK

theorem loeb_quasiPeriodic_pair_of_positive_background
    (U : Ultrafilter ℕ) (hU : (U : Filter ℕ) ≤ atTop) (q : ℕ → ℕ+)
    (A B : Set ((U : Filter ℕ).Product (fun n => ZMod (q n : ℕ))))
    (H : AddSubgroup ((U : Filter ℕ).Product (fun n => ZMod (q n : ℕ))))
    (hHm : MeasurableSet (H : Set ((U : Filter ℕ).Product (fun n => ZMod (q n : ℕ)))))
    (hHpos : 0 < loebMeasure (X := fun n => ZMod (q n : ℕ)) U hU (H : Set _))
    (p : QuasiPeriodicDecomposition (loebMeasure U hU) H A)
    (hBm : MeasurableSet B) (hSm : MeasurableSet (A + B))
    (hBgpos : 0 < loebMeasure U hU p.background)
    (hActpos : 0 < loebMeasure U hU p.active) (hBpos : 0 < loebMeasure U hU B)
    (hfull : loebMeasure U hU (A + B) = loebMeasure U hU A + loebMeasure U hU B)
    (hirr : MeasureIrreducible (loebMeasure U hU) (internalInnerMeasure U hU) A B)
    (hne : MeasureNonextendible (loebMeasure U hU) (internalInnerMeasure U hU) A B)
    (hnotperiod : ¬ ∃ L : AddSubgroup ((U : Filter ℕ).Product (fun n => ZMod (q n : ℕ))),
      MeasurableSet (L : Set ((U : Filter ℕ).Product (fun n => ZMod (q n : ℕ)))) ∧
      0 < loebMeasure (X := fun n => ZMod (q n : ℕ)) U hU (L : Set _) ∧
      (A + B) + (L : Set _) =ᵐ[loebMeasure U hU] A + B) :
    Nonempty (QuasiPeriodicPairData (loebMeasure U hU) (internalInnerMeasure U hU) A B) := by
  obtain ⟨r, _, _, _⟩ := loeb_quasiPeriodic_pair_of_positive_background_data U hU q
    A B H hHm hHpos p hBm hSm hBgpos hActpos hBpos hfull hirr hne hnotperiod
  exact ⟨r⟩

end Erdos335.Loeb

end
