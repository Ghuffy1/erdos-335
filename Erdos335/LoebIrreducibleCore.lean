import Erdos335.LoebSolidCore
import Erdos335.LoebPeriodicCoreLift
import Erdos335.LoebPeriodicEquality

/-!
# Irreducible pairs and a periodic full-measure core

Irreducibility preserves the inner measure when null parts of either
input are removed. This permits replacement of a periodic core by solid
subsets before applying the periodic-core lifting theorem.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Filter Set Topology MeasureTheory
open scoped Pointwise ENNReal

noncomputable section

namespace Erdos335.Loeb

def MeasureIrreducible {G : Type*} [AddCommGroup G] [MeasurableSpace G]
    (μ : Measure G) (inner : Set G → ℝ≥0∞) (A B : Set G) : Prop :=
  ∀ A₀ B₀ : Set G, MeasurableSet A₀ → MeasurableSet B₀ → A₀ ⊆ A → B₀ ⊆ B →
    μ A₀ = μ A → μ B₀ = μ B → inner (A₀ + B₀) = inner (A + B)

local instance irreducibleCoreLoebSpace (U : Ultrafilter ℕ) (q : ℕ → ℕ+) :
    MeasurableSpace ((U : Filter ℕ).Product (fun n => ZMod (q n : ℕ))) := loebMeasurableSpace U

theorem loeb_irreducible_or_reducible
    (U : Ultrafilter ℕ) (hU : (U : Filter ℕ) ≤ atTop) (q : ℕ → ℕ+)
    (A B : Set ((U : Filter ℕ).Product (fun n => ZMod (q n : ℕ)))) :
    MeasureIrreducible (loebMeasure U hU) (internalInnerMeasure U hU) A B ∨
      ∃ A₀ B₀ : Set ((U : Filter ℕ).Product (fun n => ZMod (q n : ℕ))),
        MeasurableSet A₀ ∧ MeasurableSet B₀ ∧ A₀ ⊆ A ∧ B₀ ⊆ B ∧
        loebMeasure U hU A₀ = loebMeasure U hU A ∧ loebMeasure U hU B₀ = loebMeasure U hU B ∧
        internalInnerMeasure U hU (A₀ + B₀) < internalInnerMeasure U hU (A + B) := by
  classical
  by_cases h : MeasureIrreducible (loebMeasure U hU) (internalInnerMeasure U hU) A B
  · exact Or.inl h
  right
  unfold MeasureIrreducible at h
  push_neg at h
  obtain ⟨A₀, B₀, hA₀m, hB₀m, hA₀sub, hB₀sub, hA₀mass, hB₀mass, hneq⟩ := h
  refine ⟨A₀, B₀, hA₀m, hB₀m, hA₀sub, hB₀sub, hA₀mass, hB₀mass, ?_⟩
  exact lt_of_le_of_ne (internalInnerMeasure_mono U hU (add_subset_add hA₀sub hB₀sub)) hneq

theorem loeb_irreducible_periodic_core_lift
    (U : Ultrafilter ℕ) (hU : (U : Filter ℕ) ≤ atTop) (q : ℕ → ℕ+)
    (H : AddSubgroup ((U : Filter ℕ).Product (fun n => ZMod (q n : ℕ))))
    (Acore Bcore A B : Set ((U : Filter ℕ).Product (fun n => ZMod (q n : ℕ))))
    (hHm : MeasurableSet (H : Set ((U : Filter ℕ).Product (fun n => ZMod (q n : ℕ)))))
    (hHpos : 0 < loebMeasure (X := fun n => ZMod (q n : ℕ)) U hU (H : Set _))
    (hAcorem : MeasurableSet Acore) (hBcorem : MeasurableSet Bcore)
    (hAm : MeasurableSet A) (hBm : MeasurableSet B)
    (hApos : 0 < loebMeasure U hU A) (hBpos : 0 < loebMeasure U hU B)
    (hAsub : Acore ⊆ A) (hBsub : Bcore ⊆ B)
    (hAmass : loebMeasure U hU A = loebMeasure U hU Acore)
    (hBmass : loebMeasure U hU B = loebMeasure U hU Bcore)
    (hirr : MeasureIrreducible (loebMeasure U hU) (internalInnerMeasure U hU) A B)
    (hfull : internalInnerMeasure U hU (A + B) = loebMeasure U hU A + loebMeasure U hU B)
    (hcoreperiod : loebMeasure U hU (((Acore + Bcore) + (H : Set _)) \ (Acore + Bcore)) = 0)
    (hH : H = AddAction.stabilizer ((U : Filter ℕ).Product (fun n => ZMod (q n : ℕ)))
      ((Acore + Bcore) + (H : Set _))) :
    (A + B) + (H : Set _) =ᵐ[loebMeasure U hU] A + B ∨
      ∃ p : QuasiPeriodicPairData (loebMeasure U hU) (internalInnerMeasure U hU) A B,
        loebMeasure U hU p.left.active = 0 ∧ loebMeasure U hU p.right.active = 0 := by
  let G := (U : Filter ℕ).Product (fun n => ZMod (q n : ℕ))
  let μ := loebMeasure (X := fun n => ZMod (q n : ℕ)) U hU
  let C := Acore + Bcore
  let T := C + (H : Set G)
  have hCT : C ⊆ T := fun x hx => ⟨x, hx, 0, H.zero_mem, add_zero x⟩
  have hTm : MeasurableSet T := measurable_saturation_of_positive_subgroup U hU q H hHm hHpos C
  have hNm : MeasurableSet (T \ C) := measurable_of_loebMeasure_zero U hU _ hcoreperiod
  have hCset : C = T \ (T \ C) := by
    ext x
    constructor
    · intro hx
      exact ⟨hCT hx, fun hn => hn.2 hx⟩
    · rintro ⟨hxT, hx⟩
      by_contra hn
      exact hx ⟨hxT, hn⟩
  have hCm : MeasurableSet C := hCset.symm ▸ hTm.diff hNm
  have hTmass : μ T = μ C := loeb_measure_saturation_eq_of_essential_period U hU H C hCm hcoreperiod
  have hcoreinner : internalInnerMeasure U hU C = internalInnerMeasure U hU (A + B) :=
    hirr Acore Bcore hAcorem hBcorem hAsub hBsub hAmass.symm hBmass.symm
  have hfullT : internalInnerMeasure U hU (A + B) = μ T :=
    hcoreinner.symm.trans ((internalInnerMeasure_eq U hU C hCm).trans hTmass.symm)
  obtain ⟨A₀, hA₀m, hA₀sub, hA₀mass, hA₀solid⟩ := exists_loeb_solid_full_measure_subset U hU q H hHm hHpos Acore hAcorem
  obtain ⟨B₀, hB₀m, hB₀sub, hB₀mass, hB₀solid⟩ := exists_loeb_solid_full_measure_subset U hU q H hHm hHpos Bcore hBcorem
  have hA₀A : A₀ ⊆ A := hA₀sub.trans hAsub
  have hB₀B : B₀ ⊆ B := hB₀sub.trans hBsub
  have hA₀A_mass : μ A₀ = μ A := hA₀mass.trans hAmass.symm
  have hB₀B_mass : μ B₀ = μ B := hB₀mass.trans hBmass.symm
  have hnewinner : internalInnerMeasure U hU (A₀ + B₀) = internalInnerMeasure U hU (A + B) :=
    hirr A₀ B₀ hA₀m hB₀m hA₀A hB₀B hA₀A_mass hB₀B_mass
  have hnewfull : internalInnerMeasure U hU (A₀ + B₀) = μ T := hnewinner.trans hfullT
  have hnewsub : A₀ + B₀ ⊆ T := (add_subset_add hA₀sub hB₀sub).trans hCT
  obtain ⟨hnewm, hnewAE⟩ := measurable_of_subset_full_inner U hU (A₀ + B₀) T hnewsub hTm hnewfull
  have hTperiod : T + (H : Set G) = T := by dsimp only [T]; rw [add_assoc, coe_add_coe]
  have hnewperiod := loeb_essential_period_of_full_inner_subset U hU q H (A₀ + B₀) T hnewsub hnewfull hTperiod
  have hsaturated : ((A₀ + B₀) + (H : Set G)) + (H : Set G) = (A₀ + B₀) + (H : Set G) := by
    rw [add_assoc, coe_add_coe]
  have hnewT : (A₀ + B₀) + (H : Set G) = T :=
    loeb_periodic_sets_eq_of_ae U hU q H hHpos _ _ hsaturated hTperiod (hnewperiod.trans hnewAE)
  have hnewH : H = AddAction.stabilizer G ((A₀ + B₀) + (H : Set G)) := by
    rw [hnewT]
    exact hH
  have hnewFullMass : internalInnerMeasure U hU (A + B) = μ A₀ + μ B₀ := by
    rw [hA₀A_mass, hB₀B_mass]
    exact hfull
  exact loeb_solid_periodic_core_lift U hU q H A₀ B₀ A B hHm hHpos hA₀m hB₀m hAm hBm
    (by rwa [hA₀A_mass]) (by rwa [hB₀B_mass]) hA₀A hB₀B hA₀A_mass.symm hB₀B_mass.symm
    (by simpa using hA₀solid) (by simpa using hB₀solid) (hnewinner.trans hnewFullMass) hnewFullMass
    (ae_le_set.mp hnewperiod.le) hnewH

end Erdos335.Loeb

end
