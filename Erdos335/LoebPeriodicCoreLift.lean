import Erdos335.LoebFullPeriodicCore

/-!
# Lifting a solid, essentially periodic equality core

A full-measure solid core with an essentially periodic sum yields either
an essentially periodic original sum or a quasi-periodic decomposition
with two null exceptional pieces. This proves the cyclic Loeb form of
Griesmer's Lemma 10.12.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Filter Set Topology MeasureTheory
open scoped ENNReal Pointwise

noncomputable section

namespace Erdos335.Loeb

local instance periodicCoreLiftLoebSpace (U : Ultrafilter ℕ) (q : ℕ → ℕ+) :
    MeasurableSpace ((U : Filter ℕ).Product (fun n => ZMod (q n : ℕ))) := loebMeasurableSpace U

theorem loeb_solid_extension_into_periodic_superset
    (U : Ultrafilter ℕ) (hU : (U : Filter ℕ) ≤ atTop) (q : ℕ → ℕ+)
    (H : AddSubgroup ((U : Filter ℕ).Product (fun n => ZMod (q n : ℕ))))
    (A B C T S : Set ((U : Filter ℕ).Product (fun n => ZMod (q n : ℕ))))
    (hBm : MeasurableSet B) (hCm : MeasurableSet C)
    (hCS : C ⊆ S) (hCT : C ⊆ T) (hAB : A + B ⊆ S)
    (hfull : internalInnerMeasure U hU S = loebMeasure U hU C)
    (hperiod : T + (H : Set _) = T)
    (hsolid : ∀ b ∈ B, 0 < loebMeasure U hU (B ∩ (b +ᵥ (H : Set _)))) :
    A + (B + (H : Set _)) ⊆ T := by
  rintro x ⟨a, ha, b, hb, rfl⟩
  have hDm : MeasurableSet ((fun y => a + y) '' B) := by
    have heq : (fun y => a + y) '' B = (fun y => -a + y) ⁻¹' B := by
      ext y
      constructor
      · rintro ⟨z, hz, rfl⟩
        simpa only [mem_preimage, neg_add_cancel_left] using hz
      · intro hy
        exact ⟨-a + y, hy, by simp⟩
    rw [heq]
    exact hBm.preimage (measurable_add_left U hU (-a))
  have hDS : (fun y => a + y) '' B ⊆ S := by
    rintro y ⟨z, hz, rfl⟩
    exact hAB (add_mem_add ha hz)
  have hzeroC := loeb_measure_sdiff_zero_of_full_inner U hU S C
    ((fun y => a + y) '' B) hCm hDm hCS hDS hfull
  have hzeroT : loebMeasure U hU (((fun y => a + y) '' B) \ T) = 0 :=
    measure_mono_null (sdiff_subset_sdiff_right hCT) hzeroC
  exact loeb_solid_translate_absorption U hU H B T a hperiod (by simpa using hsolid) hzeroT ⟨b, hb, rfl⟩

theorem loeb_solid_periodic_core_lift
    (U : Ultrafilter ℕ) (hU : (U : Filter ℕ) ≤ atTop) (q : ℕ → ℕ+)
    (H : AddSubgroup ((U : Filter ℕ).Product (fun n => ZMod (q n : ℕ))))
    (Acore Bcore A B : Set ((U : Filter ℕ).Product (fun n => ZMod (q n : ℕ))))
    (hHm : MeasurableSet (H : Set ((U : Filter ℕ).Product (fun n => ZMod (q n : ℕ)))))
    (hHpos : 0 < loebMeasure (X := fun n => ZMod (q n : ℕ)) U hU (H : Set _))
    (hAcorem : MeasurableSet Acore) (hBcorem : MeasurableSet Bcore)
    (hAm : MeasurableSet A) (hBm : MeasurableSet B)
    (hApos : 0 < loebMeasure U hU Acore) (hBpos : 0 < loebMeasure U hU Bcore)
    (hAsub : Acore ⊆ A) (hBsub : Bcore ⊆ B)
    (hAmass : loebMeasure U hU A = loebMeasure U hU Acore)
    (hBmass : loebMeasure U hU B = loebMeasure U hU Bcore)
    (hAsolid : ∀ a ∈ Acore, 0 < loebMeasure U hU (Acore ∩ (a +ᵥ (H : Set _))))
    (hBsolid : ∀ b ∈ Bcore, 0 < loebMeasure U hU (Bcore ∩ (b +ᵥ (H : Set _))))
    (hcore : internalInnerMeasure U hU (Acore + Bcore) =
      loebMeasure U hU Acore + loebMeasure U hU Bcore)
    (hfull : internalInnerMeasure U hU (A + B) = loebMeasure U hU Acore + loebMeasure U hU Bcore)
    (hcoreperiod : loebMeasure U hU (((Acore + Bcore) + (H : Set _)) \ (Acore + Bcore)) = 0)
    (hH : H = AddAction.stabilizer ((U : Filter ℕ).Product (fun n => ZMod (q n : ℕ)))
      ((Acore + Bcore) + (H : Set _))) :
    (A + B) + (H : Set _) =ᵐ[loebMeasure U hU] A + B ∨
      ∃ p : QuasiPeriodicPairData (loebMeasure U hU) (internalInnerMeasure U hU) A B,
        loebMeasure U hU p.left.active = 0 ∧ loebMeasure U hU p.right.active = 0 := by
  classical
  by_cases hperiod : (A + B) + (H : Set _) =ᵐ[loebMeasure U hU] A + B
  · exact Or.inl hperiod
  right
  let G := (U : Filter ℕ).Product (fun n => ZMod (q n : ℕ))
  let μ := loebMeasure (X := fun n => ZMod (q n : ℕ)) U hU
  letI : IsProbabilityMeasure μ := isProbabilityMeasure_loebMeasure U hU
  let C := Acore + Bcore
  let T := C + (H : Set G)
  let P := Acore + (H : Set G)
  let Q := Bcore + (H : Set G)
  have hCT : C ⊆ T := by
    intro c hc
    exact ⟨c, hc, 0, H.zero_mem, add_zero c⟩
  have hCS : C ⊆ A + B := add_subset_add hAsub hBsub
  have hTm : MeasurableSet T :=
    measurable_saturation_of_positive_subgroup U hU q H hHm hHpos C
  have hNm : MeasurableSet (T \ C) := measurable_of_loebMeasure_zero U hU (T \ C) hcoreperiod
  have hCset : C = T \ (T \ C) := by
    ext x
    constructor
    · intro hx
      exact ⟨hCT hx, fun hn => hn.2 hx⟩
    · rintro ⟨hxT, hx⟩
      by_contra hn
      exact hx ⟨hxT, hn⟩
  have hCm : MeasurableSet C := hCset.symm ▸ hTm.diff hNm
  have hCmass : μ C = μ Acore + μ Bcore := by
    rw [← internalInnerMeasure_eq U hU C hCm]
    exact hcore
  have hTmass : μ T = μ C :=
    loeb_measure_saturation_eq_of_essential_period U hU H C hCm hcoreperiod
  have hfullC : internalInnerMeasure U hU (A + B) = μ C := hfull.trans hCmass.symm
  have hfullT : internalInnerMeasure U hU (A + B) = μ T := hfullC.trans hTmass.symm
  have hTperiod : T + (H : Set G) = T := by
    dsimp only [T]
    rw [add_assoc, coe_add_coe]
  have hPperiod : P + (H : Set G) = P := by
    dsimp only [P]
    rw [add_assoc, coe_add_coe]
  have hQperiod : Q + (H : Set G) = Q := by
    dsimp only [Q]
    rw [add_assoc, coe_add_coe]
  have hPQ : P + Q = T := by
    dsimp only [P, Q, T, C]
    rw [add_add_add_comm, coe_add_coe]
  have hPm : MeasurableSet P :=
    measurable_saturation_of_positive_subgroup U hU q H hHm hHpos Acore
  have hQm : MeasurableSet Q :=
    measurable_saturation_of_positive_subgroup U hU q H hHm hHpos Bcore
  have hAP : Acore ⊆ P := by
    intro a ha
    exact ⟨a, ha, 0, H.zero_mem, add_zero a⟩
  have hBQ : Bcore ⊆ Q := by
    intro b hb
    exact ⟨b, hb, 0, H.zero_mem, add_zero b⟩
  have hAabsorb : A + Q ⊆ T :=
    loeb_solid_extension_into_periodic_superset U hU q H A Bcore C T (A + B)
      hBcorem hCm hCS hCT (add_subset_add Subset.rfl hBsub) hfullC hTperiod hBsolid
  have hBabsorb : P + B ⊆ T := by
    have hcross : B + Acore ⊆ A + B := by
      simpa only [add_comm] using (add_subset_add hAsub (show B ⊆ B from Subset.rfl))
    have h := loeb_solid_extension_into_periodic_superset U hU q H B Acore C T (A + B)
      hAcorem hCm hCS hCT hcross hfullC hTperiod hAsolid
    simpa only [add_comm] using h
  by_cases hlarge : μ Acore + μ Bcore < μ P + μ Q
  · have hPQm : MeasurableSet (P + Q) := hPQ.symm ▸ hTm
    have hsmall : internalInnerMeasure U hU (P + Q) < μ P + μ Q := by
      rw [internalInnerMeasure_eq U hU (P + Q) hPQm, hPQ, hTmass, hCmass]
      exact hlarge
    have hH' : H = AddAction.stabilizer G (P + Q) := by
      change H = AddAction.stabilizer G T at hH
      rwa [← hPQ] at hH
    have hAin : A ⊆ P := by
      intro a ha
      have hsub : a +ᵥ Q ⊆ P + Q := by
        rintro x ⟨b, hb, rfl⟩
        rw [hPQ]
        exact hAabsorb (add_mem_add ha hb)
      have hnull : μ ((a +ᵥ Q) \ (P + Q)) = 0 := by rw [sdiff_eq_empty.mpr hsub, measure_empty]
      have h := loeb_critical_translate_maximal U hU q P Q hPm hQm
        (hApos.trans_le (measure_mono hAP)) (hBpos.trans_le (measure_mono hBQ)) hsmall a hnull
      rw [← hH', hPperiod] at h
      exact h
    have hBin : B ⊆ Q := by
      intro b hb
      have hsub : b +ᵥ P ⊆ Q + P := by
        rintro x ⟨a, ha, rfl⟩
        rw [add_comm Q P, hPQ]
        simpa only [vadd_eq_add, add_comm] using hBabsorb (add_mem_add ha hb)
      have hnull : μ ((b +ᵥ P) \ (Q + P)) = 0 := by rw [sdiff_eq_empty.mpr hsub, measure_empty]
      have h := loeb_critical_translate_maximal U hU q Q P hQm hPm
        (hBpos.trans_le (measure_mono hBQ)) (hApos.trans_le (measure_mono hAP))
        (by simpa only [add_comm] using hsmall) b hnull
      rw [add_comm Q P, ← hH', hQperiod] at h
      exact h
    have hsum : A + B ⊆ T := by rw [← hPQ]; exact add_subset_add hAin hBin
    exact False.elim (hperiod (loeb_essential_period_of_full_inner_subset U hU q H (A + B) T hsum hfullT hTperiod))
  · have htotal : μ P + μ Q ≤ μ Acore + μ Bcore := le_of_not_gt hlarge
    have hPmass : μ P = μ Acore := by
      apply le_antisymm
      · apply (ENNReal.add_le_add_iff_right (measure_ne_top μ Bcore)).mp
        exact (add_le_add le_rfl (measure_mono hBQ)).trans htotal
      · exact measure_mono hAP
    have hQmass : μ Q = μ Bcore := by
      apply le_antisymm
      · apply (ENNReal.add_le_add_iff_left (measure_ne_top μ Acore)).mp
        exact (add_le_add (measure_mono hAP) le_rfl).trans htotal
      · exact measure_mono hBQ
    have hAperiod : μ (P \ Acore) = 0 := by
      rw [measure_sdiff hAP hAcorem.nullMeasurableSet (measure_ne_top μ _), hPmass, tsub_self]
    have hBperiod : μ (Q \ Bcore) = 0 := by
      rw [measure_sdiff hBQ hBcorem.nullMeasurableSet (measure_ne_top μ _), hQmass, tsub_self]
    have hCfull : C = P + Q :=
      loeb_add_eq_add_saturations_of_essential_periods U hU H Acore Bcore
        hHm hHpos hAcorem hBcorem hAperiod hBperiod
    have hCTeq : C = T := hCfull.trans hPQ
    have hHcore : H = AddAction.stabilizer G (Acore + Bcore) := by
      change H = AddAction.stabilizer G T at hH
      rwa [← hCTeq] at hH
    exact loeb_full_periodic_core_reduction U hU q H Acore Bcore A B hHm hHpos
      hAcorem hBcorem hAm hBm hApos hBpos hAsub hBsub hAmass hBmass
      hAperiod hBperiod hCmass hfullC hHcore hperiod

end Erdos335.Loeb

end
