import Erdos335.LoebOneActiveOutput
import Erdos335.LoebTranslationStructure
import Erdos335.LoebDysonBackgrounds
import Erdos335.LoebCosetSectionSums

/-!
# Recovering a pair from a strict periodic background

This is the second part of Griesmer's Lemma 5.17. The strict background
sum and its stabilizer are explicit premises. A noncritical active
component exhausts the remaining measure, and nonextendibility makes
the other input's background periodic.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Filter Set MeasureTheory
open scoped Pointwise ENNReal

noncomputable section

namespace Erdos335.Loeb

local instance strictBackgroundPairLoebSpace (U : Ultrafilter ℕ) (q : ℕ → ℕ+) :
    MeasurableSpace ((U : Filter ℕ).Product (fun n => ZMod (q n : ℕ))) := loebMeasurableSpace U

theorem loeb_quasiPeriodic_pair_of_strict_background_data
    (U : Ultrafilter ℕ) (hU : (U : Filter ℕ) ≤ atTop) (q : ℕ → ℕ+)
    (A B : Set ((U : Filter ℕ).Product (fun n => ZMod (q n : ℕ))))
    (H : AddSubgroup ((U : Filter ℕ).Product (fun n => ZMod (q n : ℕ))))
    (hHm : MeasurableSet (H : Set ((U : Filter ℕ).Product (fun n => ZMod (q n : ℕ)))))
    (hHpos : 0 < loebMeasure (X := fun n => ZMod (q n : ℕ)) U hU (H : Set _))
    (p : QuasiPeriodicDecomposition (loebMeasure U hU) H A)
    (hBm : MeasurableSet B) (hSm : MeasurableSet (A + B))
    (hBgpos : 0 < loebMeasure U hU p.background)
    (hActpos : 0 < loebMeasure U hU p.active) (hBpos : 0 < loebMeasure U hU B)
    (hsmall : internalInnerMeasure U hU (p.background + B) <
      loebMeasure U hU p.background + loebMeasure U hU B)
    (hstab : H = AddAction.stabilizer ((U : Filter ℕ).Product (fun n => ZMod (q n : ℕ)))
      (p.background + B))
    (hfull : loebMeasure U hU (A + B) = loebMeasure U hU A + loebMeasure U hU B)
    (hne : MeasureNonextendible (loebMeasure U hU) (internalInnerMeasure U hU) A B)
    (hnotperiod : ¬ ∃ L : AddSubgroup ((U : Filter ℕ).Product (fun n => ZMod (q n : ℕ))),
      MeasurableSet (L : Set ((U : Filter ℕ).Product (fun n => ZMod (q n : ℕ)))) ∧
      0 < loebMeasure (X := fun n => ZMod (q n : ℕ)) U hU (L : Set _) ∧
      (A + B) + (L : Set _) = A + B) :
    ∃ r : QuasiPeriodicPairData (loebMeasure U hU) (internalInnerMeasure U hU) A B,
      r.period = H ∧ r.left.active = p.active ∧ r.left.background = p.background := by
  classical
  let G := (U : Filter ℕ).Product (fun n => ZMod (q n : ℕ))
  let μ := loebMeasure (X := fun n => ZMod (q n : ℕ)) U hU
  have : IsProbabilityMeasure μ := isProbabilityMeasure_loebMeasure U hU
  change μ (A + B) = μ A + μ B at hfull
  let T := p.background + B
  have hAm : MeasurableSet A := p.partition.symm ▸ (p.background_measurable.union p.active_measurable)
  have hBgsub : p.background ⊆ A := subset_union_left.trans p.partition.ge
  have hActsub : p.active ⊆ A := subset_union_right.trans p.partition.ge
  have hTsub : T ⊆ A + B := add_subset_add hBgsub Subset.rfl
  obtain ⟨hTm, _, _, hid⟩ := loeb_measurable_kneser_identity U hU q p.background B
    p.background_measurable hBm hBgpos hBpos hsmall
  rw [← hstab] at hid
  have hTperiod : T + (H : Set G) = T := by
    apply subset_antisymm
    · rintro x ⟨s, hs, k, hk, rfl⟩
      have hfix : k +ᵥ T = T := by
        change k ∈ AddAction.stabilizer G T
        rw [← hstab]
        exact hk
      have hm : k + s ∈ T := by rw [← hfix]; exact ⟨s, hs, rfl⟩
      simpa only [add_comm s k] using hm
    · intro x hx
      exact ⟨x, hx, 0, H.zero_mem, add_zero x⟩
  have hparts : Disjoint p.background p.active := by
    apply Set.disjoint_left.mpr
    intro x hx hy
    exact Set.disjoint_left.mp p.separated ⟨x, hy, 0, H.zero_mem, add_zero x⟩ hx
  have hAmass : μ A = μ p.background + μ p.active :=
    (congrArg μ p.partition).trans (measure_union hparts p.active_measurable)
  have hsplit : A + B = T ∪ (p.active + B) :=
    (congrArg (fun S => S + B) p.partition).trans union_add
  obtain ⟨a, ha⟩ := p.active_nonempty
  obtain ⟨ka, hka, hkaa⟩ := p.active_subset_coset ha
  have hAcoset : p.active ⊆ a +ᵥ (H : Set G) := by
    intro x hx
    obtain ⟨kx, hkx, hkxx⟩ := p.active_subset_coset hx
    refine ⟨kx - ka, H.sub_mem hkx hka, ?_⟩
    change p.anchor + ka = a at hkaa
    change p.anchor + kx = x at hkxx
    change a + (kx - ka) = x
    rw [← hkaa, ← hkxx]
    abel
  obtain ⟨b, hb, hout, hnoncritical⟩ := loeb_noncritical_section_outside_periodic_background U hU q
    H hHm hHpos p.active B (A + B) T p.active_measurable hBm a ha hAcoset hsplit hTperiod hnotperiod
  let B₀ := B ∩ (b +ᵥ (H : Set G))
  let B₁ := B \ (b +ᵥ (H : Set G))
  let X := p.active + B₀
  let K := (a + b) +ᵥ (H : Set G)
  let δ := μ ((A + B) \ T)
  have hB₀m : MeasurableSet B₀ := hBm.inter (measurable_loeb_coset U hU H hHm b)
  have hB₁m : MeasurableSet B₁ := hBm.diff (measurable_loeb_coset U hU H hHm b)
  have hXcoset : X ⊆ K := by
    rintro z ⟨x, hx, y, hy, rfl⟩
    obtain ⟨k, hk, hkx⟩ := hAcoset hx
    obtain ⟨l, hl, hly⟩ := hy.2
    refine ⟨k + l, H.add_mem hk hl, ?_⟩
    change a + k = x at hkx
    change b + l = y at hly
    change (a + b) + (k + l) = x + y
    rw [← hkx, ← hly]
    abel
  have hTK : Disjoint T K := disjoint_periodic_set_coset H T hTperiod (a + b) hout
  have hXsub : X ⊆ (A + B) \ T := by
    intro x hx
    refine ⟨add_subset_add hActsub inter_subset_left hx, ?_⟩
    intro hxT
    exact Set.disjoint_left.mp hTK hxT (hXcoset hx)
  have hsplitMass : μ (A + B) = μ T + δ := by
    have h := measure_sdiff_add_inter (μ := μ) (A + B) hTm
    rw [inter_eq_right.mpr hTsub] at h
    exact h.symm.trans (add_comm _ _)
  have hidSwap : μ (B + (H : Set G)) + μ (p.background + (H : Set G)) =
      μ (B + p.background) + μ (H : Set G) := by
    simpa only [add_comm] using hid
  have hbound := loeb_coset_section_bound_of_kneser_identity U hU H hHm B p.background hidSwap b hb
  rw [add_comm B p.background] at hbound
  change μ B + μ p.background ≤ μ T + μ B₀ at hbound
  have hbound' : μ p.background + μ B ≤ μ T + μ B₀ := by
    simpa only [add_comm (μ B) (μ p.background)] using hbound
  have hmassBound : μ (A + B) ≤ μ T + (μ p.active + μ B₀) := by
    calc
      μ (A + B) = (μ p.background + μ B) + μ p.active := by rw [hfull, hAmass]; ac_rfl
      _ ≤ (μ T + μ B₀) + μ p.active := add_le_add hbound' le_rfl
      _ = μ T + (μ p.active + μ B₀) := by ac_rfl
  rw [hsplitMass] at hmassBound
  have hδupper : δ ≤ μ p.active + μ B₀ :=
    (ENNReal.add_le_add_iff_left (measure_ne_top μ T)).mp hmassBound
  have hXupper : internalInnerMeasure U hU X ≤ δ :=
    (internalInnerMeasure_mono U hU hXsub).trans_eq (internalInnerMeasure_eq U hU _ (hSm.diff hTm))
  have hδeq : δ = μ p.active + μ B₀ := le_antisymm hδupper (hnoncritical.trans hXupper)
  have hXinner : internalInnerMeasure U hU X = δ := le_antisymm hXupper (hδupper.trans hnoncritical)
  obtain ⟨hXm, _⟩ := measurable_of_subset_full_inner U hU X ((A + B) \ T) hXsub (hSm.diff hTm) hXinner
  have hXmass : μ X = δ := (internalInnerMeasure_eq U hU X hXm).symm.trans hXinner
  have hTX : Disjoint T X := hTK.mono_right hXcoset
  have hUsub : T ∪ X ⊆ A + B := union_subset hTsub (hXsub.trans sdiff_subset)
  have hUmass : μ (T ∪ X) = μ (A + B) := by rw [measure_union hTX hXm, hXmass, hsplitMass]
  have hUae : A + B =ᵐ[μ] T ∪ X :=
    (ae_eq_of_subset_of_measure_ge hUsub hUmass.ge (hTm.union hXm).nullMeasurableSet (measure_ne_top μ _)).symm
  have hnull : μ ((A + B) \ (T ∪ X)) = 0 := ae_le_set.mp hUae.le
  have hactiveBackground : p.active + B₁ ⊆ T := by
    rintro z ⟨x, hx, y, hy, rfl⟩
    by_contra hn
    have hay : a + y ∉ T := by
      intro h
      obtain ⟨k, hk, hkx⟩ := hAcoset hx
      have hm : (a + y) + k ∈ T + (H : Set G) := ⟨a + y, h, k, hk, rfl⟩
      rw [hTperiod] at hm
      apply hn
      change a + k = x at hkx
      convert hm using 1
      rw [← hkx]
      abel
    have hdisjK : Disjoint K ((a + y) +ᵥ (H : Set G)) := by
      apply disjoint_cosets_of_not_mem H
      rintro ⟨k, hk, hky⟩
      apply hy.2
      refine ⟨k, hk, ?_⟩
      change (a + b) + k = a + y at hky
      change b + k = y
      exact add_left_cancel (by simpa only [add_assoc] using hky)
    let E := y +ᵥ p.active
    have hEcoset : E ⊆ (a + y) +ᵥ (H : Set G) := by
      rintro w ⟨u, hu, rfl⟩
      obtain ⟨k, hk, hku⟩ := hAcoset hu
      refine ⟨k, hk, ?_⟩
      change a + k = u at hku
      change (a + y) + k = y + u
      rw [← hku]
      abel
    have hTE := (disjoint_periodic_set_coset H T hTperiod (a + y) hay).mono_right hEcoset
    have hEX := hdisjK.symm.mono hEcoset hXcoset
    have hEsub : E ⊆ (A + B) \ (T ∪ X) := by
      rintro w ⟨u, hu, rfl⟩
      refine ⟨⟨u, hActsub hu, y, hy.1, add_comm _ _⟩, ?_⟩
      rintro (hwT | hwX)
      · exact Set.disjoint_left.mp hTE hwT ⟨u, hu, rfl⟩
      · exact Set.disjoint_left.mp hEX ⟨u, hu, rfl⟩ hwX
    have hz := measure_mono_null hEsub hnull
    have hEmass : μ E = μ p.active := loebMeasure_image_add_left U hU y p.active
    rw [hEmass] at hz
    exact hActpos.ne' hz
  have hbackgroundSum : A + B₁ ⊆ T := by
    rintro z ⟨x, hx, y, hy, rfl⟩
    have hx' := p.partition ▸ hx
    rcases hx' with hxBg | hxAct
    · exact ⟨x, hxBg, y, hy.1, rfl⟩
    · exact hactiveBackground ⟨x, hxAct, y, hy, rfl⟩
  have hcosetPeriod : (b +ᵥ (H : Set G)) + (H : Set G) = b +ᵥ (H : Set G) := by
    rw [vadd_set_add_eq, coe_add_coe]
  have hB₁period : μ ((B₁ + (H : Set G)) \ B₁) = 0 := by
    apply loeb_nonextendible_part_periodic U hU q B A (b +ᵥ (H : Set G))ᶜ T H
      hBm hAm hHm hHpos hne.swap (complement_add_period H _ hcosetPeriod) hTperiod
    · simpa only [add_comm A B] using hTsub
    · change B₁ + A ⊆ T
      simpa only [add_comm B₁ A] using hbackgroundSum
  let left : QuasiPeriodicDecomposition μ H A := { p with anchor := a, active_subset_coset := hAcoset }
  let right : QuasiPeriodicDecomposition μ H B := {
    active := B₀
    background := B₁
    anchor := b
    active_measurable := hB₀m
    background_measurable := hB₁m
    active_nonempty := ⟨b, hb, 0, H.zero_mem, by simp⟩
    partition := by
      ext x
      constructor
      · intro hx
        by_cases hxc : x ∈ b +ᵥ (H : Set G)
        · exact Or.inr ⟨hx, hxc⟩
        · exact Or.inl ⟨hx, hxc⟩
      · rintro (hx | hx) <;> exact hx.1
    active_subset_coset := inter_subset_right
    separated := by
      apply Set.disjoint_left.mpr
      rintro x ⟨y, hy, k, hk, rfl⟩ hx
      apply hx.2
      have hm : y + k ∈ (b +ᵥ (H : Set G)) + (H : Set G) := ⟨y, hy.2, k, hk, rfl⟩
      rwa [hcosetPeriod] at hm
    background_periodic := hB₁period
  }
  refine ⟨{
    period := H
    period_measurable := hHm
    period_positive := hHpos
    left := left
    right := right
    nonempty_background := Or.inl (nonempty_of_measure_ne_zero hBgpos.ne')
    unique_expression := ?_
    active_identity := hXinner.trans hδeq
  }, rfl, rfl, rfl⟩
  intro x hx y hy hxy
  constructor
  · by_contra hxout
    have hxBg : x ∈ p.background := by
      rcases (p.partition ▸ hx) with hxBg | hxAct
      · exact hxBg
      · exact False.elim (hxout (hAcoset hxAct))
    exact Set.disjoint_left.mp hTK ⟨x, hxBg, y, hy, rfl⟩ hxy
  · by_contra hyout
    exact Set.disjoint_left.mp hTK (hbackgroundSum ⟨x, hx, y, ⟨hy, hyout⟩, rfl⟩) hxy

theorem loeb_quasiPeriodic_pair_of_strict_background
    (U : Ultrafilter ℕ) (hU : (U : Filter ℕ) ≤ atTop) (q : ℕ → ℕ+)
    (A B : Set ((U : Filter ℕ).Product (fun n => ZMod (q n : ℕ))))
    (H : AddSubgroup ((U : Filter ℕ).Product (fun n => ZMod (q n : ℕ))))
    (hHm : MeasurableSet (H : Set ((U : Filter ℕ).Product (fun n => ZMod (q n : ℕ)))))
    (hHpos : 0 < loebMeasure (X := fun n => ZMod (q n : ℕ)) U hU (H : Set _))
    (p : QuasiPeriodicDecomposition (loebMeasure U hU) H A)
    (hBm : MeasurableSet B) (hSm : MeasurableSet (A + B))
    (hBgpos : 0 < loebMeasure U hU p.background)
    (hActpos : 0 < loebMeasure U hU p.active) (hBpos : 0 < loebMeasure U hU B)
    (hsmall : internalInnerMeasure U hU (p.background + B) <
      loebMeasure U hU p.background + loebMeasure U hU B)
    (hstab : H = AddAction.stabilizer ((U : Filter ℕ).Product (fun n => ZMod (q n : ℕ)))
      (p.background + B))
    (hfull : loebMeasure U hU (A + B) = loebMeasure U hU A + loebMeasure U hU B)
    (hne : MeasureNonextendible (loebMeasure U hU) (internalInnerMeasure U hU) A B)
    (hnotperiod : ¬ ∃ L : AddSubgroup ((U : Filter ℕ).Product (fun n => ZMod (q n : ℕ))),
      MeasurableSet (L : Set ((U : Filter ℕ).Product (fun n => ZMod (q n : ℕ)))) ∧
      0 < loebMeasure (X := fun n => ZMod (q n : ℕ)) U hU (L : Set _) ∧
      (A + B) + (L : Set _) = A + B) :
    Nonempty (QuasiPeriodicPairData (loebMeasure U hU) (internalInnerMeasure U hU) A B) := by
  obtain ⟨r, _, _, _⟩ := loeb_quasiPeriodic_pair_of_strict_background_data U hU q
    A B H hHm hHpos p hBm hSm hBgpos hActpos hBpos hsmall hstab hfull hne hnotperiod
  exact ⟨r⟩

end Erdos335.Loeb

end
