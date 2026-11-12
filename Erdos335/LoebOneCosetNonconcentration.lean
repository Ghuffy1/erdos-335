import Erdos335.LoebOneCosetPair
import Erdos335.LoebFullMeasureRestriction
import Erdos335.LoebCosetSectionSums

/-!
# A one-coset input with a nonconcentrated partner
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Filter Set MeasureTheory
open scoped Pointwise ENNReal

noncomputable section

namespace Erdos335.Loeb

local instance oneCosetNonconcentrationLoebSpace (U : Ultrafilter ℕ) (q : ℕ → ℕ+) :
    MeasurableSpace ((U : Filter ℕ).Product (fun n => ZMod (q n : ℕ))) := loebMeasurableSpace U

theorem loeb_quasiPeriodic_pair_of_one_coset_and_nonconcentration
    (U : Ultrafilter ℕ) (hU : (U : Filter ℕ) ≤ atTop) (q : ℕ → ℕ+)
    (A B : Set ((U : Filter ℕ).Product (fun n => ZMod (q n : ℕ))))
    (H : AddSubgroup ((U : Filter ℕ).Product (fun n => ZMod (q n : ℕ))))
    (a : (U : Filter ℕ).Product (fun n => ZMod (q n : ℕ)))
    (hAcoset : A ⊆ a +ᵥ (H : Set _))
    (hBspread : ¬ ∃ b : (U : Filter ℕ).Product (fun n => ZMod (q n : ℕ)),
      B ⊆ b +ᵥ (H : Set ((U : Filter ℕ).Product (fun n => ZMod (q n : ℕ)))))
    (hAm : MeasurableSet A) (hBm : MeasurableSet B) (hSm : MeasurableSet (A + B))
    (hApos : 0 < loebMeasure U hU A) (hBpos : 0 < loebMeasure U hU B)
    (hfull : loebMeasure U hU (A + B) = loebMeasure U hU A + loebMeasure U hU B)
    (hirr : MeasureIrreducible (loebMeasure U hU) (internalInnerMeasure U hU) A B)
    (hne : MeasureNonextendible (loebMeasure U hU) (internalInnerMeasure U hU) A B)
    (hnotperiod : ¬ ∃ L : AddSubgroup ((U : Filter ℕ).Product (fun n => ZMod (q n : ℕ))),
      MeasurableSet (L : Set ((U : Filter ℕ).Product (fun n => ZMod (q n : ℕ)))) ∧
      0 < loebMeasure (X := fun n => ZMod (q n : ℕ)) U hU (L : Set _) ∧
      (A + B) + (L : Set _) =ᵐ[loebMeasure U hU] A + B) :
    Nonempty (QuasiPeriodicPairData (loebMeasure U hU) (internalInnerMeasure U hU) A B) := by
  let G := (U : Filter ℕ).Product (fun n => ZMod (q n : ℕ))
  let μ := loebMeasure (X := fun n => ZMod (q n : ℕ)) U hU
  have : IsProbabilityMeasure μ := isProbabilityMeasure_loebMeasure U hU
  have hnotexact : ¬ ∃ L : AddSubgroup G, MeasurableSet (L : Set G) ∧
      0 < μ (L : Set G) ∧ (A + B) + (L : Set G) = A + B := by
    rintro ⟨L, hLm, hLpos, hp⟩
    apply hnotperiod
    refine ⟨L, hLm, hLpos, ?_⟩
    rw [hp]
  obtain ⟨K, hKm, hKpos, hKH, ⟨p⟩⟩ := loeb_one_coset_input_reduction U hU q A B H a
    hAcoset hAm hBm hSm hApos hfull hnotexact
  have hBgpos : 0 < μ p.background := by
    by_contra hn
    have hBgzero : μ p.background = 0 := le_antisymm (not_lt.mp hn) bot_le
    have hparts : Disjoint p.background p.active := by
      apply Set.disjoint_left.mpr
      intro x hx hy
      exact Set.disjoint_left.mp p.separated ⟨x, hy, 0, K.zero_mem, add_zero x⟩ hx
    have hActmass : μ p.active = μ B := by
      have hm := (congrArg μ p.partition).trans (measure_union hparts p.active_measurable)
      rw [hBgzero, zero_add] at hm
      exact hm.symm
    have hActB : p.active ⊆ B := subset_union_right.trans p.partition.ge
    obtain ⟨_, hsumAE, _, _⟩ := loeb_irreducible_full_measure_restriction U hU q A B A p.active
      hAm p.active_measurable hSm Subset.rfl hActB rfl hActmass hirr hfull
    obtain ⟨b, hb, hbout⟩ := not_subset.mp (show ¬ B ⊆ p.anchor +ᵥ (H : Set G) from
      fun h => hBspread ⟨p.anchor, h⟩)
    have hactiveCoset : A + p.active ⊆ (a + p.anchor) +ᵥ (H : Set G) := by
      rintro z ⟨x, hx, y, hy, rfl⟩
      obtain ⟨k, hk, hkx⟩ := hAcoset hx
      obtain ⟨l, hl, hly⟩ := p.active_subset_coset hy
      refine ⟨k + l, H.add_mem hk (hKH hl), ?_⟩
      change a + k = x at hkx
      change p.anchor + l = y at hly
      change (a + p.anchor) + (k + l) = x + y
      rw [← hkx, ← hly]
      ac_rfl
    have htranslateCoset : b +ᵥ A ⊆ (a + b) +ᵥ (H : Set G) := by
      rintro z ⟨x, hx, rfl⟩
      obtain ⟨k, hk, hkx⟩ := hAcoset hx
      refine ⟨k, hk, ?_⟩
      change a + k = x at hkx
      change (a + b) + k = b + x
      rw [← hkx]
      ac_rfl
    have hout : a + b ∉ (a + p.anchor) +ᵥ (H : Set G) := by
      rintro ⟨k, hk, hka⟩
      apply hbout
      refine ⟨k, hk, ?_⟩
      change (a + p.anchor) + k = a + b at hka
      change p.anchor + k = b
      exact add_left_cancel (by simpa only [add_assoc] using hka)
    have hdisjoint : Disjoint (A + p.active) (b +ᵥ A) :=
      (disjoint_cosets_of_not_mem H (a + p.anchor) (a + b) hout).mono hactiveCoset htranslateCoset
    have hsub : b +ᵥ A ⊆ (A + B) \ (A + p.active) := by
      rintro z ⟨x, hx, rfl⟩
      refine ⟨⟨x, hx, b, hb, add_comm x b⟩, ?_⟩
      intro hact
      exact Set.disjoint_left.mp hdisjoint hact ⟨x, hx, rfl⟩
    have hzero : μ (b +ᵥ A) = 0 := measure_mono_null hsub (ae_le_set.mp hsumAE.symm.le)
    have hmass : μ (b +ᵥ A) = μ A := loebMeasure_image_add_left U hU b A
    exact hApos.ne' (hmass.symm.trans hzero)
  have hnotperiodSwap : ¬ ∃ L : AddSubgroup G, MeasurableSet (L : Set G) ∧
      0 < μ (L : Set G) ∧ (B + A) + (L : Set G) =ᵐ[μ] B + A := by
    simpa only [add_comm B A] using hnotperiod
  obtain ⟨r⟩ := loeb_quasiPeriodic_pair_of_nonnull_background U hU q B A K hKm hKpos p
    hAm (by simpa only [add_comm B A] using hSm) hBgpos hBpos hApos
    (by simpa only [add_comm] using hfull) hirr.swap hne.swap hnotperiodSwap
  exact ⟨r.swap⟩

end Erdos335.Loeb

end
