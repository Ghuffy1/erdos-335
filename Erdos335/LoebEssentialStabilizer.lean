import Erdos335.LoebTranslationStructure
import Erdos335.LoebFiniteCosetCover
import Erdos335.LoebNullExtensionBackground
import Mathlib.MeasureTheory.Group.AEStabilizer

/-!
# Maximal essential periods above a positive Loeb period

A positive measurable period reduces saturation to finitely many
translations. The essential stabilizer is then measurable and saturates
the set without changing its measure.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Filter Set MeasureTheory
open scoped Pointwise ENNReal

noncomputable section

namespace Erdos335.Loeb

local instance essentialStabilizerLoebSpace (U : Ultrafilter ℕ) (q : ℕ → ℕ+) :
    MeasurableSpace ((U : Filter ℕ).Product (fun n => ZMod (q n : ℕ))) := loebMeasurableSpace U

theorem loeb_translate_ae_of_essential_period
    (U : Ultrafilter ℕ) (hU : (U : Filter ℕ) ≤ atTop) (q : ℕ → ℕ+)
    (S : Set ((U : Filter ℕ).Product (fun n => ZMod (q n : ℕ)))) (hSm : MeasurableSet S)
    (H : AddSubgroup ((U : Filter ℕ).Product (fun n => ZMod (q n : ℕ))))
    (hperiod : loebMeasure U hU ((S + (H : Set _)) \ S) = 0)
    (t : (U : Filter ℕ).Product (fun n => ZMod (q n : ℕ))) (ht : t ∈ H) :
    t +ᵥ S =ᵐ[loebMeasure U hU] S := by
  let μ := loebMeasure (X := fun n => ZMod (q n : ℕ)) U hU
  have : IsProbabilityMeasure μ := isProbabilityMeasure_loebMeasure U hU
  have hsub : t +ᵥ S ⊆ S + (H : Set _) := by
    rintro x ⟨s, hs, rfl⟩
    exact ⟨s, hs, t, ht, add_comm _ _⟩
  have hae : t +ᵥ S ≤ᵐ[μ] S := ae_le_set.mpr
    (measure_mono_null (sdiff_subset_sdiff_left hsub) hperiod)
  exact ae_eq_of_ae_subset_of_measure_ge hae (loebMeasure_image_add_left U hU t S).symm.le
    (measurable_loeb_translate U hU S hSm t).nullMeasurableSet (measure_ne_top μ S)

theorem loeb_exists_maximal_essential_period
    (U : Ultrafilter ℕ) (hU : (U : Filter ℕ) ≤ atTop) (q : ℕ → ℕ+)
    (S : Set ((U : Filter ℕ).Product (fun n => ZMod (q n : ℕ)))) (hSm : MeasurableSet S)
    (H : AddSubgroup ((U : Filter ℕ).Product (fun n => ZMod (q n : ℕ))))
    (hHm : MeasurableSet (H : Set ((U : Filter ℕ).Product (fun n => ZMod (q n : ℕ)))))
    (hHpos : 0 < loebMeasure (X := fun n => ZMod (q n : ℕ)) U hU (H : Set _))
    (hperiod : loebMeasure U hU ((S + (H : Set _)) \ S) = 0) :
    ∃ K : AddSubgroup ((U : Filter ℕ).Product (fun n => ZMod (q n : ℕ))),
      MeasurableSet (K : Set ((U : Filter ℕ).Product (fun n => ZMod (q n : ℕ)))) ∧
      0 < loebMeasure (X := fun n => ZMod (q n : ℕ)) U hU (K : Set _) ∧ H ≤ K ∧
      loebMeasure U hU ((S + (K : Set _)) \ S) = 0 ∧
      ∀ L : AddSubgroup ((U : Filter ℕ).Product (fun n => ZMod (q n : ℕ))),
        loebMeasure U hU ((S + (L : Set _)) \ S) = 0 → L ≤ K := by
  classical
  let G := (U : Filter ℕ).Product (fun n => ZMod (q n : ℕ))
  let μ := loebMeasure (X := fun n => ZMod (q n : ℕ)) U hU
  let : VAddInvariantMeasure G G μ := ⟨fun t _ _ => loebMeasure_preimage_add_left U hU t _⟩
  let K := AddAction.aestabilizer G μ S
  have hHK : H ≤ K := fun t ht => loeb_translate_ae_of_essential_period U hU q S hSm H hperiod t ht
  have hKH : (K : Set G) + (H : Set G) = K := by
    apply subset_antisymm
    · rintro x ⟨k, hk, h, hh, rfl⟩
      exact K.add_mem hk (hHK hh)
    · intro x hx
      exact ⟨x, hx, 0, H.zero_mem, add_zero x⟩
  have hKm : MeasurableSet (K : Set G) := by
    rw [← hKH]
    exact measurable_saturation_of_positive_subgroup U hU q H hHm hHpos K
  have hKpos : 0 < μ (K : Set G) := hHpos.trans_le (measure_mono hHK)
  obtain ⟨R, hRK, hcover⟩ := loeb_exists_finite_coset_cover U hU q H hHm hHpos K
  have hSS : S ⊆ S + (H : Set G) := fun x hx => ⟨x, hx, 0, H.zero_mem, add_zero x⟩
  have hbase : S + (H : Set G) =ᵐ[μ] S :=
    (ae_le_set.mpr hperiod).antisymm hSS.eventuallySubset
  let D (r : R) := (r.val +ᵥ (S + (H : Set G))) \ S
  have hD (r : R) : μ (D r) = 0 := by
    have hshift := loeb_vadd_congr_ae U hU (S + (H : Set G)) S r.val hbase
    have hfix : r.val +ᵥ S =ᵐ[μ] S := hRK r.property
    exact ae_le_set.mp (hshift.trans hfix).le
  have hnull : μ ((S + (K : Set G)) \ S) = 0 := by
    apply measure_mono_null _ (measure_iUnion_null hD)
    rintro x ⟨⟨s, hs, k, hk, rfl⟩, hn⟩
    have hkr : k ∈ (R : Set G) + (H : Set G) := by rw [← hcover, hKH]; exact hk
    obtain ⟨r, hr, h, hh, hrhk⟩ := hkr
    refine mem_iUnion.mpr ⟨⟨r, hr⟩, ?_, hn⟩
    refine ⟨s + h, ⟨s, hs, h, hh, rfl⟩, ?_⟩
    change r + (s + h) = s + k
    rw [← hrhk]
    ac_rfl
  refine ⟨K, hKm, hKpos, hHK, hnull, ?_⟩
  intro L hL t ht
  exact loeb_translate_ae_of_essential_period U hU q S hSm L hL t ht

end Erdos335.Loeb

end
