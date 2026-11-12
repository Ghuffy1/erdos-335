import Erdos335.LoebConvolutionMean
import Erdos335.LoebDifferenceDeficit
import Erdos335.LoebTranslationStructure
import Erdos335.LoebSolidCore

/-!
# Essentially periodic cores from translation periods

Invariance under every translation in a positive subgroup forces each
coset section to have zero or full measure. Deleting the null sections
then gives a full-measure core whose subgroup saturation changes measure
by zero.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Filter Set MeasureTheory
open scoped Pointwise ENNReal

noncomputable section

namespace Erdos335.Loeb

local instance aePeriodCoreLoebSpace (U : Ultrafilter ℕ) (q : ℕ → ℕ+) :
    MeasurableSpace ((U : Filter ℕ).Product (fun n => ZMod (q n : ℕ))) := loebMeasurableSpace U

theorem loeb_section_zero_or_full_of_ae_periods
    (U : Ultrafilter ℕ) (hU : (U : Filter ℕ) ≤ atTop) (q : ℕ → ℕ+)
    (S : Set ((U : Filter ℕ).Product (fun n => ZMod (q n : ℕ)))) (hSm : MeasurableSet S)
    (H : AddSubgroup ((U : Filter ℕ).Product (fun n => ZMod (q n : ℕ))))
    (hHm : MeasurableSet (H : Set ((U : Filter ℕ).Product (fun n => ZMod (q n : ℕ)))))
    (hperiod : ∀ t ∈ H, t +ᵥ S =ᵐ[loebMeasure U hU] S)
    (a : (U : Filter ℕ).Product (fun n => ZMod (q n : ℕ))) :
    loebMeasure U hU (S ∩ (a +ᵥ (H : Set _))) = 0 ∨
      loebMeasure U hU (S ∩ (a +ᵥ (H : Set _))) = loebMeasure U hU
        (H : Set ((U : Filter ℕ).Product (fun n => ZMod (q n : ℕ)))) := by
  classical
  let G := (U : Filter ℕ).Product (fun n => ZMod (q n : ℕ))
  let μ := loebMeasure (X := fun n => ZMod (q n : ℕ)) U hU
  have : IsProbabilityMeasure μ := isProbabilityMeasure_loebMeasure U hU
  let X := S ∩ (a +ᵥ (H : Set G))
  let D := (a +ᵥ (H : Set G)) \ S
  have hcosm := measurable_loeb_coset U hU H hHm a
  have hXm : MeasurableSet X := hSm.inter hcosm
  have hDm : MeasurableSet D := hcosm.diff hSm
  by_cases hzero : μ X = 0
  · exact Or.inl hzero
  right
  have hXpos : 0 < μ X := pos_iff_ne_zero.mpr hzero
  have hXle : μ X ≤ μ (H : Set G) :=
    (measure_mono inter_subset_right).trans_eq (loebMeasure_coset U hU H a)
  apply le_antisymm hXle
  by_contra hn
  have hstrict : μ X < μ (H : Set G) := lt_of_not_ge hn
  have hDpos : 0 < μ D := by
    apply pos_iff_ne_zero.mpr
    intro hz
    have h := measure_sdiff_add_inter (μ := μ) (a +ᵥ (H : Set G)) hSm
    rw [hz, zero_add, inter_comm, loebMeasure_coset] at h
    exact hstrict.ne h
  have hnegDm : MeasurableSet (-D) := hDm.preimage (measurable_loeb_neg U hU)
  have hnegDpos : 0 < μ (-D) := by rwa [loebMeasure_neg U hU D hDm]
  obtain ⟨t, ht⟩ := loeb_exists_positive_indicator_convolution U hU X (-D) hXm hnegDm hXpos hnegDpos
  have htSum : t ∈ X + (-D) := positive_indicator_convolution_subset_add μ X (-D) ht
  have htH : t ∈ H := by
    obtain ⟨u, hu, v, hv, rfl⟩ := htSum
    have hvD : -v ∈ D := hv
    obtain ⟨k, hk, hku⟩ := hu.2
    obtain ⟨l, hl, hlv⟩ := hvD.1
    have heq : u + v = k - l := by
      change a + k = u at hku
      change a + l = -v at hlv
      have hvEq : v = -(a + l) := by rw [hlv, neg_neg]
      rw [← hku, hvEq]
      abel
    change u + v ∈ H
    rw [heq]
    exact H.sub_mem hk hl
  have hnull : (fun u => X.indicator (fun _ => (1 : ℝ)) u *
      (-D).indicator (fun _ => (1 : ℝ)) (t - u)) =ᵐ[μ] (fun _ => 0) := by
    filter_upwards [hperiod t htH] with u hu
    by_cases hx : u ∈ X
    · by_cases hd : t - u ∈ -D
      · have hd' : -(t - u) ∈ D := hd
        obtain ⟨s, hs, hsu⟩ := hu.mpr hx.1
        have heq : -(t - u) = s := by
          change t + s = u at hsu
          rw [← hsu]
          abel
        exact False.elim (hd'.2 (heq.symm ▸ hs))
      · simp only [Set.indicator_of_notMem hd, mul_zero]
    · simp only [Set.indicator_of_notMem hx, zero_mul]
  have hz : (∫ u, X.indicator (fun _ => (1 : ℝ)) u *
      (-D).indicator (fun _ => (1 : ℝ)) (t - u) ∂μ) = 0 := by
    rw [integral_congr_ae hnull, integral_zero]
  rw [hz] at ht
  exact (lt_irrefl 0) ht

theorem loeb_essential_periodic_core_of_ae_periods
    (U : Ultrafilter ℕ) (hU : (U : Filter ℕ) ≤ atTop) (q : ℕ → ℕ+)
    (S : Set ((U : Filter ℕ).Product (fun n => ZMod (q n : ℕ)))) (hSm : MeasurableSet S)
    (H : AddSubgroup ((U : Filter ℕ).Product (fun n => ZMod (q n : ℕ))))
    (hHm : MeasurableSet (H : Set ((U : Filter ℕ).Product (fun n => ZMod (q n : ℕ)))))
    (hHpos : 0 < loebMeasure (X := fun n => ZMod (q n : ℕ)) U hU (H : Set _))
    (hperiod : ∀ t ∈ H, t +ᵥ S =ᵐ[loebMeasure U hU] S) :
    ∃ C : Set ((U : Filter ℕ).Product (fun n => ZMod (q n : ℕ))),
      MeasurableSet C ∧ C ⊆ S ∧ loebMeasure U hU C = loebMeasure U hU S ∧
      loebMeasure U hU ((C + (H : Set _)) \ C) = 0 := by
  classical
  let G := (U : Filter ℕ).Product (fun n => ZMod (q n : ℕ))
  let μ := loebMeasure (X := fun n => ZMod (q n : ℕ)) U hU
  have : IsProbabilityMeasure μ := isProbabilityMeasure_loebMeasure U hU
  obtain ⟨C, hCm, hCS, hCmass, hsolid⟩ := exists_loeb_solid_full_measure_subset U hU q H hHm hHpos S hSm
  have hCae : C =ᵐ[μ] S := ae_eq_of_subset_of_measure_ge hCS hCmass.symm.le
    hCm.nullMeasurableSet (measure_ne_top μ S)
  have hCperiod (t : G) (ht : t ∈ H) : t +ᵥ C =ᵐ[μ] C :=
    (loeb_vadd_congr_ae U hU C S t hCae).trans ((hperiod t ht).trans hCae.symm)
  obtain ⟨R, hRC, hcover⟩ := loeb_exists_finite_coset_cover U hU q H hHm hHpos C
  have hfull (r : R) : μ (C ∩ ((r : G) +ᵥ (H : Set G))) = μ (H : Set G) := by
    rcases loeb_section_zero_or_full_of_ae_periods U hU q C hCm H hHm hCperiod r with hz | hf
    · have hpos : (0 : ℝ≥0∞) < μ (C ∩ ((r : G) +ᵥ (H : Set G))) := by
        simpa using hsolid r (hRC r.property)
      rw [hz] at hpos
      exact False.elim ((lt_irrefl (0 : ℝ≥0∞)) hpos)
    · exact hf
  have hnull (r : R) : μ (((r : G) +ᵥ (H : Set G)) \ C) = 0 := by
    have h := measure_sdiff_add_inter (μ := μ) ((r : G) +ᵥ (H : Set G)) hCm
    rw [inter_comm, hfull r, loebMeasure_coset] at h
    apply (ENNReal.add_left_inj (measure_ne_top μ (H : Set G))).mp
    simpa only [zero_add] using h
  refine ⟨C, hCm, hCS, hCmass, ?_⟩
  apply measure_mono_null _ (measure_iUnion_null hnull)
  rintro x ⟨hx, hn⟩
  rw [hcover] at hx
  obtain ⟨r, hr, k, hk, hkx⟩ := hx
  exact mem_iUnion.mpr ⟨⟨r, hr⟩, ⟨k, hk, hkx⟩, hn⟩

end Erdos335.Loeb

end
