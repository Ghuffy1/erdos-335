import Erdos335.LoebShiftedProfileMasks
import Erdos335.LoebAEPeriodCore

/-!
# Finite natural masks from a positive subgroup of almost-everywhere periods
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Filter Set MeasureTheory
open scoped Pointwise ENNReal

noncomputable section

namespace Erdos335.Loeb

local instance naturalPeriodMasksLoebSpace (U : Ultrafilter ℕ) (q : ℕ → ℕ+) :
    MeasurableSpace ((U : Filter ℕ).Product (fun n => ZMod (q n : ℕ))) := loebMeasurableSpace U

theorem loeb_ae_periods_have_natural_mask
    (U : Ultrafilter ℕ) (hU : (U : Filter ℕ) ≤ atTop) (q : ℕ → ℕ+)
    (S : Set ((U : Filter ℕ).Product (fun n => ZMod (q n : ℕ)))) (hSm : MeasurableSet S)
    (H : AddSubgroup ((U : Filter ℕ).Product (fun n => ZMod (q n : ℕ))))
    (hHm : MeasurableSet (H : Set ((U : Filter ℕ).Product (fun n => ZMod (q n : ℕ)))))
    (hHpos : 0 < loebMeasure U hU (H : Set ((U : Filter ℕ).Product (fun n => ZMod (q n : ℕ)))))
    (hperiod : ∀ t ∈ H, t +ᵥ S =ᵐ[loebMeasure U hU] S) :
    ∃ (h : ℕ+) (R : Finset (ZMod (h : ℕ))), (∀ᶠ n in U, (h : ℕ) ∣ (q n : ℕ)) ∧
      S =ᵐ[loebMeasure U hU]
        (finiteQuotient U (fun n => naturalCyclicProjection (q n) h)) ⁻¹' (R : Set _) := by
  classical
  let G := (U : Filter ℕ).Product (fun n => ZMod (q n : ℕ))
  let μ : Measure G := loebMeasure (X := fun n => ZMod (q n : ℕ)) U hU
  obtain ⟨h, p, hp, hker, hmass⟩ :=
    positive_measurable_subgroup_is_natural_finite_kernel U hU q H hHm hHpos
  have hd : ∀ᶠ n in U, (h : ℕ) ∣ (q n : ℕ) := by
    filter_upwards [hp] with n hn
    have ht := hn.2 (q n : ℕ)
    rw [ZMod.natCast_self, map_zero] at ht
    exact (ZMod.natCast_eq_zero_iff (q n : ℕ) (h : ℕ)).mp ht.symm
  have heq := finiteQuotient_eq_of_eventually_natural U q h p
    (fun n => naturalCyclicProjection (q n) h) (hp.mono fun n hn => hn.2)
    (hd.mono fun n hn t => naturalCyclicProjection_natCast (q n) h hn t)
  rw [heq] at hker
  let φ := finiteQuotient U (fun n => naturalCyclicProjection (q n) h)
  let f := loebResidueProfile U hU q h S
  have hf : ∀ r, f r = 0 ∨ f r = 1 := by
    intro r
    obtain ⟨a, ha⟩ := finiteQuotient_surjective_of_eventually U
      (fun n => naturalCyclicProjection (q n) h)
      (hd.mono fun n hn => naturalCyclicProjection_surjective (q n) h hn) r
    change φ a = r at ha
    have hcoset : φ ⁻¹' {r} = a +ᵥ (H : Set G) := by
      rw [← ha, addHom_fiber_eq_coset, hker]
    have hs := loeb_section_zero_or_full_of_ae_periods U hU q S hSm H hHm hperiod a
    rw [← hcoset] at hs
    rcases hs with hz | ho
    · left
      change ((h : ℕ) : ℝ) * (μ (S ∩ φ ⁻¹' {r})).toReal = 0
      rw [hz, ENNReal.toReal_zero, mul_zero]
    · right
      change ((h : ℕ) : ℝ) * (μ (S ∩ φ ⁻¹' {r})).toReal = 1
      rw [ho, hmass, ENNReal.toReal_div, ENNReal.toReal_one, ENNReal.toReal_natCast]
      have hh : ((h : ℕ) : ℝ) ≠ 0 := by exact_mod_cast h.ne_zero
      field_simp
  let R := Finset.univ.filter (fun r => f r = 1)
  have hindicator : ∀ r, loebResidueProfile U hU q h S (r - 0) = if r ∈ R then (1 : ℝ) else 0 := by
    intro r
    simp only [sub_zero]
    change f r = if r ∈ R then (1 : ℝ) else 0
    have hmem : r ∈ R ↔ f r = 1 := by simp only [R, Finset.mem_filter, Finset.mem_univ, true_and]
    by_cases hr : f r = 1
    · rw [if_pos (hmem.mpr hr)]
      exact hr
    · rw [if_neg (fun hm => hr (hmem.mp hm))]
      exact (hf r).resolve_right hr
  obtain hmodel := loeb_ae_eq_shifted_mask_of_full_profile U hU q h hd S hSm R 0 hindicator
  have himage : R.image (fun r : ZMod (h : ℕ) => r - 0) = R := by ext r; simp
  refine ⟨h, R, hd, ?_⟩
  simpa only [himage] using hmodel

end Erdos335.Loeb

end
