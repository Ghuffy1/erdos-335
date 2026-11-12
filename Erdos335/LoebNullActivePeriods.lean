import Erdos335.LoebQuasiPeriodicSaturation

/-!
# Difference periods supplied by a null exceptional summand
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Filter Set MeasureTheory
open scoped Pointwise ENNReal

noncomputable section

namespace Erdos335.Loeb

local instance nullActivePeriodsLoebSpace (U : Ultrafilter ℕ) (q : ℕ → ℕ+) :
    MeasurableSpace ((U : Filter ℕ).Product (fun n => ZMod (q n : ℕ))) := loebMeasurableSpace U

theorem loeb_equal_translate_difference_period
    (U : Ultrafilter ℕ) (hU : (U : Filter ℕ) ≤ atTop) (q : ℕ → ℕ+)
    (A S : Set ((U : Filter ℕ).Product (fun n => ZMod (q n : ℕ))))
    (x y : (U : Filter ℕ).Product (fun n => ZMod (q n : ℕ)))
    (hx : x +ᵥ A =ᵐ[loebMeasure U hU] S)
    (hy : y +ᵥ A =ᵐ[loebMeasure U hU] S) :
    (x - y) +ᵥ A =ᵐ[loebMeasure U hU] A := by
  have ht := loeb_vadd_congr_ae U hU _ _ (-y) (hx.trans hy.symm)
  rw [vadd_vadd, vadd_vadd, neg_add_cancel, zero_vadd] at ht
  simpa only [sub_eq_add_neg, add_comm] using ht

theorem loeb_quasiPeriodic_period_of_active_period
    (U : Ultrafilter ℕ) (hU : (U : Filter ℕ) ≤ atTop) (q : ℕ → ℕ+)
    (A : Set ((U : Filter ℕ).Product (fun n => ZMod (q n : ℕ))))
    (H : AddSubgroup ((U : Filter ℕ).Product (fun n => ZMod (q n : ℕ))))
    (p : QuasiPeriodicDecomposition (loebMeasure U hU) H A)
    (t : (U : Filter ℕ).Product (fun n => ZMod (q n : ℕ))) (ht : t ∈ H)
    (hactive : t +ᵥ p.active =ᵐ[loebMeasure U hU] p.active) :
    t +ᵥ A =ᵐ[loebMeasure U hU] A := by
  have hbackground := loeb_translate_ae_of_essential_period U hU q p.background
    p.background_measurable H p.background_periodic t ht
  rw [p.partition, vadd_set_union]
  filter_upwards [hbackground, hactive] with x hx hy
  change (x ∈ t +ᵥ p.background ∨ x ∈ t +ᵥ p.active) =
    (x ∈ p.background ∨ x ∈ p.active)
  rw [hx, hy]

theorem loeb_null_right_active_difference_periods
    (U : Ultrafilter ℕ) (hU : (U : Filter ℕ) ≤ atTop) (q : ℕ → ℕ+)
    (A B : Set ((U : Filter ℕ).Product (fun n => ZMod (q n : ℕ))))
    (p : QuasiPeriodicPairData (loebMeasure U hU) (internalInnerMeasure U hU) A B)
    (hSm : MeasurableSet (A + B))
    (hzero : loebMeasure U hU p.right.active = 0)
    (x y : (U : Filter ℕ).Product (fun n => ZMod (q n : ℕ)))
    (hx : x ∈ p.right.active) (hy : y ∈ p.right.active) :
    (x - y) +ᵥ A =ᵐ[loebMeasure U hU] A ∧
      (x - y) +ᵥ (A + B) =ᵐ[loebMeasure U hU] A + B := by
  let G := (U : Filter ℕ).Product (fun n => ZMod (q n : ℕ))
  let μ : Measure G := loebMeasure (X := fun n => ZMod (q n : ℕ)) U hU
  have : IsProbabilityMeasure μ := isProbabilityMeasure_loebMeasure U hU
  let C := p.left.active + p.right.active
  have hCm : MeasurableSet C := by
    change MeasurableSet (p.left.active + p.right.active)
    rw [p.active_sum_eq_inter]
    exact hSm.inter (measurable_loeb_translate U hU _ p.period_measurable _)
  have hmass : μ C = μ p.left.active := by
    rw [← internalInnerMeasure_eq U hU C hCm, p.active_identity, hzero, add_zero]
  have translate_eq (z : G) (hz : z ∈ p.right.active) : z +ᵥ p.left.active =ᵐ[μ] C := by
    have hsub : z +ᵥ p.left.active ⊆ C := by
      rintro u ⟨a, ha, rfl⟩
      exact ⟨a, ha, z, hz, add_comm _ _⟩
    apply ae_eq_of_ae_subset_of_measure_ge hsub.eventuallySubset
    · exact hmass.le.trans_eq (loebMeasure_image_add_left U hU z p.left.active).symm
    · exact (measurable_loeb_translate U hU _ p.left.active_measurable z).nullMeasurableSet
    · exact measure_ne_top μ C
  have hactive := loeb_equal_translate_difference_period U hU q p.left.active C x y
    (translate_eq x hx) (translate_eq y hy)
  have hperiod : x - y ∈ p.period := by
    obtain ⟨k, hk, hkx⟩ := p.right.active_subset_coset hx
    obtain ⟨l, hl, hly⟩ := p.right.active_subset_coset hy
    change p.right.anchor + k = x at hkx
    change p.right.anchor + l = y at hly
    rw [← hkx, ← hly, add_sub_add_left_eq_sub]
    exact p.period.sub_mem hk hl
  have hCperiod : (x - y) +ᵥ C =ᵐ[μ] C := by
    have htranslated := loeb_vadd_congr_ae U hU _ _ (x - y) (translate_eq y hy).symm
    have hcomm : (x - y) +ᵥ (y +ᵥ p.left.active) = y +ᵥ ((x - y) +ᵥ p.left.active) := by
      rw [vadd_vadd, vadd_vadd, add_comm (x - y) y]
    rw [hcomm] at htranslated
    exact htranslated.trans ((loeb_vadd_congr_ae U hU _ _ y hactive).trans (translate_eq y hy))
  exact ⟨loeb_quasiPeriodic_period_of_active_period U hU q A p.period p.left (x - y) hperiod hactive,
    loeb_quasiPeriodic_period_of_active_period U hU q (A + B) p.period
      (loeb_quasiPeriodic_sum_decomposition U hU q A B p hSm) (x - y) hperiod hCperiod⟩

end Erdos335.Loeb

end
