import Erdos335.LoebBohrPeriodAlignment

/-!
# Exact saturation identities for a quasi-periodic equality pair
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter MeasureTheory
open scoped ENNReal Pointwise

noncomputable section

namespace Erdos335.Loeb

local instance quasiPeriodicSaturationLoebSpace (U : Ultrafilter ℕ) (q : ℕ → ℕ+) :
    MeasurableSpace ((U : Filter ℕ).Product (fun n => ZMod (q n : ℕ))) := loebMeasurableSpace U

theorem loeb_quasiPeriodic_saturation_identity
    (U : Ultrafilter ℕ) (hU : (U : Filter ℕ) ≤ atTop) (q : ℕ → ℕ+)
    (A : Set ((U : Filter ℕ).Product (fun n => ZMod (q n : ℕ))))
    (H : AddSubgroup ((U : Filter ℕ).Product (fun n => ZMod (q n : ℕ))))
    (hHm : MeasurableSet (H : Set ((U : Filter ℕ).Product (fun n => ZMod (q n : ℕ)))))
    (p : QuasiPeriodicDecomposition (loebMeasure U hU) H A) :
    loebMeasure U hU (A + (H : Set _)) + loebMeasure U hU p.active =
      loebMeasure U hU A + loebMeasure U hU
        (H : Set ((U : Filter ℕ).Product (fun n => ZMod (q n : ℕ)))) := by
  let G := (U : Filter ℕ).Product (fun n => ZMod (q n : ℕ))
  let μ := loebMeasure (X := fun n => ZMod (q n : ℕ)) U hU
  let T := p.anchor +ᵥ (H : Set G)
  have hTm : MeasurableSet T := measurable_loeb_translate U hU _ hHm _
  have hdisjoint : Disjoint p.background T := by
    simpa only [p.active_add_period] using p.separated.symm
  have hactiveDisjoint : Disjoint p.background p.active := hdisjoint.mono_right p.active_subset_coset
  have hback : p.background ⊆ p.background + (H : Set G) :=
    fun x hx => ⟨x, hx, 0, H.zero_mem, add_zero x⟩
  have hbg : p.background + (H : Set G) =ᵐ[μ] p.background :=
    (ae_le_set.mpr p.background_periodic).antisymm hback.eventuallySubset
  have hsplit : A + (H : Set G) = (p.background + (H : Set G)) ∪ T := by
    conv_lhs => rw [p.partition]
    rw [union_add, p.active_add_period]
  have hsat : μ (A + (H : Set G)) = μ p.background + μ (H : Set G) := by
    calc
      μ (A + (H : Set G)) = μ (p.background ∪ T) := by
        rw [hsplit]
        apply measure_congr
        filter_upwards [hbg] with x hx
        change (x ∈ p.background + (H : Set G) ∨ x ∈ T) = (x ∈ p.background ∨ x ∈ T)
        rw [hx]
      _ = μ p.background + μ T := measure_union hdisjoint hTm
      _ = _ := by rw [show μ T = μ (H : Set G) from loebMeasure_coset U hU H p.anchor]
  have hinput : μ A = μ p.background + μ p.active := by
    calc
      μ A = μ (p.background ∪ p.active) := congrArg μ p.partition
      _ = _ := measure_union hactiveDisjoint p.active_measurable
  change μ (A + (H : Set G)) + μ p.active = μ A + μ (H : Set G)
  rw [hsat, hinput]
  ac_rfl

def loeb_quasiPeriodic_sum_decomposition
    (U : Ultrafilter ℕ) (hU : (U : Filter ℕ) ≤ atTop) (q : ℕ → ℕ+)
    (A B : Set ((U : Filter ℕ).Product (fun n => ZMod (q n : ℕ))))
    (p : QuasiPeriodicPairData (loebMeasure U hU) (internalInnerMeasure U hU) A B)
    (hSm : MeasurableSet (A + B)) :
    QuasiPeriodicDecomposition (loebMeasure U hU) p.period (A + B) where
  active := p.left.active + p.right.active
  background := (p.left.background + B) ∪ (A + p.right.background)
  anchor := p.left.anchor + p.right.anchor
  active_measurable := by
    rw [p.active_sum_eq_inter]
    exact hSm.inter (measurable_loeb_translate U hU _ p.period_measurable _)
  background_measurable := (loeb_quasiPeriodic_background U hU q A B (internalInnerMeasure U hU) p).1
  active_nonempty := p.left.active_nonempty.add p.right.active_nonempty
  partition := p.sum_partition
  active_subset_coset := by
    rw [p.active_sum_eq_inter]
    exact inter_subset_right
  separated := by
    apply p.background_disjoint_active_coset.symm.mono_left
    rintro x ⟨y, hy, k, hk, rfl⟩
    rw [p.active_sum_eq_inter] at hy
    obtain ⟨l, hl, hly⟩ := hy.2
    refine ⟨l + k, p.period.add_mem hl hk, ?_⟩
    change (p.left.anchor + p.right.anchor) + l = y at hly
    change (p.left.anchor + p.right.anchor) + (l + k) = y + k
    rw [← hly]
    abel
  background_periodic := ae_le_set.mp
    (loeb_quasiPeriodic_background U hU q A B (internalInnerMeasure U hU) p).2.le

theorem loeb_quasiPeriodic_saturated_equality
    (U : Ultrafilter ℕ) (hU : (U : Filter ℕ) ≤ atTop) (q : ℕ → ℕ+)
    (A B : Set ((U : Filter ℕ).Product (fun n => ZMod (q n : ℕ))))
    (p : QuasiPeriodicPairData (loebMeasure U hU) (internalInnerMeasure U hU) A B)
    (hSm : MeasurableSet (A + B))
    (hfull : loebMeasure U hU (A + B) = loebMeasure U hU A + loebMeasure U hU B) :
    (loebMeasure U hU (A + (p.period : Set _))).toReal +
        (loebMeasure U hU (B + (p.period : Set _))).toReal =
      (loebMeasure U hU ((A + B) + (p.period : Set _))).toReal +
        (loebMeasure U hU
          (p.period : Set ((U : Filter ℕ).Product (fun n => ZMod (q n : ℕ))))).toReal := by
  let μ := loebMeasure (X := fun n => ZMod (q n : ℕ)) U hU
  have : IsProbabilityMeasure μ := isProbabilityMeasure_loebMeasure U hU
  let s := loeb_quasiPeriodic_sum_decomposition U hU q A B p hSm
  have hleft : μ (A + (p.period : Set _)) + μ p.left.active = μ A + μ (p.period : Set _) :=
    loeb_quasiPeriodic_saturation_identity U hU q A p.period p.period_measurable p.left
  have hright : μ (B + (p.period : Set _)) + μ p.right.active = μ B + μ (p.period : Set _) :=
    loeb_quasiPeriodic_saturation_identity U hU q B p.period p.period_measurable p.right
  have hsum : μ ((A + B) + (p.period : Set _)) + μ (p.left.active + p.right.active) =
      μ (A + B) + μ (p.period : Set _) :=
    loeb_quasiPeriodic_saturation_identity U hU q (A + B) p.period p.period_measurable s
  have hactiveMeasurable : MeasurableSet (p.left.active + p.right.active) := s.active_measurable
  have hactive : μ (p.left.active + p.right.active) = μ p.left.active + μ p.right.active := by
    rw [← internalInnerMeasure_eq U hU _ hactiveMeasurable]
    exact p.active_identity
  have hfull' : μ (A + B) = μ A + μ B := hfull
  have hplus : (μ (A + (p.period : Set _)) + μ (B + (p.period : Set _))) +
      μ (p.left.active + p.right.active) =
      (μ ((A + B) + (p.period : Set _)) + μ (p.period : Set _)) +
        μ (p.left.active + p.right.active) := by
    calc
      _ = (μ (A + (p.period : Set _)) + μ p.left.active) +
          (μ (B + (p.period : Set _)) + μ p.right.active) := by rw [hactive]; ac_rfl
      _ = (μ A + μ (p.period : Set _)) + (μ B + μ (p.period : Set _)) := by rw [hleft, hright]
      _ = (μ (A + B) + μ (p.period : Set _)) + μ (p.period : Set _) := by rw [hfull']; ac_rfl
      _ = (μ ((A + B) + (p.period : Set _)) + μ (p.left.active + p.right.active)) +
          μ (p.period : Set _) := by rw [hsum]
      _ = _ := by ac_rfl
  have heq := (ENNReal.add_left_inj (measure_ne_top μ (p.left.active + p.right.active))).mp hplus
  have hreal := congrArg ENNReal.toReal heq
  rw [ENNReal.toReal_add (measure_ne_top μ _) (measure_ne_top μ _),
    ENNReal.toReal_add (measure_ne_top μ _) (measure_ne_top μ _)] at hreal
  exact hreal

end Erdos335.Loeb

end
