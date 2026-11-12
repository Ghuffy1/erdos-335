import Erdos335.QuasiPeriodicRestriction
import Erdos335.LoebQuasiPeriodicBackground
import Erdos335.LoebNullExtensionBackground

/-!
# Full-measure restrictions of measurable quasi-periodic pairs

When both restricted active pieces are nonempty, the original period and
the active-sum identity pass to the restriction. Equality of the sumsets
almost everywhere supplies the active-sum measure identity.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Filter Set Topology MeasureTheory
open scoped Pointwise ENNReal

noncomputable section

namespace Erdos335.Loeb

local instance quasiPeriodicRestrictionLoebSpace (U : Ultrafilter ℕ) (q : ℕ → ℕ+) :
    MeasurableSpace ((U : Filter ℕ).Product (fun n => ZMod (q n : ℕ))) := loebMeasurableSpace U

theorem loeb_quasiPeriodic_background_positive
    (U : Ultrafilter ℕ) (hU : (U : Filter ℕ) ≤ atTop) (q : ℕ → ℕ+)
    (H : AddSubgroup ((U : Filter ℕ).Product (fun n => ZMod (q n : ℕ))))
    (A : Set ((U : Filter ℕ).Product (fun n => ZMod (q n : ℕ))))
    (p : QuasiPeriodicDecomposition (loebMeasure U hU) H A)
    (hHpos : 0 < loebMeasure (X := fun n => ZMod (q n : ℕ)) U hU (H : Set _))
    (hne : p.background.Nonempty) :
    0 < loebMeasure U hU p.background := by
  obtain ⟨x, hx⟩ := hne
  have hsection := loeb_measure_section_eq_of_essential_period U hU H p.background
    p.background_measurable p.background_periodic x hx
  exact (hHpos.trans_le (hsection.symm.le.trans (measure_mono inter_subset_left)))

theorem loeb_quasiPeriodic_full_restriction
    (U : Ultrafilter ℕ) (hU : (U : Filter ℕ) ≤ atTop) (q : ℕ → ℕ+)
    (A B C D : Set ((U : Filter ℕ).Product (fun n => ZMod (q n : ℕ))))
    (p : QuasiPeriodicPairData (loebMeasure U hU) (internalInnerMeasure U hU) A B)
    (hCm : MeasurableSet C) (hDm : MeasurableSet D)
    (hCA : C ⊆ A) (hDB : D ⊆ B)
    (hCeq : C =ᵐ[loebMeasure U hU] A) (hDeq : D =ᵐ[loebMeasure U hU] B)
    (hABm : MeasurableSet (A + B)) (hCDm : MeasurableSet (C + D))
    (hSumeq : C + D =ᵐ[loebMeasure U hU] A + B)
    (hleft : (p.left.active ∩ C).Nonempty) (hright : (p.right.active ∩ D).Nonempty) :
    ∃ r : QuasiPeriodicPairData (loebMeasure U hU) (internalInnerMeasure U hU) C D,
      r.period = p.period ∧
      r.left.active = p.left.active ∩ C ∧
      r.right.active = p.right.active ∩ D := by
  classical
  let G := (U : Filter ℕ).Product (fun n => ZMod (q n : ℕ))
  let μ := loebMeasure (X := fun n => ZMod (q n : ℕ)) U hU
  have hAnull : μ (A \ C) = 0 := ae_le_set.mp hCeq.ge
  have hBnull : μ (B \ D) = 0 := ae_le_set.mp hDeq.ge
  let left := p.left.restrict C hCA hCm hAnull hleft
  let right := p.right.restrict D hDB hDm hBnull hright
  have hleftAE : p.left.active ∩ C =ᵐ[μ] p.left.active := by
    filter_upwards [hCeq] with x hx
    change (x ∈ p.left.active ∧ x ∈ C) = (x ∈ p.left.active)
    rw [hx]
    exact propext ⟨And.left, fun ha => ⟨ha, (subset_union_right.trans p.left.partition.ge) ha⟩⟩
  have hrightAE : p.right.active ∩ D =ᵐ[μ] p.right.active := by
    filter_upwards [hDeq] with x hx
    change (x ∈ p.right.active ∧ x ∈ D) = (x ∈ p.right.active)
    rw [hx]
    exact propext ⟨And.left, fun hb => ⟨hb, (subset_union_right.trans p.right.partition.ge) hb⟩⟩
  have hbackground : left.background.Nonempty ∨ right.background.Nonempty := by
    rcases p.nonempty_background with hleftbg | hrightbg
    · left
      have hbgAE : p.left.background ∩ C =ᵐ[μ] p.left.background := by
        filter_upwards [hCeq] with x hx
        change (x ∈ p.left.background ∧ x ∈ C) = (x ∈ p.left.background)
        rw [hx]
        exact propext ⟨And.left, fun ha => ⟨ha, (subset_union_left.trans p.left.partition.ge) ha⟩⟩
      have hpos := loeb_quasiPeriodic_background_positive U hU q p.period A p.left
        p.period_positive hleftbg
      have hpos' : 0 < μ (p.left.background ∩ C) := by rwa [measure_congr hbgAE]
      exact nonempty_of_measure_ne_zero hpos'.ne'
    · right
      have hbgAE : p.right.background ∩ D =ᵐ[μ] p.right.background := by
        filter_upwards [hDeq] with x hx
        change (x ∈ p.right.background ∧ x ∈ D) = (x ∈ p.right.background)
        rw [hx]
        exact propext ⟨And.left, fun hb => ⟨hb, (subset_union_left.trans p.right.partition.ge) hb⟩⟩
      have hpos := loeb_quasiPeriodic_background_positive U hU q p.period B p.right
        p.period_positive hrightbg
      have hpos' : 0 < μ (p.right.background ∩ D) := by rwa [measure_congr hbgAE]
      exact nonempty_of_measure_ne_zero hpos'.ne'
  let L := (p.left.anchor + p.right.anchor) +ᵥ (p.period : Set G)
  have hLm : MeasurableSet L := measurable_loeb_translate U hU _ p.period_measurable _
  have hactiveSet : (p.left.active ∩ C) + (p.right.active ∩ D) = (C + D) ∩ L := by
    apply subset_antisymm
    · rintro z ⟨a, ha, b, hb, rfl⟩
      exact ⟨Set.add_mem_add ha.2 hb.2, (p.active_sum_eq_inter ▸ Set.add_mem_add ha.1 hb.1).2⟩
    · rintro z ⟨⟨a, ha, b, hb, rfl⟩, hz⟩
      obtain ⟨hacoset, hbcoset⟩ := p.unique_expression a (hCA ha) b (hDB hb) hz
      apply Set.add_mem_add
      · refine ⟨?_, ha⟩
        rw [p.left.active_eq_inter_coset]
        exact ⟨hCA ha, hacoset⟩
      · refine ⟨?_, hb⟩
        rw [p.right.active_eq_inter_coset]
        exact ⟨hDB hb, hbcoset⟩
  have hactiveAE : (p.left.active ∩ C) + (p.right.active ∩ D) =ᵐ[μ]
      p.left.active + p.right.active := by
    rw [hactiveSet, p.active_sum_eq_inter]
    filter_upwards [hSumeq] with x hx
    change (x ∈ C + D ∧ x ∈ L) = (x ∈ A + B ∧ x ∈ L)
    rw [hx]
  have hnewm : MeasurableSet ((p.left.active ∩ C) + (p.right.active ∩ D)) := by
    rw [hactiveSet]
    exact hCDm.inter hLm
  have holdm : MeasurableSet (p.left.active + p.right.active) := by
    rw [p.active_sum_eq_inter]
    exact hABm.inter hLm
  let r : QuasiPeriodicPairData μ (internalInnerMeasure U hU) C D := {
    period := p.period
    period_measurable := p.period_measurable
    period_positive := p.period_positive
    left := left
    right := right
    nonempty_background := hbackground
    unique_expression := by
      intro x hx y hy hxy
      exact p.unique_expression x (hCA hx) y (hDB hy) hxy
    active_identity := by
      change internalInnerMeasure U hU ((p.left.active ∩ C) + (p.right.active ∩ D)) =
        μ (p.left.active ∩ C) + μ (p.right.active ∩ D)
      rw [internalInnerMeasure_eq U hU _ hnewm, measure_congr hactiveAE,
        ← internalInnerMeasure_eq U hU _ holdm, p.active_identity,
        measure_congr hleftAE, measure_congr hrightAE]
  }
  exact ⟨r, rfl, rfl, rfl⟩

end Erdos335.Loeb

end
