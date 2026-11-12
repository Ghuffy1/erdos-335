import Erdos335.QuasiPeriodicSets
import Erdos335.LoebOnePeriodicSummand

/-!
# The periodic part of a quasi-periodic sum

The background sum is essentially periodic. Filling the one active
output coset in measure therefore makes the whole sum essentially
periodic.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Filter Set Topology MeasureTheory
open scoped Pointwise ENNReal

noncomputable section

namespace Erdos335.Loeb

local instance quasiPeriodicBackgroundLoebSpace (U : Ultrafilter ℕ) (q : ℕ → ℕ+) :
    MeasurableSpace ((U : Filter ℕ).Product (fun n => ZMod (q n : ℕ))) := loebMeasurableSpace U

theorem loeb_quasiPeriodic_decomposition_solid
    (U : Ultrafilter ℕ) (hU : (U : Filter ℕ) ≤ atTop) (q : ℕ → ℕ+)
    (H : AddSubgroup ((U : Filter ℕ).Product (fun n => ZMod (q n : ℕ))))
    (A : Set ((U : Filter ℕ).Product (fun n => ZMod (q n : ℕ))))
    (p : QuasiPeriodicDecomposition (loebMeasure U hU) H A)
    (hHpos : 0 < loebMeasure (X := fun n => ZMod (q n : ℕ)) U hU (H : Set _))
    (hactive : 0 < loebMeasure U hU p.active) :
    ∀ a ∈ A, 0 < loebMeasure U hU (A ∩ (a +ᵥ (H : Set _))) := by
  intro x hx
  have hx' := hx
  rw [p.partition] at hx'
  rcases hx' with hxbackground | hxactive
  · have hmass := loeb_measure_section_eq_of_essential_period U hU H p.background
      p.background_measurable p.background_periodic x hxbackground
    have hsub : p.background ∩ (x +ᵥ (H : Set _)) ⊆ A ∩ (x +ᵥ (H : Set _)) :=
      inter_subset_inter_left _ (subset_union_left.trans p.partition.ge)
    have hpos := hHpos
    rw [← hmass] at hpos
    simpa using hpos.trans_le (measure_mono hsub)
  · have hsub : p.active ⊆ A ∩ (x +ᵥ (H : Set _)) := by
      obtain ⟨l, hl, hlx⟩ := p.active_subset_coset hxactive
      intro a ha
      refine ⟨(subset_union_right.trans p.partition.ge) ha, ?_⟩
      obtain ⟨k, hk, hka⟩ := p.active_subset_coset ha
      refine ⟨k - l, H.sub_mem hk hl, ?_⟩
      change p.anchor + l = x at hlx
      change p.anchor + k = a at hka
      change x + (k - l) = a
      rw [← hlx, ← hka]
      abel
    simpa using hactive.trans_le (measure_mono hsub)

theorem loeb_quasiPeriodic_background
    (U : Ultrafilter ℕ) (hU : (U : Filter ℕ) ≤ atTop) (q : ℕ → ℕ+)
    (A B : Set ((U : Filter ℕ).Product (fun n => ZMod (q n : ℕ))))
    (inner : Set ((U : Filter ℕ).Product (fun n => ZMod (q n : ℕ))) → ℝ≥0∞)
    (p : QuasiPeriodicPairData (loebMeasure U hU) inner A B) :
    MeasurableSet ((p.left.background + B) ∪ (A + p.right.background)) ∧
      ((p.left.background + B) ∪ (A + p.right.background)) + (p.period : Set _) =ᵐ[loebMeasure U hU]
        (p.left.background + B) ∪ (A + p.right.background) := by
  obtain ⟨hleftm, hleftp⟩ := loeb_sum_with_essentially_periodic_summand U hU q p.period
    p.period_measurable p.period_positive B p.left.background p.left.background_periodic
  have hleftm' : MeasurableSet (p.left.background + B) := by simpa only [add_comm] using hleftm
  have hleftp' : (p.left.background + B) + (p.period : Set _) =ᵐ[loebMeasure U hU]
      p.left.background + B := by simpa only [add_comm B p.left.background] using hleftp
  obtain ⟨hrightm, hrightp⟩ := loeb_sum_with_essentially_periodic_summand U hU q p.period
    p.period_measurable p.period_positive A p.right.background p.right.background_periodic
  refine ⟨hleftm'.union hrightm, ?_⟩
  rw [union_add]
  filter_upwards [hleftp', hrightp] with x hx hy
  change ((x ∈ (p.left.background + B) + (p.period : Set _)) ∨
      x ∈ (A + p.right.background) + (p.period : Set _)) =
    (x ∈ p.left.background + B ∨ x ∈ A + p.right.background)
  rw [hx, hy]

theorem loeb_quasiPeriodic_essential_period_of_full_coset
    (U : Ultrafilter ℕ) (hU : (U : Filter ℕ) ≤ atTop) (q : ℕ → ℕ+)
    (A B : Set ((U : Filter ℕ).Product (fun n => ZMod (q n : ℕ))))
    (inner : Set ((U : Filter ℕ).Product (fun n => ZMod (q n : ℕ))) → ℝ≥0∞)
    (p : QuasiPeriodicPairData (loebMeasure U hU) inner A B)
    (hcoset : (p.left.anchor + p.right.anchor) +ᵥ (p.period : Set _) ≤ᵐ[loebMeasure U hU] A + B) :
    (A + B) + (p.period : Set _) =ᵐ[loebMeasure U hU] A + B := by
  let G := (U : Filter ℕ).Product (fun n => ZMod (q n : ℕ))
  let background := (p.left.background + B) ∪ (A + p.right.background)
  let active := p.left.active + p.right.active
  have hsplit : A + B = background ∪ active := p.sum_partition
  have hbackgroundSub : background ⊆ A + B := by rw [hsplit]; exact subset_union_left
  have hbackgroundPeriod := (loeb_quasiPeriodic_background U hU q A B inner p).2
  have hactiveSub : active + (p.period : Set G) ⊆
      (p.left.anchor + p.right.anchor) +ᵥ (p.period : Set G) := by
    rintro z ⟨x, ⟨a, ha, b, hb, rfl⟩, k, hk, rfl⟩
    obtain ⟨l, hl, hla⟩ := p.left.active_subset_coset ha
    obtain ⟨m, hm, hmb⟩ := p.right.active_subset_coset hb
    refine ⟨l + m + k, p.period.add_mem (p.period.add_mem hl hm) hk, ?_⟩
    change p.left.anchor + l = a at hla
    change p.right.anchor + m = b at hmb
    change (p.left.anchor + p.right.anchor) + (l + m + k) = (a + b) + k
    rw [← hla, ← hmb]
    abel
  have hbackgroundAE : background + (p.period : Set G) ≤ᵐ[loebMeasure U hU] A + B :=
    hbackgroundPeriod.le.trans hbackgroundSub.eventuallySubset
  have hactiveAE : active + (p.period : Set G) ≤ᵐ[loebMeasure U hU] A + B :=
    hactiveSub.eventuallySubset.trans hcoset
  have hsaturated : (A + B) + (p.period : Set G) =
      (background + (p.period : Set G)) ∪ (active + (p.period : Set G)) := by rw [hsplit, union_add]
  have hforward : (A + B) + (p.period : Set G) ≤ᵐ[loebMeasure U hU] A + B := by
    rw [hsaturated]
    filter_upwards [hbackgroundAE, hactiveAE] with x hx hy
    change (x ∈ (background + (p.period : Set G)) ∨ x ∈ (active + (p.period : Set G))) → x ∈ A + B
    intro h
    exact h.elim hx hy
  have hback : A + B ⊆ (A + B) + (p.period : Set G) :=
    fun x hx => ⟨x, hx, 0, p.period.zero_mem, add_zero x⟩
  exact hforward.antisymm hback.eventuallySubset

end Erdos335.Loeb

end
