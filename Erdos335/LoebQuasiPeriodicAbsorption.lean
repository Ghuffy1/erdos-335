import Erdos335.LoebQuasiPeriodicBackground
import Erdos335.LoebNonextendible

/-!
# Absorbing translates outside the active coset

A translate that meets the active output coset through a background
point would fill that coset in measure. Failure of essential periodicity
excludes this. Solidity then absorbs the saturated translate, and
nonextendibility puts the corresponding input coset in the original
input up to a null set.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Filter Set Topology MeasureTheory
open scoped Pointwise ENNReal

noncomputable section

namespace Erdos335.Loeb

theorem QuasiPeriodicPairData.active_sum_subset_coset
    {G : Type*} [AddCommGroup G] [MeasurableSpace G]
    {μ : Measure G} {inner : Set G → ℝ≥0∞} {A B : Set G}
    (p : QuasiPeriodicPairData μ inner A B) :
    p.left.active + p.right.active ⊆ (p.left.anchor + p.right.anchor) +ᵥ (p.period : Set G) := by
  rintro x ⟨a, ha, b, hb, rfl⟩
  obtain ⟨k, hk, hka⟩ := p.left.active_subset_coset ha
  obtain ⟨l, hl, hlb⟩ := p.right.active_subset_coset hb
  refine ⟨k + l, p.period.add_mem hk hl, ?_⟩
  change p.left.anchor + k = a at hka
  change p.right.anchor + l = b at hlb
  change (p.left.anchor + p.right.anchor) + (k + l) = a + b
  rw [← hka, ← hlb]
  abel

local instance quasiPeriodicAbsorptionLoebSpace (U : Ultrafilter ℕ) (q : ℕ → ℕ+) :
    MeasurableSpace ((U : Filter ℕ).Product (fun n => ZMod (q n : ℕ))) := loebMeasurableSpace U

theorem loeb_quasiPeriodic_translate_avoids_active_coset
    (U : Ultrafilter ℕ) (hU : (U : Filter ℕ) ≤ atTop) (q : ℕ → ℕ+)
    (A B : Set ((U : Filter ℕ).Product (fun n => ZMod (q n : ℕ))))
    (inner : Set ((U : Filter ℕ).Product (fun n => ZMod (q n : ℕ))) → ℝ≥0∞)
    (p : QuasiPeriodicPairData (loebMeasure U hU) inner A B)
    (g : (U : Filter ℕ).Product (fun n => ZMod (q n : ℕ)))
    (hg : g ∉ p.left.anchor +ᵥ (p.period : Set ((U : Filter ℕ).Product (fun n => ZMod (q n : ℕ)))))
    (hnotperiod : ¬ (A + B) + (p.period : Set _) =ᵐ[loebMeasure U hU] A + B)
    (hnull : loebMeasure U hU ((g +ᵥ B) \ (A + B)) = 0) :
    Disjoint (g +ᵥ B) ((p.left.anchor + p.right.anchor) +ᵥ (p.period : Set _)) := by
  let G := (U : Filter ℕ).Product (fun n => ZMod (q n : ℕ))
  let μ := loebMeasure (X := fun n => ZMod (q n : ℕ)) U hU
  apply Set.disjoint_left.mpr
  rintro z ⟨b, hb, hgb⟩ ⟨k, hk, hkz⟩
  have hsum : g + b = (p.left.anchor + p.right.anchor) + k := hgb.trans hkz.symm
  have hb' := hb
  rw [p.right.partition] at hb'
  rcases hb' with hbbackground | hbactive
  · have hcover : b +ᵥ (p.period : Set G) ⊆ p.right.background + (p.period : Set G) := by
      rintro x ⟨l, hl, hlx⟩
      exact ⟨b, hbbackground, l, hl, hlx⟩
    have hzero : μ ((b +ᵥ (p.period : Set G)) \ p.right.background) = 0 :=
      measure_mono_null (sdiff_subset_sdiff_left hcover) p.right.background_periodic
    have htranslated : μ ((g +ᵥ (b +ᵥ (p.period : Set G))) \ (g +ᵥ p.right.background)) = 0 := by
      rw [← vadd_set_sdiff]
      change μ ((fun x => g + x) '' ((b +ᵥ (p.period : Set G)) \ p.right.background)) = 0
      rw [loebMeasure_image_add_left]
      exact hzero
    have hcosetEq : g +ᵥ (b +ᵥ (p.period : Set G)) =
        (p.left.anchor + p.right.anchor) +ᵥ (p.period : Set G) := by
      apply subset_antisymm
      · rintro x ⟨y, ⟨l, hl, rfl⟩, rfl⟩
        refine ⟨k + l, p.period.add_mem hk hl, ?_⟩
        change (p.left.anchor + p.right.anchor) + (k + l) = g + (b + l)
        rw [← add_assoc, ← hsum]
        abel
      · rintro x ⟨l, hl, rfl⟩
        refine ⟨b + (l - k), ⟨l - k, p.period.sub_mem hl hk, rfl⟩, ?_⟩
        change g + (b + (l - k)) = (p.left.anchor + p.right.anchor) + l
        calc
          _ = (g + b) + (l - k) := by abel
          _ = _ := by rw [hsum]; abel
    rw [hcosetEq] at htranslated
    have hbgsub : g +ᵥ p.right.background ⊆ g +ᵥ B := by
      rintro x ⟨y, hy, rfl⟩
      exact ⟨y, (subset_union_left.trans p.right.partition.ge) hy, rfl⟩
    have hfull : (p.left.anchor + p.right.anchor) +ᵥ (p.period : Set G) ≤ᵐ[μ] A + B :=
      (ae_le_set.mpr htranslated).trans (hbgsub.eventuallySubset.trans (ae_le_set.mpr hnull))
    exact hnotperiod (loeb_quasiPeriodic_essential_period_of_full_coset U hU q A B inner p hfull)
  · obtain ⟨l, hl, hlb⟩ := p.right.active_subset_coset hbactive
    apply hg
    refine ⟨k - l, p.period.sub_mem hk hl, ?_⟩
    change p.right.anchor + l = b at hlb
    change p.left.anchor + (k - l) = g
    have heq : g + (p.right.anchor + l) = (p.left.anchor + p.right.anchor) + k := by rwa [hlb]
    calc
      _ = ((p.left.anchor + p.right.anchor) + k) - (p.right.anchor + l) := by abel
      _ = (g + (p.right.anchor + l)) - (p.right.anchor + l) := by rw [heq]
      _ = g := by simp

theorem loeb_quasiPeriodic_translate_saturated_subset
    (U : Ultrafilter ℕ) (hU : (U : Filter ℕ) ≤ atTop) (q : ℕ → ℕ+)
    (A B : Set ((U : Filter ℕ).Product (fun n => ZMod (q n : ℕ))))
    (inner : Set ((U : Filter ℕ).Product (fun n => ZMod (q n : ℕ))) → ℝ≥0∞)
    (p : QuasiPeriodicPairData (loebMeasure U hU) inner A B)
    (g : (U : Filter ℕ).Product (fun n => ZMod (q n : ℕ)))
    (hg : g ∉ p.left.anchor +ᵥ (p.period : Set ((U : Filter ℕ).Product (fun n => ZMod (q n : ℕ)))))
    (hBactive : 0 < loebMeasure U hU p.right.active)
    (hnotperiod : ¬ (A + B) + (p.period : Set _) =ᵐ[loebMeasure U hU] A + B)
    (hnull : loebMeasure U hU ((g +ᵥ B) \ (A + B)) = 0) :
    (g +ᵥ (p.period : Set _)) + B ≤ᵐ[loebMeasure U hU] A + B := by
  let G := (U : Filter ℕ).Product (fun n => ZMod (q n : ℕ))
  let μ := loebMeasure (X := fun n => ZMod (q n : ℕ)) U hU
  let background := (p.left.background + B) ∪ (A + p.right.background)
  let T := background + (p.period : Set G)
  have havoid := loeb_quasiPeriodic_translate_avoids_active_coset U hU q A B inner p g hg hnotperiod hnull
  have hbgSub : background ⊆ A + B := by rw [p.sum_partition]; exact subset_union_left
  have hintoBg : g +ᵥ B ≤ᵐ[μ] background := by
    filter_upwards [ae_le_set.mpr hnull] with x hx
    intro hxg
    have hxsum := hx hxg
    rw [p.sum_partition] at hxsum
    rcases hxsum with hxbg | hxactive
    · exact hxbg
    · exact False.elim (Set.disjoint_left.mp havoid hxg (p.active_sum_subset_coset hxactive))
  have hbgT : background ⊆ T := fun x hx => ⟨x, hx, 0, p.period.zero_mem, add_zero x⟩
  have hintoT : g +ᵥ B ≤ᵐ[μ] T := hintoBg.trans hbgT.eventuallySubset
  have hTperiod : T + (p.period : Set G) = T := by dsimp only [T]; rw [add_assoc, coe_add_coe]
  have hsolid : ∀ b ∈ B, 0 < μ (B ∩ (b +ᵥ (p.period : Set G))) := by
    simpa using loeb_quasiPeriodic_decomposition_solid U hU q p.period B p.right p.period_positive hBactive
  have hfill := loeb_solid_translate_absorption U hU p.period B T g hTperiod hsolid (ae_le_set.mp hintoT)
  have hsub : (g +ᵥ (p.period : Set G)) + B ⊆ T := by
    rintro x ⟨y, ⟨k, hk, hky⟩, b, hb, rfl⟩
    apply hfill
    refine ⟨b + k, ⟨b, hb, k, hk, rfl⟩, ?_⟩
    change g + k = y at hky
    change g + (b + k) = y + b
    rw [← hky]
    abel
  have hTbg := (loeb_quasiPeriodic_background U hU q A B inner p).2
  exact hsub.eventuallySubset.trans (hTbg.le.trans hbgSub.eventuallySubset)

theorem loeb_nonextendible_quasiPeriodic_translate
    (U : Ultrafilter ℕ) (hU : (U : Filter ℕ) ≤ atTop) (q : ℕ → ℕ+)
    (A B : Set ((U : Filter ℕ).Product (fun n => ZMod (q n : ℕ))))
    (p : QuasiPeriodicPairData (loebMeasure U hU) (internalInnerMeasure U hU) A B)
    (g : (U : Filter ℕ).Product (fun n => ZMod (q n : ℕ)))
    (hg : g ∉ p.left.anchor +ᵥ (p.period : Set ((U : Filter ℕ).Product (fun n => ZMod (q n : ℕ)))))
    (hBactive : 0 < loebMeasure U hU p.right.active)
    (hne : MeasureNonextendible (loebMeasure U hU) (internalInnerMeasure U hU) A B)
    (hnotperiod : ¬ (A + B) + (p.period : Set _) =ᵐ[loebMeasure U hU] A + B)
    (hnull : loebMeasure U hU ((g +ᵥ B) \ (A + B)) = 0) :
    loebMeasure U hU ((g +ᵥ (p.period : Set _)) \ A) = 0 := by
  have hAm : MeasurableSet A := p.left.partition.symm ▸
    (p.left.background_measurable.union p.left.active_measurable)
  have hBm : MeasurableSet B := p.right.partition.symm ▸
    (p.right.background_measurable.union p.right.active_measurable)
  exact loeb_nonextendible_absorbed_coset U hU p.period A B g p.period_measurable hAm hBm hne
    (loeb_quasiPeriodic_translate_saturated_subset U hU q A B (internalInnerMeasure U hU) p g hg hBactive hnotperiod hnull)

end Erdos335.Loeb

end
