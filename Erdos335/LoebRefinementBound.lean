import Erdos335.LoebRefinementPeriods

/-!
# Quantitative decrease under active-pair refinement

A proper measurable subgroup occupies at most half of its containing
subgroup. Refining the active pair therefore gives the measure decrease
used to iterate the Loeb inverse theorem.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Filter Set Topology MeasureTheory
open scoped Pointwise ENNReal

noncomputable section

namespace Erdos335.Loeb

local instance refinementBoundLoebSpace (U : Ultrafilter ℕ) (q : ℕ → ℕ+) :
    MeasurableSpace ((U : Filter ℕ).Product (fun n => ZMod (q n : ℕ))) := loebMeasurableSpace U

theorem loeb_proper_subgroup_measure_double_le
    (U : Ultrafilter ℕ) (hU : (U : Filter ℕ) ≤ atTop) (q : ℕ → ℕ+)
    (H K : AddSubgroup ((U : Filter ℕ).Product (fun n => ZMod (q n : ℕ))))
    (hKm : MeasurableSet (K : Set ((U : Filter ℕ).Product (fun n => ZMod (q n : ℕ)))))
    (hKH : K ≤ H) (hne : K ≠ H) :
    loebMeasure (X := fun n => ZMod (q n : ℕ)) U hU (K : Set _) +
      loebMeasure (X := fun n => ZMod (q n : ℕ)) U hU (K : Set _) ≤
        loebMeasure (X := fun n => ZMod (q n : ℕ)) U hU (H : Set _) := by
  classical
  let G := (U : Filter ℕ).Product (fun n => ZMod (q n : ℕ))
  let μ := loebMeasure (X := fun n => ZMod (q n : ℕ)) U hU
  obtain ⟨k, hkH, hkK⟩ : ∃ k, k ∈ H ∧ k ∉ K := by
    by_contra h
    push_neg at h
    exact hne (le_antisymm hKH h)
  have hd : Disjoint (K : Set G) (k +ᵥ (K : Set G)) := by
    apply Set.disjoint_left.mpr
    rintro x hx ⟨y, hy, heq⟩
    apply hkK
    have hdiff : k = x - y := by
      change k + y = x at heq
      rw [← heq]
      abel
    rw [hdiff]
    exact K.sub_mem hx hy
  have htm : MeasurableSet (k +ᵥ (K : Set G)) := measurable_loeb_translate U hU _ hKm k
  have hmass : μ (k +ᵥ (K : Set G)) = μ (K : Set G) := by
    change μ ((fun x => k + x) '' (K : Set G)) = μ (K : Set G)
    exact loebMeasure_image_add_left U hU k (K : Set G)
  have hsub : (K : Set G) ∪ (k +ᵥ (K : Set G)) ⊆ (H : Set G) := by
    rintro x (hx | ⟨y, hy, rfl⟩)
    · exact hKH hx
    · exact H.add_mem hkH (hKH hy)
  calc
    μ (K : Set G) + μ (K : Set G) = μ (K : Set G) + μ (k +ᵥ (K : Set G)) := by rw [hmass]
    _ = μ ((K : Set G) ∪ (k +ᵥ (K : Set G))) := (measure_union hd htm).symm
    _ ≤ μ (H : Set G) := measure_mono hsub

theorem loeb_quasiPeriodic_refinement
    (U : Ultrafilter ℕ) (hU : (U : Filter ℕ) ≤ atTop) (q : ℕ → ℕ+)
    (A B : Set ((U : Filter ℕ).Product (fun n => ZMod (q n : ℕ))))
    (p : QuasiPeriodicPairData (loebMeasure U hU) (internalInnerMeasure U hU) A B)
    (r : QuasiPeriodicPairData (loebMeasure U hU) (internalInnerMeasure U hU)
      p.left.active p.right.active) :
    ∃ s : QuasiPeriodicPairData (loebMeasure U hU) (internalInnerMeasure U hU) A B,
      s.period = r.period ∧ s.left.active = r.left.active ∧ s.right.active = r.right.active ∧
      loebMeasure (X := fun n => ZMod (q n : ℕ)) U hU (s.period : Set _) +
        loebMeasure (X := fun n => ZMod (q n : ℕ)) U hU (s.period : Set _) ≤
          loebMeasure (X := fun n => ZMod (q n : ℕ)) U hU (p.period : Set _) := by
  have hle := loeb_quasiPeriodic_refinement_period_le U hU q A B p r
  have hne := loeb_quasiPeriodic_refinement_period_ne U hU q A B p r
  refine ⟨p.refine r hle, rfl, rfl, rfl, ?_⟩
  exact loeb_proper_subgroup_measure_double_le U hU q p.period r.period r.period_measurable hle hne

end Erdos335.Loeb

end
