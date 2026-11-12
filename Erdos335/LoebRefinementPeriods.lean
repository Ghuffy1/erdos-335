import Erdos335.QuasiPeriodicRefinement
import Erdos335.LoebQuasiPeriodicRestriction

/-!
# Strict decrease of quasi-periods in an active-pair refinement
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Filter Set Topology MeasureTheory
open scoped Pointwise ENNReal

noncomputable section

namespace Erdos335.Loeb

local instance refinementPeriodsLoebSpace (U : Ultrafilter ℕ) (q : ℕ → ℕ+) :
    MeasurableSpace ((U : Filter ℕ).Product (fun n => ZMod (q n : ℕ))) := loebMeasurableSpace U

theorem loeb_period_le_of_positive_coset_subset
    (U : Ultrafilter ℕ) (hU : (U : Filter ℕ) ≤ atTop) (q : ℕ → ℕ+)
    (H K : AddSubgroup ((U : Filter ℕ).Product (fun n => ZMod (q n : ℕ))))
    (C : Set ((U : Filter ℕ).Product (fun n => ZMod (q n : ℕ))))
    (a : (U : Filter ℕ).Product (fun n => ZMod (q n : ℕ)))
    (hC : C ⊆ a +ᵥ (H : Set _)) (hpos : 0 < loebMeasure U hU C)
    (hperiod : loebMeasure U hU ((C + (K : Set _)) \ C) = 0) : K ≤ H := by
  intro k hk
  by_contra hkH
  have hsub : k +ᵥ C ⊆ (C + (K : Set _)) \ C := by
    rintro x ⟨c, hc, rfl⟩
    refine ⟨⟨c, hc, k, hk, by simp only [vadd_eq_add]; ac_rfl⟩, ?_⟩
    intro hkc
    obtain ⟨u, hu, huc⟩ := hC hc
    obtain ⟨v, hv, hvkc⟩ := hC hkc
    apply hkH
    have heq : k = v - u := by
      change a + u = c at huc
      change a + v = k + c at hvkc
      rw [← huc] at hvkc
      apply add_right_cancel (b := a + u)
      calc
        k + (a + u) = a + v := hvkc.symm
        _ = (v - u) + (a + u) := by abel
    rw [heq]
    exact H.sub_mem hv hu
  have hzero := measure_mono_null hsub hperiod
  change loebMeasure U hU ((fun x => k + x) '' C) = 0 at hzero
  rw [loebMeasure_image_add_left] at hzero
  exact hpos.ne' hzero

theorem loeb_quasiPeriodic_refinement_period_le
    (U : Ultrafilter ℕ) (hU : (U : Filter ℕ) ≤ atTop) (q : ℕ → ℕ+)
    (A B : Set ((U : Filter ℕ).Product (fun n => ZMod (q n : ℕ))))
    (p : QuasiPeriodicPairData (loebMeasure U hU) (internalInnerMeasure U hU) A B)
    (r : QuasiPeriodicPairData (loebMeasure U hU) (internalInnerMeasure U hU)
      p.left.active p.right.active) : r.period ≤ p.period := by
  rcases r.nonempty_background with hleft | hright
  · apply loeb_period_le_of_positive_coset_subset U hU q p.period r.period
      r.left.background p.left.anchor
      ((subset_union_left.trans r.left.partition.ge).trans p.left.active_subset_coset)
    · exact loeb_quasiPeriodic_background_positive U hU q r.period p.left.active r.left
        r.period_positive hleft
    · exact r.left.background_periodic
  · apply loeb_period_le_of_positive_coset_subset U hU q p.period r.period
      r.right.background p.right.anchor
      ((subset_union_left.trans r.right.partition.ge).trans p.right.active_subset_coset)
    · exact loeb_quasiPeriodic_background_positive U hU q r.period p.right.active r.right
        r.period_positive hright
    · exact r.right.background_periodic

theorem QuasiPeriodicDecomposition.period_ne_of_coset_containment
    {G : Type*} [AddCommGroup G] [MeasurableSpace G]
    {μ : Measure G} {H K : AddSubgroup G} {A : Set G}
    (p : QuasiPeriodicDecomposition μ K A) (a : G)
    (hA : A ⊆ a +ᵥ (H : Set G)) (hbg : p.background.Nonempty) : K ≠ H := by
  intro heq
  obtain ⟨x, hx⟩ := p.active_nonempty
  obtain ⟨y, hy⟩ := hbg
  obtain ⟨u, hu, hux⟩ := hA ((subset_union_right.trans p.partition.ge) hx)
  obtain ⟨v, hv, hvy⟩ := hA ((subset_union_left.trans p.partition.ge) hy)
  have hdiff : y - x ∈ K := by
    rw [heq]
    have hd : y - x = v - u := by
      change a + u = x at hux
      change a + v = y at hvy
      rw [← hux, ← hvy]
      abel
    rw [hd]
    exact H.sub_mem hv hu
  have hysum : y ∈ p.active + (K : Set G) := ⟨x, hx, y - x, hdiff, by abel⟩
  exact Set.disjoint_left.mp p.separated hysum hy

theorem loeb_quasiPeriodic_refinement_period_ne
    (U : Ultrafilter ℕ) (hU : (U : Filter ℕ) ≤ atTop) (q : ℕ → ℕ+)
    (A B : Set ((U : Filter ℕ).Product (fun n => ZMod (q n : ℕ))))
    (p : QuasiPeriodicPairData (loebMeasure U hU) (internalInnerMeasure U hU) A B)
    (r : QuasiPeriodicPairData (loebMeasure U hU) (internalInnerMeasure U hU)
      p.left.active p.right.active) : r.period ≠ p.period := by
  rcases r.nonempty_background with hleft | hright
  · exact r.left.period_ne_of_coset_containment p.left.anchor p.left.active_subset_coset hleft
  · exact r.right.period_ne_of_coset_containment p.right.anchor p.right.active_subset_coset hright

end Erdos335.Loeb

end
