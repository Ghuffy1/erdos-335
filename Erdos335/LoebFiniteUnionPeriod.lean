import Erdos335.LoebFinitePeriodIntersection

/-!
# A common positive period for a finite union
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Filter Set Topology MeasureTheory
open scoped Pointwise ENNReal

noncomputable section

namespace Erdos335.Loeb

local instance finiteUnionPeriodLoebSpace (U : Ultrafilter ℕ) (q : ℕ → ℕ+) :
    MeasurableSpace ((U : Filter ℕ).Product (fun n => ZMod (q n : ℕ))) := loebMeasurableSpace U

theorem loeb_finset_period_intersection
    (U : Ultrafilter ℕ) (hU : (U : Filter ℕ) ≤ atTop) (q : ℕ → ℕ+)
    {I : Type*} (s : Finset I)
    (H : I → AddSubgroup ((U : Filter ℕ).Product (fun n => ZMod (q n : ℕ))))
    (hmeas : ∀ i ∈ s, MeasurableSet (H i : Set ((U : Filter ℕ).Product (fun n => ZMod (q n : ℕ)))))
    (hpos : ∀ i ∈ s, 0 < loebMeasure (X := fun n => ZMod (q n : ℕ)) U hU (H i : Set _)) :
    let K := s.inf H
    MeasurableSet (K : Set ((U : Filter ℕ).Product (fun n => ZMod (q n : ℕ)))) ∧
      0 < loebMeasure (X := fun n => ZMod (q n : ℕ)) U hU (K : Set _) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    simp only [Finset.inf_empty, AddSubgroup.coe_top]
    exact ⟨MeasurableSet.univ, by rw [loebMeasure_univ]; norm_num⟩
  | @insert i s hi ih =>
    have hiMeas := hmeas i (Finset.mem_insert_self i s)
    have hiPos := hpos i (Finset.mem_insert_self i s)
    obtain ⟨hsMeas, hsPos⟩ := ih
      (fun j hj => hmeas j (Finset.mem_insert_of_mem hj))
      (fun j hj => hpos j (Finset.mem_insert_of_mem hj))
    simpa only [Finset.inf_insert, AddSubgroup.coe_inf, Set.inf_eq_inter] using
      loeb_positive_subgroup_intersection U hU q (H i) (s.inf H) hiMeas hsMeas hiPos hsPos

theorem loeb_finite_union_has_positive_period
    (U : Ultrafilter ℕ) (hU : (U : Filter ℕ) ≤ atTop) (q : ℕ → ℕ+)
    {I : Type*} (s : Finset I)
    (S : I → Set ((U : Filter ℕ).Product (fun n => ZMod (q n : ℕ))))
    (H : I → AddSubgroup ((U : Filter ℕ).Product (fun n => ZMod (q n : ℕ))))
    (hmeas : ∀ i ∈ s, MeasurableSet (H i : Set ((U : Filter ℕ).Product (fun n => ZMod (q n : ℕ)))))
    (hpos : ∀ i ∈ s, 0 < loebMeasure (X := fun n => ZMod (q n : ℕ)) U hU (H i : Set _))
    (hperiod : ∀ i ∈ s, S i + (H i : Set _) = S i) :
    ∃ K : AddSubgroup ((U : Filter ℕ).Product (fun n => ZMod (q n : ℕ))),
      MeasurableSet (K : Set ((U : Filter ℕ).Product (fun n => ZMod (q n : ℕ)))) ∧
      0 < loebMeasure (X := fun n => ZMod (q n : ℕ)) U hU (K : Set _) ∧
      (⋃ i ∈ s, S i) + (K : Set _) = ⋃ i ∈ s, S i := by
  classical
  obtain ⟨hKm, hKpos⟩ := loeb_finset_period_intersection U hU q s H hmeas hpos
  refine ⟨s.inf H, hKm, hKpos, subset_antisymm ?_ ?_⟩
  · rintro x ⟨a, ha, k, hk, rfl⟩
    obtain ⟨i, hi⟩ := mem_iUnion.mp ha
    obtain ⟨his, hai⟩ := mem_iUnion.mp hi
    apply mem_iUnion.mpr
    refine ⟨i, mem_iUnion.mpr ⟨his, ?_⟩⟩
    have hle : s.inf H ≤ H i := Finset.inf_le his
    have hkH : k ∈ H i := hle hk
    have hx : a + k ∈ S i + (H i : Set _) := ⟨a, hai, k, hkH, rfl⟩
    rwa [hperiod i his] at hx
  · intro x hx
    exact ⟨x, hx, 0, (s.inf H).zero_mem, add_zero x⟩

end Erdos335.Loeb

end
