import Erdos335.LoebInnerSumBounds
import Erdos335.LoebFiniteCriticalUnion

/-!
# A noncritical component outside a periodic base

Nonempty measurable sections suffice for this finite-union alternative.
The positivity required by Kneser follows from a strict deficit.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Filter Set MeasureTheory
open scoped Pointwise ENNReal

noncomputable section

namespace Erdos335.Loeb

local instance finiteNoncriticalLoebSpace (U : Ultrafilter ℕ) (q : ℕ → ℕ+) :
    MeasurableSpace ((U : Filter ℕ).Product (fun n => ZMod (q n : ℕ))) := loebMeasurableSpace U

theorem loeb_nonperiodic_union_base_has_noncritical_component
    (U : Ultrafilter ℕ) (hU : (U : Filter ℕ) ≤ atTop) (q : ℕ → ℕ+)
    {I : Type*} [Fintype I]
    (A B : I → Set ((U : Filter ℕ).Product (fun n => ZMod (q n : ℕ))))
    (hAm : ∀ i, MeasurableSet (A i)) (hBm : ∀ i, MeasurableSet (B i))
    (hA : ∀ i, (A i).Nonempty) (hB : ∀ i, (B i).Nonempty)
    (T : Set ((U : Filter ℕ).Product (fun n => ZMod (q n : ℕ))))
    (H : AddSubgroup ((U : Filter ℕ).Product (fun n => ZMod (q n : ℕ))))
    (hHm : MeasurableSet (H : Set ((U : Filter ℕ).Product (fun n => ZMod (q n : ℕ)))))
    (hHpos : 0 < loebMeasure (X := fun n => ZMod (q n : ℕ)) U hU (H : Set _))
    (hTperiod : T + (H : Set _) = T)
    (hnotperiod : ¬ ∃ L : AddSubgroup ((U : Filter ℕ).Product (fun n => ZMod (q n : ℕ))),
      MeasurableSet (L : Set ((U : Filter ℕ).Product (fun n => ZMod (q n : ℕ)))) ∧
      0 < loebMeasure (X := fun n => ZMod (q n : ℕ)) U hU (L : Set _) ∧
      (T ∪ ⋃ i, A i + B i) + (L : Set _) = T ∪ ⋃ i, A i + B i) :
    ∃ i, loebMeasure U hU (A i) + loebMeasure U hU (B i) ≤
      internalInnerMeasure U hU (A i + B i) := by
  classical
  by_contra h
  push Not at h
  have hpos := fun i => loeb_positive_of_strict_sum_deficit U hU (A i) (B i)
    (hAm i) (hBm i) (hA i) (hB i) (h i)
  obtain ⟨K, hKm, hKpos, hKperiod⟩ := loeb_finite_union_of_critical_sums_periodic U hU q A B
    hAm hBm (fun i => (hpos i).1) (fun i => (hpos i).2) h
  obtain ⟨hLm, hLpos⟩ := loeb_positive_subgroup_intersection U hU q H K hHm hKm hHpos hKpos
  let G := (U : Filter ℕ).Product (fun n => ZMod (q n : ℕ))
  have shrink (S : Set G) (J L : AddSubgroup G) (hLJ : L ≤ J)
      (hS : S + (J : Set G) = S) : S + (L : Set G) = S := by
    apply subset_antisymm
    · intro x hx
      have hx' := add_subset_add (show S ⊆ S from Subset.rfl) hLJ hx
      rwa [hS] at hx'
    · intro x hx
      exact ⟨x, hx, 0, L.zero_mem, add_zero x⟩
  have hTL := shrink T H (H ⊓ K) inf_le_left hTperiod
  have hUL := shrink (⋃ i, A i + B i) K (H ⊓ K) inf_le_right hKperiod
  apply hnotperiod
  refine ⟨H ⊓ K, hLm, hLpos, ?_⟩
  rw [union_add, hTL, hUL]

end Erdos335.Loeb

end
