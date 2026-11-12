import Erdos335.LoebInner
import Erdos335.LoebKneser
import Erdos335.LoebCyclicQuotients

/-!
# Positive-measure subgroups of cyclic ultraproducts

Internal inner approximation and Kneser's inequality produce a positive
internal subgroup inside a measurable positive-measure subgroup. A finite
cyclic quotient then identifies the whole subgroup exactly.
-/

set_option autoImplicit false

open Filter Set Topology MeasureTheory
open scoped ENNReal Pointwise symmDiff

namespace Erdos335.Loeb

theorem exists_positive_internal_subgroup
    {X : ℕ → Type*} [∀ n, AddCommGroup (X n)] [∀ n, Finite (X n)]
    (U : Ultrafilter ℕ) (hU : (U : Filter ℕ) ≤ atTop)
    (H : AddSubgroup ((U : Filter ℕ).Product X))
    (hH : MeasurableSet[loebMeasurableSpace U] (H : Set ((U : Filter ℕ).Product X)))
    (hpos : 0 < loebMeasure U hU (H : Set ((U : Filter ℕ).Product X))) :
    ∃ K : ∀ n, AddSubgroup (X n), internalAddSubgroup U K ≤ H ∧
      0 < loebMeasure U hU (internalAddSubgroup U K : Set ((U : Filter ℕ).Product X)) := by
  classical
  let : MeasurableSpace ((U : Filter ℕ).Product X) := loebMeasurableSpace U
  let μ := loebMeasure (X := X) U hU
  letI : IsProbabilityMeasure μ := isProbabilityMeasure_loebMeasure U hU
  have hfinite (S : Set ((U : Filter ℕ).Product X)) : μ S ≠ ∞ := measure_ne_top μ S
  let a : ℝ := (μ (H : Set ((U : Filter ℕ).Product X))).toReal
  have ha : 0 < a := ENNReal.toReal_pos hpos.ne' (hfinite H)
  obtain ⟨T, ⟨A, rfl⟩, hAH, herror⟩ := exists_internal_inner_approximation U hU
    (H : Set ((U : Filter ℕ).Product X)) hH (ENNReal.ofReal (a / 4))
    (ENNReal.ofReal_pos.mpr (by positivity))
  let S := internalSet U A
  have hSH : S ⊆ (H : Set ((U : Filter ℕ).Product X)) := hAH
  have hHmeas : MeasurableSet (H : Set ((U : Filter ℕ).Product X)) := hH
  have hSmeas : MeasurableSet S := measurable_internalSet U A
  change μ ((H : Set ((U : Filter ℕ).Product X)) ∆ S) < ENNReal.ofReal (a / 4) at herror
  have herr : μ ((H : Set ((U : Filter ℕ).Product X)) \ S) < ENNReal.ofReal (a / 4) := by
    simpa only [Set.symmDiff_def, Set.sdiff_eq_empty.mpr hSH, union_empty] using herror
  have hpartition : S ∪ ((H : Set ((U : Filter ℕ).Product X)) \ S) = H := by
    ext x
    constructor
    · rintro (hx | hx)
      · exact hSH hx
      · exact hx.1
    · intro hx
      by_cases hxs : x ∈ S
      · exact Or.inl hxs
      · exact Or.inr ⟨hx, hxs⟩
  have hdisjoint : Disjoint S ((H : Set ((U : Filter ℕ).Product X)) \ S) := by
    exact Set.disjoint_left.mpr fun _ hx hy => hy.2 hx
  have hmeasure : μ (H : Set ((U : Filter ℕ).Product X)) =
      μ S + μ ((H : Set ((U : Filter ℕ).Product X)) \ S) := by
    calc
      μ (H : Set ((U : Filter ℕ).Product X)) =
          μ (S ∪ ((H : Set ((U : Filter ℕ).Product X)) \ S)) := congrArg μ hpartition.symm
      _ = _ := measure_union hdisjoint (MeasurableSet.diff hHmeas hSmeas)
  have hreal := congrArg ENNReal.toReal hmeasure
  rw [ENNReal.toReal_add (hfinite S) (hfinite _)] at hreal
  have herrR := (ENNReal.toReal_lt_toReal (hfinite _) (by simp)).mpr herr
  rw [ENNReal.toReal_ofReal (by positivity)] at herrR
  have hhalf : a < (μ S).toReal + (μ S).toReal := by
    change a = _ at hreal
    linarith
  have hSpos : 0 < (μ S).toReal := by linarith
  have hSne : S.Nonempty := by
    apply Set.nonempty_iff_ne_empty.mpr
    intro heq
    have hz : μ S = 0 := by rw [heq, measure_empty]
    rw [hz, ENNReal.toReal_zero] at hSpos
    exact (lt_irrefl 0) hSpos
  let C := fun n => A n + A n
  let K := fun n => AddAction.stabilizer (X n) (C n)
  have hCsub : internalSet U C ⊆ H := by
    rw [internalSet_add]
    intro x hx
    obtain ⟨y, hy, z, hz, rfl⟩ := Set.mem_add.mp hx
    exact H.add_mem (hAH hy) (hAH hz)
  have hCne : (internalSet U C).Nonempty := by
    rw [internalSet_add]
    exact hSne.add hSne
  refine ⟨K, internal_stabilizer_le_of_subset U C H hCne hCsub, ?_⟩
  have hbound := loebMeasure_internal_add_le U hU A A hSne hSne
  change μ S + μ S ≤ μ (internalSet U C) +
    μ (internalAddSubgroup U K : Set ((U : Filter ℕ).Product X)) at hbound
  by_contra hn
  have hz : μ (internalAddSubgroup U K : Set ((U : Filter ℕ).Product X)) = 0 :=
    le_antisymm (le_of_not_gt hn) bot_le
  rw [hz, add_zero] at hbound
  have hr := ENNReal.toReal_mono (hfinite H) (hbound.trans (measure_mono hCsub))
  rw [ENNReal.toReal_add (hfinite S) (hfinite S)] at hr
  exact (not_le_of_gt hhalf) hr

theorem positive_measurable_subgroup_is_natural_finite_kernel
    (U : Ultrafilter ℕ) (hU : (U : Filter ℕ) ≤ atTop) (q : ℕ → ℕ+)
    (H : AddSubgroup ((U : Filter ℕ).Product (fun n => ZMod (q n : ℕ))))
    (hH : MeasurableSet[loebMeasurableSpace U]
      (H : Set ((U : Filter ℕ).Product (fun n => ZMod (q n : ℕ)))))
    (hpos : 0 < loebMeasure U hU
      (H : Set ((U : Filter ℕ).Product (fun n => ZMod (q n : ℕ))))) :
    ∃ (h : ℕ+) (p : ∀ n, ZMod (q n : ℕ) →+ ZMod (h : ℕ)),
      (∀ᶠ i in U, Function.Surjective (p i) ∧
        ∀ n : ℕ, p i (n : ZMod (q i : ℕ)) = (n : ZMod (h : ℕ))) ∧
      (finiteQuotient U p).ker = H ∧
      loebMeasure U hU
        (H : Set ((U : Filter ℕ).Product (fun n => ZMod (q n : ℕ)))) =
          1 / ((h : ℕ) : ℝ≥0∞) := by
  obtain ⟨K, hKH, hKpos⟩ := exists_positive_internal_subgroup U hU H hH hpos
  obtain ⟨D, hD⟩ := eventually_bounded_index_of_positive_loebMeasure U hU K hKpos
  obtain ⟨m, p, _, hp, hker⟩ := exists_fixed_natural_cyclic_quotient U q K D hD
  have hcontain : (finiteQuotient U p).ker ≤ H := by rw [hker]; exact hKH
  obtain ⟨h, r, _, hr, hrker, hmass⟩ := exists_natural_quotient_of_supergroup U hU q m p
    (hp.mono fun _ hi => ⟨hi.2.1, hi.2.2.2⟩) H hcontain
  exact ⟨h, r, hr, hrker, hmass⟩

end Erdos335.Loeb
