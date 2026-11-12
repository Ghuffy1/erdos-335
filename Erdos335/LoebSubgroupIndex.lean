import Erdos335.LoebPositiveSubgroups

/-!
# Bounded-index termination in cyclic Loeb groups

A positive measurable subgroup has measure equal to the reciprocal of its
finite index. Each proper subgroup step multiplies the index by at least two.
A fixed positive lower bound on subgroup measure therefore prevents an
infinite sequence of proper refinements.
-/

set_option autoImplicit false

open Filter Set Topology MeasureTheory
open scoped ENNReal

namespace Erdos335.Loeb

theorem positive_measurable_subgroup_index
    (U : Ultrafilter ℕ) (hU : (U : Filter ℕ) ≤ atTop) (q : ℕ → ℕ+)
    (H : AddSubgroup ((U : Filter ℕ).Product (fun n => ZMod (q n : ℕ))))
    (hH : MeasurableSet[loebMeasurableSpace U]
      (H : Set ((U : Filter ℕ).Product (fun n => ZMod (q n : ℕ)))))
    (hpos : 0 < loebMeasure U hU (H : Set ((U : Filter ℕ).Product (fun n => ZMod (q n : ℕ))))) :
    0 < H.index ∧ loebMeasure U hU
      (H : Set ((U : Filter ℕ).Product (fun n => ZMod (q n : ℕ)))) =
        1 / (H.index : ℝ≥0∞) := by
  obtain ⟨h, p, hp, hker, hmass⟩ :=
    positive_measurable_subgroup_is_natural_finite_kernel U hU q H hH hpos
  have hsurj := finiteQuotient_surjective_of_eventually U p (hp.mono fun _ hi => hi.1)
  have hindex : H.index = (h : ℕ) := by
    rw [← hker, AddSubgroup.index_eq_card]
    simpa only [Nat.card_zmod] using Nat.card_congr
      (QuotientAddGroup.quotientKerEquivOfSurjective (finiteQuotient U p) hsurj).toEquiv
  exact ⟨hindex.symm ▸ h.pos, hindex.symm ▸ hmass⟩

theorem twice_index_le_of_proper_subgroup
    {G : Type*} [AddCommGroup G] (H K : AddSubgroup G)
    (hHK : H < K) (hindex : H.index ≠ 0) : 2 * K.index ≤ H.index := by
  have hrel : H.relIndex K ≠ 0 := by
    intro hz
    exact hindex (H.index_eq_zero_of_relIndex_eq_zero hz)
  have hne : H.relIndex K ≠ 1 := by
    intro hone
    exact (not_le_of_gt hHK) (AddSubgroup.relIndex_eq_one.mp hone)
  have htwo : 2 ≤ H.relIndex K := by omega
  calc
    2 * K.index ≤ H.relIndex K * K.index := Nat.mul_le_mul_right _ htwo
    _ = H.index := H.relIndex_mul_index hHK.le

theorem positive_subgroup_index_le_of_measure_bound
    (U : Ultrafilter ℕ) (hU : (U : Filter ℕ) ≤ atTop) (q : ℕ → ℕ+)
    (H : AddSubgroup ((U : Filter ℕ).Product (fun n => ZMod (q n : ℕ))))
    (hH : MeasurableSet[loebMeasurableSpace U]
      (H : Set ((U : Filter ℕ).Product (fun n => ZMod (q n : ℕ)))))
    (δ : ℝ≥0∞) (hδ : 0 < δ)
    (hlower : δ ≤ loebMeasure U hU
      (H : Set ((U : Filter ℕ).Product (fun n => ZMod (q n : ℕ)))))
    (D : ℕ) (hD : 1 / ((D + 1 : ℕ) : ℝ≥0∞) < δ) : H.index ≤ D := by
  have hpos := hδ.trans_le hlower
  obtain ⟨_, hmass⟩ := positive_measurable_subgroup_index U hU q H hH hpos
  by_contra hn
  have hindex : D + 1 ≤ H.index := by omega
  have hinv : 1 / (H.index : ℝ≥0∞) ≤ 1 / ((D + 1 : ℕ) : ℝ≥0∞) := by
    simpa only [one_div] using ENNReal.inv_le_inv.mpr
      (show ((D + 1 : ℕ) : ℝ≥0∞) ≤ (H.index : ℝ≥0∞) by exact_mod_cast hindex)
  exact (not_le_of_gt hD) (hlower.trans (hmass.le.trans hinv))

theorem exists_nat_reciprocal_lt (δ : ℝ≥0∞) (hδ : 0 < δ) :
    ∃ D : ℕ, 1 / ((D + 1 : ℕ) : ℝ≥0∞) < δ := by
  have hevent := ENNReal.tendsto_inv_nat_nhds_zero.eventually (gt_mem_nhds hδ)
  obtain ⟨N, hN⟩ := Filter.eventually_atTop.mp hevent
  refine ⟨N, ?_⟩
  simpa only [one_div] using hN (N + 1) (by omega)

theorem no_infinite_proper_refinements_of_measure_bound
    (U : Ultrafilter ℕ) (hU : (U : Filter ℕ) ≤ atTop) (q : ℕ → ℕ+)
    (H : ℕ → AddSubgroup ((U : Filter ℕ).Product (fun n => ZMod (q n : ℕ))))
    (hmeas : ∀ n, MeasurableSet[loebMeasurableSpace U]
      (H n : Set ((U : Filter ℕ).Product (fun i => ZMod (q i : ℕ)))))
    (δ : ℝ≥0∞) (hδ : 0 < δ)
    (hlower : ∀ n, δ ≤ loebMeasure U hU
      (H n : Set ((U : Filter ℕ).Product (fun i => ZMod (q i : ℕ))))) :
    ∃ n, ¬ H (n + 1) < H n := by
  obtain ⟨D, hD⟩ := exists_nat_reciprocal_lt δ hδ
  by_contra h
  have hproper : ∀ n, H (n + 1) < H n := by simpa only [not_exists, not_not] using h
  have hpos (n : ℕ) : 0 < (H n).index :=
    (positive_measurable_subgroup_index U hU q (H n) (hmeas n) (hδ.trans_le (hlower n))).1
  have hgrow : ∀ n, n < (H n).index := by
    intro n
    induction n with
    | zero => exact hpos 0
    | succ n ih =>
      have hdouble := twice_index_le_of_proper_subgroup (H (n + 1)) (H n)
        (hproper n) (hpos (n + 1)).ne'
      have := hpos n
      omega
  have hbound := positive_subgroup_index_le_of_measure_bound U hU q (H D)
    (hmeas D) δ hδ (hlower D) D hD
  exact (not_lt_of_ge hbound) (hgrow D)

end Erdos335.Loeb
