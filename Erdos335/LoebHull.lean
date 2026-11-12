import Erdos335.LoebMeasure

/-!
# Internal upper bounds for countable internal families

A countable family whose finite unions have uniformly bounded measure has
an internal upper bound with any prescribed larger bound on its measure.
-/

set_option autoImplicit false

open Filter Set Topology MeasureTheory
open scoped ENNReal symmDiff

namespace Erdos335.Loeb

variable {X : ℕ → Type*} [∀ n, Nonempty (X n)]

omit [∀ n, Nonempty (X n)] in
theorem internalSet_biUnion_finset {K : Type*} (U : Ultrafilter ℕ)
    (J : Finset K) (A : K → ∀ n, Set (X n)) :
    internalSet U (fun n => ⋃ k ∈ J, A k n) = ⋃ k ∈ J, internalSet U (A k) := by
  ext x
  induction x using Quotient.inductionOn with
  | h f =>
    constructor
    · intro hx
      have he : ∀ᶠ n in U, ∃ k ∈ (J : Set K), f n ∈ A k n := by
        apply hx.mono
        intro n hn
        obtain ⟨k, hk⟩ := mem_iUnion.mp hn
        obtain ⟨hkJ, hkn⟩ := mem_iUnion.mp hk
        exact ⟨k, hkJ, hkn⟩
      obtain ⟨k, hk, hfk⟩ := (Ultrafilter.eventually_exists_mem_iff J.finite_toSet).mp he
      exact mem_iUnion.mpr ⟨k, mem_iUnion.mpr ⟨hk, hfk⟩⟩
    · intro hx
      obtain ⟨k, hk⟩ := mem_iUnion.mp hx
      obtain ⟨hkJ, hfk⟩ := mem_iUnion.mp hk
      exact hfk.mono fun n hn => mem_iUnion.mpr ⟨k, mem_iUnion.mpr ⟨hkJ, hn⟩⟩

theorem exists_internal_upper_bound
    (U : Ultrafilter ℕ) (hU : (U : Filter ℕ) ≤ atTop)
    (A : ℕ → ∀ n, Set (X n)) (r c : ℝ≥0∞) (hrc : r < c)
    (hA : ∀ k, ultraCount U (fun n => ⋃ j ≤ k, A j n) ≤ r) :
    ∃ B : ∀ n, Set (X n), (∀ j, internalSet U (A j) ⊆ internalSet U B) ∧
      ultraCount U B ≤ c := by
  let P (j n : ℕ) : Set (Set (X n)) :=
    {B | (∀ i ≤ j, A i n ⊆ B) ∧ countingRatio B ≤ c}
  have hfinite : ∀ k, ∀ᶠ n in U, ∃ B : Set (X n), ∀ j ≤ k, B ∈ P j n := by
    intro k
    have hlim := tendsto_ultraCount U (fun n => ⋃ j ≤ k, A j n)
    have he : ∀ᶠ n in U, countingRatio (⋃ j ≤ k, A j n) < c :=
      hlim.eventually (gt_mem_nhds ((hA k).trans_lt hrc))
    apply he.mono
    intro n hn
    refine ⟨⋃ j ≤ k, A j n, fun j hj => ⟨?_, hn.le⟩⟩
    intro i hi x hx
    exact mem_iUnion.mpr ⟨i, mem_iUnion.mpr ⟨hi.trans hj, hx⟩⟩
  obtain ⟨B, hB⟩ := exists_representative_of_eventually_finite U hU P hfinite
  refine ⟨B, fun j => ?_, ?_⟩
  · apply (internalSet_subset_iff U (A j) B).mpr
    exact (hB j).mono fun n hn => hn.1 j le_rfl
  · apply le_of_tendsto (tendsto_ultraCount U B)
    exact (hB 0).mono fun n hn => hn.2

theorem exists_internal_cover_of_countable [∀ n, Finite (X n)]
    (U : Ultrafilter ℕ) (hU : (U : Filter ℕ) ≤ atTop)
    (V : ℕ → Set ((U : Filter ℕ).Product X)) (hV : ∀ k, V k ∈ internalSets U)
    (r c : ℝ≥0∞) (hrc : r < c)
    (hbound : ∀ k, loebMeasure U hU (⋃ j ≤ k, V j) ≤ r) :
    ∃ B ∈ internalSets U, (⋃ j, V j) ⊆ B ∧ loebMeasure U hU B ≤ c := by
  choose A hA using hV
  have hEq : V = fun j => internalSet U (A j) := funext fun j => (hA j).symm
  subst V
  have hfinite : ∀ k, ultraCount U (fun n => ⋃ j ≤ k, A j n) ≤ r := by
    intro k
    rw [← loebMeasure_internal U hU]
    have hUnion := internalSet_biUnion_finset U (Finset.range (k + 1)) A
    simp only [Finset.mem_range, Nat.lt_succ_iff] at hUnion
    rw [hUnion]
    exact hbound k
  obtain ⟨B, hB, hBc⟩ := exists_internal_upper_bound U hU A r c hrc hfinite
  refine ⟨internalSet U B, ⟨B, rfl⟩, iUnion_subset hB, ?_⟩
  rw [loebMeasure_internal]
  exact hBc

theorem exists_countable_internal_cover_lt [∀ n, Finite (X n)]
    (U : Ultrafilter ℕ) (hU : (U : Filter ℕ) ≤ atTop)
    (S : Set ((U : Filter ℕ).Product X)) (c : ℝ≥0∞)
    (hSc : loebMeasure U hU S < c) :
    ∃ V : ℕ → Set ((U : Filter ℕ).Product X), (∀ n, V n ∈ internalSets U) ∧
      S ⊆ ⋃ n, V n ∧ (∑' n, loebMeasure U hU (V n)) < c := by
  let m : ∀ T : Set ((U : Filter ℕ).Product X), T ∈ internalSets U → ℝ≥0∞ :=
    fun T _ => internalCountingContent U T
  have hformula : loebMeasure U hU S =
      ⨅ (V : ℕ → Set ((U : Filter ℕ).Product X)) (_ : ∀ n, V n ∈ internalSets U)
        (_ : S ⊆ ⋃ n, V n), ∑' n, extend m (V n) := by
    exact OuterMeasure.ofFunction_eq_iInf_mem (extend m)
      (extend_empty (isSetAlgebra_internalSets (X := X) U).empty_mem addContent_empty)
      (fun T hT => extend_eq_top m hT) S
  rw [hformula] at hSc
  obtain ⟨V, hV⟩ := iInf_lt_iff.mp hSc
  obtain ⟨hVi, hV⟩ := iInf_lt_iff.mp hV
  obtain ⟨hcover, hVsum⟩ := iInf_lt_iff.mp hV
  refine ⟨V, hVi, hcover, ?_⟩
  have hterms : ∀ n, loebMeasure U hU (V n) = extend m (V n) := by
    intro n
    obtain ⟨A, hA⟩ := hVi n
    rw [← hA, loebMeasure_internal, extend_eq m ⟨A, rfl⟩]
    exact (internalCountingContent_internal U A).symm
  simpa only [hterms] using hVsum

theorem exists_internal_cover_lt [∀ n, Finite (X n)]
    (U : Ultrafilter ℕ) (hU : (U : Filter ℕ) ≤ atTop)
    (S : Set ((U : Filter ℕ).Product X)) (c : ℝ≥0∞)
    (hSc : loebMeasure U hU S < c) :
    ∃ B ∈ internalSets U, S ⊆ B ∧ loebMeasure U hU B < c := by
  obtain ⟨V, hV, hSV, hsum⟩ := exists_countable_internal_cover_lt U hU S c hSc
  obtain ⟨c', hleft, hright⟩ := exists_between hsum
  have hbound : ∀ k, loebMeasure U hU (⋃ j ≤ k, V j) ≤ ∑' j, loebMeasure U hU (V j) := by
    intro k
    calc
      loebMeasure U hU (⋃ j ≤ k, V j) ≤
          loebMeasure U hU (⋃ j, V j) := measure_mono (iUnion₂_subset fun j _ => subset_iUnion V j)
      _ ≤ ∑' j, loebMeasure U hU (V j) := measure_iUnion_le V
  obtain ⟨B, hBi, hVB, hBc⟩ := exists_internal_cover_of_countable U hU V hV
    (∑' j, loebMeasure U hU (V j)) c' hleft hbound
  exact ⟨B, hBi, hSV.trans hVB, hBc.trans_lt hright⟩

theorem measurable_of_loebMeasure_zero [∀ n, Finite (X n)]
    (U : Ultrafilter ℕ) (hU : (U : Filter ℕ) ≤ atTop)
    (S : Set ((U : Filter ℕ).Product X)) (hS : loebMeasure U hU S = 0) :
    MeasurableSet[loebMeasurableSpace U] S := by
  let : MeasurableSpace ((U : Filter ℕ).Product X) := loebMeasurableSpace U
  change (loebMeasure U hU).toOuterMeasure.IsCaratheodory S
  apply (OuterMeasure.isCaratheodory_iff_le' (loebMeasure U hU).toOuterMeasure).mpr
  intro T
  change loebMeasure U hU (T ∩ S) + loebMeasure U hU (T \ S) ≤ loebMeasure U hU T
  have hzero : loebMeasure U hU (T ∩ S) = 0 :=
    le_antisymm ((measure_mono inter_subset_right).trans_eq hS) bot_le
  rw [hzero, zero_add]
  exact measure_mono sdiff_subset

theorem exists_internal_approximation [∀ n, Finite (X n)]
    (U : Ultrafilter ℕ) (hU : (U : Filter ℕ) ≤ atTop)
    (S : Set ((U : Filter ℕ).Product X)) (hS : MeasurableSet[loebMeasurableSpace U] S)
    (ε : ℝ≥0∞) (hε : 0 < ε) :
    ∃ B ∈ internalSets U, S ⊆ B ∧ loebMeasure U hU (S ∆ B) < ε := by
  let : MeasurableSpace ((U : Filter ℕ).Product X) := loebMeasurableSpace U
  have hSfin : loebMeasure U hU S ≠ ∞ := by
    apply ne_of_lt
    calc
      loebMeasure U hU S ≤ loebMeasure U hU univ := measure_mono (subset_univ S)
      _ = 1 := loebMeasure_univ U hU
      _ < ∞ := ENNReal.one_lt_top
  obtain ⟨B, hBi, hSB, hB⟩ := exists_internal_cover_lt U hU S
    (loebMeasure U hU S + ε) (ENNReal.lt_add_right hSfin hε.ne')
  refine ⟨B, hBi, hSB, ?_⟩
  rw [Set.symmDiff_def, Set.sdiff_eq_empty.mpr hSB, empty_union]
  exact measure_sdiff_lt_of_lt_add hS.nullMeasurableSet hSB hSfin hB

end Erdos335.Loeb
