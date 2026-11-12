import Erdos335.LoebInnerMeasure

/-!
# Internal representatives modulo Loeb null sets

Countable saturation gives an internal upper bound at the exact finite
measure bound. Applying it to internal inner approximations represents
every measurable set, up to a null set, by an internal set.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Filter Set Topology MeasureTheory
open scoped ENNReal symmDiff

noncomputable section

namespace Erdos335.Loeb

variable {X : ℕ → Type*} [∀ n, Finite (X n)] [∀ n, Nonempty (X n)]

local instance internalRepresentativeLoebSpace (U : Ultrafilter ℕ) :
    MeasurableSpace ((U : Filter ℕ).Product X) := loebMeasurableSpace U

theorem exists_internal_upper_bound_exact
    (U : Ultrafilter ℕ) (hU : (U : Filter ℕ) ≤ atTop)
    (A : ℕ → ∀ n, Set (X n)) (r : ℝ≥0∞) (hr : r ≠ ∞)
    (hA : ∀ k, ultraCount U (fun n => ⋃ j ≤ k, A j n) ≤ r) :
    ∃ B : ∀ n, Set (X n), (∀ j, internalSet U (A j) ⊆ internalSet U B) ∧ ultraCount U B ≤ r := by
  let ε (n : ℕ) : ℝ≥0∞ := ENNReal.ofReal (1 / ((n : ℝ) + 1))
  have hεpos (n : ℕ) : 0 < ε n := by dsimp [ε]; positivity
  have hε : Tendsto ε atTop (𝓝 0) := by
    simpa only [Function.comp_def, ENNReal.ofReal_zero] using
      (ENNReal.continuous_ofReal.tendsto 0).comp tendsto_one_div_add_atTop_nhds_zero_nat
  let P (j n : ℕ) : Set (Set (X n)) :=
    {B | (∀ i ≤ j, A i n ⊆ B) ∧ countingRatio B ≤ r + ε j}
  have hfinite : ∀ k, ∀ᶠ n in U, ∃ B : Set (X n), ∀ j ≤ k, B ∈ P j n := by
    intro k
    have hlim := tendsto_ultraCount U (fun n => ⋃ j ≤ k, A j n)
    have heach (j : ℕ) : ∀ᶠ n in U, countingRatio (⋃ i ≤ k, A i n) < r + ε j :=
      hlim.eventually (gt_mem_nhds ((hA k).trans_lt (ENNReal.lt_add_right hr (hεpos j).ne')))
    have he := (eventually_all_finset (Finset.range (k + 1))).mpr (fun j _ => heach j)
    apply he.mono
    intro n hn
    refine ⟨⋃ i ≤ k, A i n, fun j hj => ⟨?_, (hn j (by simpa only [Finset.mem_range, Nat.lt_succ_iff] using hj)).le⟩⟩
    intro i hi x hx
    exact mem_iUnion.mpr ⟨i, mem_iUnion.mpr ⟨hi.trans hj, hx⟩⟩
  obtain ⟨B, hB⟩ := exists_representative_of_eventually_finite U hU P hfinite
  refine ⟨B, fun j => ?_, ?_⟩
  · exact (internalSet_subset_iff U (A j) B).mpr ((hB j).mono fun n hn => hn.1 j le_rfl)
  · have hbound (j : ℕ) : ultraCount U B ≤ r + ε j :=
      le_of_tendsto (tendsto_ultraCount U B) ((hB j).mono fun n hn => hn.2)
    have hlim : Tendsto (fun j => r + ε j) atTop (𝓝 r) := by
      simpa only [add_zero] using tendsto_const_nhds.add hε
    exact ge_of_tendsto' hlim hbound

theorem exists_internal_ae_representative
    (U : Ultrafilter ℕ) (hU : (U : Filter ℕ) ≤ atTop)
    (S : Set ((U : Filter ℕ).Product X)) (hS : MeasurableSet S) :
    ∃ A : ∀ n, Set (X n), internalSet U A =ᵐ[loebMeasure U hU] S := by
  let μ := loebMeasure (X := X) U hU
  letI : IsProbabilityMeasure μ := isProbabilityMeasure_loebMeasure U hU
  let ε (n : ℕ) : ℝ≥0∞ := ENNReal.ofReal (1 / ((n : ℝ) + 1))
  have hεpos (n : ℕ) : 0 < ε n := by dsimp [ε]; positivity
  have hε : Tendsto ε atTop (𝓝 0) := by
    simpa only [Function.comp_def, ENNReal.ofReal_zero] using
      (ENNReal.continuous_ofReal.tendsto 0).comp tendsto_one_div_add_atTop_nhds_zero_nat
  choose V hVi hVS herror using fun n => exists_internal_inner_approximation U hU S hS (ε n) (hεpos n)
  choose A hA using hVi
  let E := ⋃ n, V n
  have hEm : MeasurableSet E := MeasurableSet.iUnion (fun n => by rw [← hA n]; exact measurable_internalSet U (A n))
  have hES : E ⊆ S := iUnion_subset hVS
  have hEmass : μ E = μ S := by
    apply le_antisymm (measure_mono hES)
    have hbound (n : ℕ) : μ S ≤ μ E + ε n := by
      have hcover : S ⊆ V n ∪ (S ∆ V n) := by
        intro x hx
        by_cases hv : x ∈ V n
        · exact Or.inl hv
        · exact Or.inr (Or.inl ⟨hx, hv⟩)
      calc
        μ S ≤ μ (V n ∪ (S ∆ V n)) := measure_mono hcover
        _ ≤ μ (V n) + μ (S ∆ V n) := measure_union_le _ _
        _ ≤ μ E + ε n := add_le_add (measure_mono (subset_iUnion V n)) (herror n).le
    have hlim : Tendsto (fun n => μ E + ε n) atTop (𝓝 (μ E)) := by
      simpa only [add_zero] using tendsto_const_nhds.add hε
    exact ge_of_tendsto' hlim hbound
  have hfinite (k : ℕ) : ultraCount U (fun n => ⋃ j ≤ k, A j n) ≤ μ S := by
    rw [← loebMeasure_internal U hU]
    have hUnion := internalSet_biUnion_finset U (Finset.range (k + 1)) A
    simp only [Finset.mem_range, Nat.lt_succ_iff] at hUnion
    rw [hUnion]
    apply measure_mono
    apply iUnion₂_subset
    intro j _
    rw [hA j]
    exact hVS j
  obtain ⟨B, hB, hBmass⟩ := exists_internal_upper_bound_exact U hU A (μ S) (measure_ne_top μ S) hfinite
  have hEB : E ⊆ internalSet U B := by
    apply iUnion_subset
    intro n
    rw [← hA n]
    exact hB n
  have hBmass' : μ (internalSet U B) = μ S := by
    apply le_antisymm
    · simpa only [μ, loebMeasure_internal] using hBmass
    · rw [← hEmass]
      exact measure_mono hEB
  have hSZ : μ (S \ E) = 0 := by
    rw [measure_sdiff hES hEm.nullMeasurableSet (measure_ne_top μ _), hEmass, tsub_self]
  have hBZ : μ ((internalSet U B) \ E) = 0 := by
    rw [measure_sdiff hEB hEm.nullMeasurableSet (measure_ne_top μ _), hBmass', hEmass, tsub_self]
  have hESA : E =ᵐ[μ] S := hES.eventuallySubset.antisymm (ae_le_set.mpr hSZ)
  have hEBA : E =ᵐ[μ] internalSet U B := hEB.eventuallySubset.antisymm (ae_le_set.mpr hBZ)
  exact ⟨B, hEBA.symm.trans hESA⟩

end Erdos335.Loeb

end
