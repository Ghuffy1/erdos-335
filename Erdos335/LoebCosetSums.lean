import Erdos335.LoebConvolutionAE
import Erdos335.CompactPositiveSums
import Erdos335.LoebTranslation

/-!
# Full cosets from overlapping Loeb sections

The finite-measure pigeonhole argument is the cyclic Loeb form of the
coset sum lemma used in Griesmer's critical-pair reductions.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Filter Set Topology MeasureTheory
open scoped ENNReal Pointwise

noncomputable section

namespace Erdos335.Loeb

variable {X : ℕ → Type*} [∀ n, AddCommGroup (X n)] [∀ n, Fintype (X n)]

local instance cosetSumsLoebSpace (U : Ultrafilter ℕ) :
    MeasurableSpace ((U : Filter ℕ).Product X) := loebMeasurableSpace U

theorem measurable_loeb_coset
    (U : Ultrafilter ℕ) (hU : (U : Filter ℕ) ≤ atTop)
    (H : AddSubgroup ((U : Filter ℕ).Product X))
    (hH : MeasurableSet (H : Set ((U : Filter ℕ).Product X)))
    (a : (U : Filter ℕ).Product X) :
    MeasurableSet (a +ᵥ (H : Set ((U : Filter ℕ).Product X))) := by
  have heq : a +ᵥ (H : Set ((U : Filter ℕ).Product X)) =
      (fun x => -a + x) ⁻¹' (H : Set ((U : Filter ℕ).Product X)) := by
    ext x
    constructor
    · rintro ⟨h, hh, rfl⟩
      simpa only [mem_preimage, vadd_eq_add, neg_add_cancel_left] using hh
    · intro hx
      exact ⟨-a + x, hx, by simp [vadd_eq_add]⟩
  rw [heq]
  exact hH.preimage (measurable_add_left U hU (-a))

theorem loebMeasure_coset
    (U : Ultrafilter ℕ) (hU : (U : Filter ℕ) ≤ atTop)
    (H : AddSubgroup ((U : Filter ℕ).Product X))
    (a : (U : Filter ℕ).Product X) :
    loebMeasure U hU (a +ᵥ (H : Set ((U : Filter ℕ).Product X))) =
      loebMeasure U hU (H : Set ((U : Filter ℕ).Product X)) := by
  change loebMeasure U hU ((fun x => a + x) '' (H : Set ((U : Filter ℕ).Product X))) = _
  exact loebMeasure_image_add_left U hU a _

theorem loeb_coset_subset_add_of_measure_sum_gt
    (U : Ultrafilter ℕ) (hU : (U : Filter ℕ) ≤ atTop)
    (H : AddSubgroup ((U : Filter ℕ).Product X))
    (hH : MeasurableSet (H : Set ((U : Filter ℕ).Product X)))
    (A B : Set ((U : Filter ℕ).Product X)) (hB : MeasurableSet B)
    (a b : (U : Filter ℕ).Product X)
    (hsum : loebMeasure U hU (H : Set ((U : Filter ℕ).Product X)) <
      loebMeasure U hU (A ∩ (a +ᵥ (H : Set ((U : Filter ℕ).Product X)))) +
        loebMeasure U hU (B ∩ (b +ᵥ (H : Set ((U : Filter ℕ).Product X))))) :
    (a + b) +ᵥ (H : Set ((U : Filter ℕ).Product X)) ⊆ A + B := by
  let G := (U : Filter ℕ).Product X
  let μ := loebMeasure (X := X) U hU
  rintro x ⟨k, hk, rfl⟩
  let S := A ∩ (a +ᵥ (H : Set G))
  let D := B ∩ (b +ᵥ (H : Set G))
  let T := (fun t => a + b + k - t) ⁻¹' D
  have hD : MeasurableSet D := hB.inter (measurable_loeb_coset U hU H hH b)
  have hmap := loebMeasurePreserving_sub_left U hU (a + b + k)
  have hT : MeasurableSet T := hD.preimage hmap.measurable
  have hTm : μ T = μ D := hmap.measure_preimage hD.nullMeasurableSet
  have hTsub : T ⊆ a +ᵥ (H : Set G) := by
    intro t ht
    obtain ⟨h, hh, heq⟩ := ht.2
    refine ⟨k - h, H.sub_mem hk hh, ?_⟩
    change a + (k - h) = t
    change b + h = a + b + k - t at heq
    calc
      a + (k - h) = (a + b + k) - (b + h) := by abel
      _ = t := by rw [heq]; abel
  have hsum' : μ (a +ᵥ (H : Set G)) < μ S + μ T := by
    rw [loebMeasure_coset U hU H a, hTm]
    exact hsum
  have hover := measure_inter_pos_of_sum_gt μ (a +ᵥ (H : Set G)) S T
    inter_subset_right hTsub hT hsum'
  obtain ⟨t, ht⟩ := nonempty_of_measure_ne_zero hover.ne'
  exact ⟨t, ht.1.1, a + b + k - t, ht.2.1, by simp [vadd_eq_add]⟩

theorem loeb_coset_section_measure_le
    (U : Ultrafilter ℕ) (hU : (U : Filter ℕ) ≤ atTop)
    (H : AddSubgroup ((U : Filter ℕ).Product X))
    (hH : MeasurableSet (H : Set ((U : Filter ℕ).Product X)))
    (A : Set ((U : Filter ℕ).Product X)) (a : (U : Filter ℕ).Product X) (ha : a ∈ A) :
    loebMeasure U hU A + loebMeasure U hU (H : Set ((U : Filter ℕ).Product X)) ≤
      loebMeasure U hU (A + (H : Set ((U : Filter ℕ).Product X))) +
        loebMeasure U hU (A ∩ (a +ᵥ (H : Set ((U : Filter ℕ).Product X)))) := by
  let G := (U : Filter ℕ).Product X
  let μ := loebMeasure (X := X) U hU
  have hsub : A ∪ (a +ᵥ (H : Set G)) ⊆ A + (H : Set G) := by
    rintro x (hx | hx)
    · exact ⟨x, hx, 0, H.zero_mem, add_zero x⟩
    · obtain ⟨k, hk, rfl⟩ := hx
      exact ⟨a, ha, k, hk, rfl⟩
  calc
    μ A + μ (H : Set G) = μ A + μ (a +ᵥ (H : Set G)) := by rw [loebMeasure_coset]
    _ = μ (A ∪ (a +ᵥ (H : Set G))) + μ (A ∩ (a +ᵥ (H : Set G))) :=
      (measure_union_add_inter A (measurable_loeb_coset U hU H hH a)).symm
    _ ≤ μ (A + (H : Set G)) + μ (A ∩ (a +ᵥ (H : Set G))) :=
      add_le_add (measure_mono hsub) le_rfl

theorem loeb_coset_sections_gt_of_saturated_deficit
    (U : Ultrafilter ℕ) (hU : (U : Filter ℕ) ≤ atTop)
    (H : AddSubgroup ((U : Filter ℕ).Product X))
    (hH : MeasurableSet (H : Set ((U : Filter ℕ).Product X)))
    (A B : Set ((U : Filter ℕ).Product X))
    (hsum : loebMeasure U hU (A + (H : Set ((U : Filter ℕ).Product X))) +
        loebMeasure U hU (B + (H : Set ((U : Filter ℕ).Product X))) <
      loebMeasure U hU A + loebMeasure U hU B +
        loebMeasure U hU (H : Set ((U : Filter ℕ).Product X)))
    (a b : (U : Filter ℕ).Product X) (ha : a ∈ A) (hb : b ∈ B) :
    loebMeasure U hU (H : Set ((U : Filter ℕ).Product X)) <
      loebMeasure U hU (A ∩ (a +ᵥ (H : Set ((U : Filter ℕ).Product X)))) +
        loebMeasure U hU (B ∩ (b +ᵥ (H : Set ((U : Filter ℕ).Product X)))) := by
  let G := (U : Filter ℕ).Product X
  let μ := loebMeasure (X := X) U hU
  letI : IsProbabilityMeasure μ := isProbabilityMeasure_loebMeasure U hU
  have hAineq := loeb_coset_section_measure_le U hU H hH A a ha
  have hBineq := loeb_coset_section_measure_le U hU H hH B b hb
  change μ A + μ (H : Set G) ≤ μ (A + (H : Set G)) + μ (A ∩ (a +ᵥ (H : Set G))) at hAineq
  change μ B + μ (H : Set G) ≤ μ (B + (H : Set G)) + μ (B ∩ (b +ᵥ (H : Set G))) at hBineq
  change μ (A + (H : Set G)) + μ (B + (H : Set G)) < μ A + μ B + μ (H : Set G) at hsum
  have hAr := ENNReal.toReal_mono (by finiteness) hAineq
  have hBr := ENNReal.toReal_mono (by finiteness) hBineq
  have hSr := (ENNReal.toReal_lt_toReal (by finiteness) (by finiteness)).mpr hsum
  rw [ENNReal.toReal_add (measure_ne_top μ _) (measure_ne_top μ _),
    ENNReal.toReal_add (measure_ne_top μ _) (measure_ne_top μ _)] at hAr
  rw [ENNReal.toReal_add (measure_ne_top μ _) (measure_ne_top μ _),
    ENNReal.toReal_add (measure_ne_top μ _) (measure_ne_top μ _)] at hBr
  rw [ENNReal.toReal_add (measure_ne_top μ _) (measure_ne_top μ _),
    ENNReal.toReal_add (by finiteness) (measure_ne_top μ _),
    ENNReal.toReal_add (measure_ne_top μ _) (measure_ne_top μ _)] at hSr
  apply (ENNReal.toReal_lt_toReal (measure_ne_top μ _) (by finiteness)).mp
  rw [ENNReal.toReal_add (measure_ne_top μ _) (measure_ne_top μ _)]
  linarith

theorem loeb_add_periodic_of_saturated_deficit
    (U : Ultrafilter ℕ) (hU : (U : Filter ℕ) ≤ atTop)
    (H : AddSubgroup ((U : Filter ℕ).Product X))
    (hH : MeasurableSet (H : Set ((U : Filter ℕ).Product X)))
    (A B : Set ((U : Filter ℕ).Product X)) (hB : MeasurableSet B)
    (hsum : loebMeasure U hU (A + (H : Set ((U : Filter ℕ).Product X))) +
        loebMeasure U hU (B + (H : Set ((U : Filter ℕ).Product X))) <
      loebMeasure U hU A + loebMeasure U hU B +
        loebMeasure U hU (H : Set ((U : Filter ℕ).Product X))) :
    (A + B) + (H : Set ((U : Filter ℕ).Product X)) = A + B := by
  apply subset_antisymm
  · rintro x ⟨c, ⟨a, ha, b, hb, rfl⟩, k, hk, rfl⟩
    exact loeb_coset_subset_add_of_measure_sum_gt U hU H hH A B hB a b
      (loeb_coset_sections_gt_of_saturated_deficit U hU H hH A B hsum a b ha hb)
      ⟨k, hk, rfl⟩
  · intro x hx
    exact ⟨x, hx, 0, H.zero_mem, add_zero x⟩

end Erdos335.Loeb

end
