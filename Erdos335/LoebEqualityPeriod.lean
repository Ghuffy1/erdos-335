import Erdos335.LoebExtraCoset
import Erdos335.LoebFullInner

/-!
# Nonperiodic equality extensions have a partial active coset

The critical core has a periodic background. If its exceptional input
section filled its coset, the whole output would be periodic in measure.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Filter Set Topology MeasureTheory
open scoped ENNReal Pointwise

noncomputable section

namespace Erdos335.Loeb

variable {X : ℕ → Type*} [∀ n, AddCommGroup (X n)] [∀ n, Fintype (X n)]

local instance equalityPeriodLoebSpace (U : Ultrafilter ℕ) :
    MeasurableSpace ((U : Filter ℕ).Product X) := loebMeasurableSpace U

theorem loeb_measure_section_eq_of_essential_period
    (U : Ultrafilter ℕ) (hU : (U : Filter ℕ) ≤ atTop)
    (H : AddSubgroup ((U : Filter ℕ).Product X))
    (A : Set ((U : Filter ℕ).Product X)) (hAm : MeasurableSet A)
    (hperiod : loebMeasure U hU ((A + (H : Set ((U : Filter ℕ).Product X))) \ A) = 0)
    (a : (U : Filter ℕ).Product X) (ha : a ∈ A) :
    loebMeasure U hU (A ∩ (a +ᵥ (H : Set ((U : Filter ℕ).Product X)))) =
      loebMeasure U hU (H : Set ((U : Filter ℕ).Product X)) := by
  let G := (U : Filter ℕ).Product X
  let μ := loebMeasure (X := X) U hU
  have hsub : a +ᵥ (H : Set G) ⊆ A + (H : Set G) := by
    rintro x ⟨k, hk, rfl⟩
    exact ⟨a, ha, k, hk, rfl⟩
  have hzero : μ ((a +ᵥ (H : Set G)) \ A) = 0 :=
    measure_mono_null (sdiff_subset_sdiff_left hsub) hperiod
  have hsum := measure_inter_add_sdiff (μ := μ) (a +ᵥ (H : Set G)) hAm
  rw [hzero, add_zero, loebMeasure_coset U hU H a] at hsum
  simpa only [inter_comm] using hsum

theorem loeb_nonperiodic_equality_extension_active_section
    (U : Ultrafilter ℕ) (hU : (U : Filter ℕ) ≤ atTop) (q : ℕ → ℕ+)
    (A B₀ B : Set ((U : Filter ℕ).Product (fun n => ZMod (q n : ℕ))))
    (hAm : MeasurableSet A) (hB₀m : MeasurableSet B₀)
    (hApos : 0 < loebMeasure U hU A) (hB₀pos : 0 < loebMeasure U hU B₀)
    (hB₀B : B₀ ⊆ B)
    (hcore : internalInnerMeasure U hU (A + B₀) < loebMeasure U hU A + loebMeasure U hU B₀)
    (hequality : internalInnerMeasure U hU (A + B) = loebMeasure U hU A + loebMeasure U hU B₀)
    (hnotperiod : ¬ (A + B) + (AddAction.stabilizer
      ((U : Filter ℕ).Product (fun n => ZMod (q n : ℕ))) (A + B₀) : Set _) =ᵐ[loebMeasure U hU] A + B) :
    let G := (U : Filter ℕ).Product (fun n => ZMod (q n : ℕ))
    let H := AddAction.stabilizer G (A + B₀)
    ∃ a ∈ A, ∃ b ∈ B, a + b ∉ A + B₀ ∧
      (0 < loebMeasure U hU (A ∩ (a +ᵥ (H : Set G))) ∧
        loebMeasure U hU (A ∩ (a +ᵥ (H : Set G))) < loebMeasure U hU (H : Set G)) ∧
      loebMeasure U hU A + loebMeasure U hU B₀ =
        loebMeasure U hU (A + B₀) + loebMeasure U hU (A ∩ (a +ᵥ (H : Set G))) ∧
      loebMeasure U hU ((B₀ + (H : Set G)) \ B₀) = 0 ∧
      loebMeasure U hU (((A \ (a +ᵥ (H : Set G))) + (H : Set G)) \ (A \ (a +ᵥ (H : Set G)))) = 0 := by
  let G := (U : Filter ℕ).Product (fun n => ZMod (q n : ℕ))
  let μ := loebMeasure (X := fun n => ZMod (q n : ℕ)) U hU
  let H := AddAction.stabilizer G (A + B₀)
  obtain ⟨hCm, hHm, _, _⟩ := loeb_measurable_kneser_identity U hU q A B₀ hAm hB₀m hApos hB₀pos hcore
  obtain ⟨a, ha, b, hb, hout, hactive, hBperiod, hAperiod⟩ :=
    loeb_equality_extension_periodic_backgrounds U hU q A B₀ B hAm hB₀m hApos hB₀pos hB₀B hcore hequality
  have hsectionpos : 0 < μ (A ∩ (a +ᵥ (H : Set G))) :=
    (loeb_critical_coset_masses_positive U hU q A B₀ hAm hB₀m hApos hB₀pos hcore).1 a ha
  have hsectionle : μ (A ∩ (a +ᵥ (H : Set G))) ≤ μ (H : Set G) := by
    calc
      _ ≤ μ (a +ᵥ (H : Set G)) := measure_mono inter_subset_right
      _ = _ := loebMeasure_coset U hU H a
  have hsectionlt : μ (A ∩ (a +ᵥ (H : Set G))) < μ (H : Set G) := by
    by_contra hn
    have heq := le_antisymm hsectionle (not_lt.mp hn)
    obtain ⟨g, hg, hdiff⟩ := loeb_equality_extension_extra_coset U hU q A B₀ B
      hAm hB₀m hApos hB₀pos hB₀B hcore hequality
    let S := (A + B) + (H : Set G)
    have hCsub : A + B₀ ⊆ S := by
      intro x hx
      exact ⟨x, add_subset_add (show A ⊆ A from Subset.rfl) hB₀B hx, 0, H.zero_mem, add_zero x⟩
    have hS : S = (A + B₀) ∪ (g +ᵥ (H : Set G)) := by
      rw [← hdiff]
      apply subset_antisymm
      · intro x hx
        by_cases hc : x ∈ A + B₀
        · exact Or.inl hc
        · exact Or.inr ⟨hx, hc⟩
      · rintro x (hx | hx)
        · exact hCsub hx
        · exact hx.1
    have hdisj : Disjoint (A + B₀) (g +ᵥ (H : Set G)) := by
      rw [← hdiff]
      exact disjoint_sdiff_right
    have hmass : μ S = μ (A + B₀) + μ (H : Set G) := by
      rw [hS, measure_union hdisj (measurable_loeb_coset U hU H hHm g), loebMeasure_coset]
    have hSm : MeasurableSet S := by rw [hS]; exact hCm.union (measurable_loeb_coset U hU H hHm g)
    have hfull : internalInnerMeasure U hU (A + B) = μ S := by
      rw [hequality, hactive, heq, hmass]
    have hsub : A + B ⊆ S := by
      intro x hx
      exact ⟨x, hx, 0, H.zero_mem, add_zero x⟩
    have hsame := (measurable_of_subset_full_inner U hU (A + B) S hsub hSm hfull).2
    exact hnotperiod hsame.symm
  exact ⟨a, ha, b, hb, hout, ⟨hsectionpos, hsectionlt⟩, hactive, hBperiod, hAperiod⟩

end Erdos335.Loeb

end
