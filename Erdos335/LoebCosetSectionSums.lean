import Erdos335.LoebCosetSums

/-!
# Sumset mass in fixed cosets

Nonempty sections give translation lower bounds for the corresponding
output section. Equal saturations supply nonempty sections on both sides.
-/

set_option autoImplicit false

open Filter Set Topology MeasureTheory
open scoped Pointwise

noncomputable section

namespace Erdos335.Loeb

theorem coset_section_sum_subset
    {G : Type*} [AddCommGroup G] (H : AddSubgroup G)
    (A B S : Set G) (hS : A + B ⊆ S) (a b : G) :
    (A ∩ (a +ᵥ (H : Set G))) + (B ∩ (b +ᵥ (H : Set G))) ⊆
      S ∩ ((a + b) +ᵥ (H : Set G)) := by
  rintro z ⟨x, ⟨hx, k, hk, hkx⟩, y, ⟨hy, l, hl, hly⟩, rfl⟩
  refine ⟨hS ⟨x, hx, y, hy, rfl⟩, k + l, H.add_mem hk hl, ?_⟩
  change a + k = x at hkx
  change b + l = y at hly
  change (a + b) + (k + l) = x + y
  rw [← hkx, ← hly]
  abel

theorem coset_section_nonempty_of_saturation_eq
    {G : Type*} [AddCommGroup G] (H : AddSubgroup G) (A B : Set G)
    (hsame : A + (H : Set G) = B + (H : Set G)) (a : G) (ha : a ∈ A) :
    (B ∩ (a +ᵥ (H : Set G))).Nonempty := by
  have hsat : a ∈ B + (H : Set G) := by
    rw [← hsame]
    exact ⟨a, ha, 0, H.zero_mem, add_zero a⟩
  obtain ⟨b, hb, k, hk, hka⟩ := hsat
  refine ⟨b, hb, -k, H.neg_mem hk, ?_⟩
  change b + k = a at hka
  change a + -k = b
  rw [← hka]
  abel

theorem disjoint_periodic_set_coset
    {G : Type*} [AddCommGroup G] (H : AddSubgroup G) (T : Set G)
    (hperiod : T + (H : Set G) = T) (a : G) (ha : a ∉ T) :
    Disjoint T (a +ᵥ (H : Set G)) := by
  apply Set.disjoint_left.mpr
  rintro x hx ⟨k, hk, hkx⟩
  apply ha
  have hmem : x + -k ∈ T + (H : Set G) := ⟨x, hx, -k, H.neg_mem hk, rfl⟩
  rw [hperiod] at hmem
  change a + k = x at hkx
  simpa only [← hkx, add_neg_cancel_right] using hmem

theorem disjoint_cosets_of_not_mem
    {G : Type*} [AddCommGroup G] (H : AddSubgroup G) (a b : G)
    (hb : b ∉ a +ᵥ (H : Set G)) :
    Disjoint (a +ᵥ (H : Set G)) (b +ᵥ (H : Set G)) := by
  apply Set.disjoint_left.mpr
  rintro x ⟨k, hk, hkx⟩ ⟨l, hl, hlx⟩
  apply hb
  refine ⟨k - l, H.sub_mem hk hl, ?_⟩
  change a + k = x at hkx
  change b + l = x at hlx
  change a + (k - l) = b
  calc
    a + (k - l) = (a + k) - l := by abel
    _ = b := by rw [hkx, ← hlx]; abel

variable {X : ℕ → Type*} [∀ n, AddCommGroup (X n)] [∀ n, Fintype (X n)]

local instance cosetSectionSumsLoebSpace (U : Ultrafilter ℕ) :
    MeasurableSpace ((U : Filter ℕ).Product X) := loebMeasurableSpace U

theorem loeb_section_measures_le_sum_section
    (U : Ultrafilter ℕ) (hU : (U : Filter ℕ) ≤ atTop)
    (H : AddSubgroup ((U : Filter ℕ).Product X))
    (A B S : Set ((U : Filter ℕ).Product X)) (hS : A + B ⊆ S)
    (a b : (U : Filter ℕ).Product X)
    (ha : (A ∩ (a +ᵥ (H : Set _))).Nonempty)
    (hb : (B ∩ (b +ᵥ (H : Set _))).Nonempty) :
    loebMeasure U hU (A ∩ (a +ᵥ (H : Set _))) ≤
        loebMeasure U hU (S ∩ ((a + b) +ᵥ (H : Set _))) ∧
      loebMeasure U hU (B ∩ (b +ᵥ (H : Set _))) ≤
        loebMeasure U hU (S ∩ ((a + b) +ᵥ (H : Set _))) := by
  obtain ⟨x, hx⟩ := ha
  obtain ⟨y, hy⟩ := hb
  constructor
  · have hsub : y +ᵥ (A ∩ (a +ᵥ (H : Set _))) ⊆ S ∩ ((a + b) +ᵥ (H : Set _)) := by
      rintro z ⟨w, hw, rfl⟩
      apply coset_section_sum_subset H A B S hS a b
      exact ⟨w, hw, y, hy, add_comm _ _⟩
    have hbound := measure_mono hsub (μ := loebMeasure U hU)
    rwa [show loebMeasure U hU (y +ᵥ (A ∩ (a +ᵥ (H : Set _)))) =
      loebMeasure U hU (A ∩ (a +ᵥ (H : Set _))) from loebMeasure_image_add_left U hU y _] at hbound
  · have hsub : x +ᵥ (B ∩ (b +ᵥ (H : Set _))) ⊆ S ∩ ((a + b) +ᵥ (H : Set _)) := by
      rintro z ⟨w, hw, rfl⟩
      apply coset_section_sum_subset H A B S hS a b
      exact ⟨x, hx, w, hw, rfl⟩
    have hbound := measure_mono hsub (μ := loebMeasure U hU)
    rwa [show loebMeasure U hU (x +ᵥ (B ∩ (b +ᵥ (H : Set _)))) =
      loebMeasure U hU (B ∩ (b +ᵥ (H : Set _))) from loebMeasure_image_add_left U hU x _] at hbound

end Erdos335.Loeb

end
