import Erdos335.LoebCosetSums

/-!
# The full background of a critical-pair decomposition

When a single coset section accounts for the entire critical deficit,
the other input and the complementary background are periodic in measure.
These identities are used in the reducible equality case.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Filter Set Topology MeasureTheory
open scoped ENNReal Pointwise

noncomputable section

namespace Erdos335.Loeb

theorem sdiff_coset_add_subgroup
    {G : Type*} [AddCommGroup G] (A : Set G) (H : AddSubgroup G) (a : G) :
    (A \ (a +ᵥ (H : Set G))) + (H : Set G) = (A + (H : Set G)) \ (a +ᵥ (H : Set G)) := by
  apply subset_antisymm
  · rintro x ⟨y, ⟨hy, hyn⟩, k, hk, rfl⟩
    refine ⟨⟨y, hy, k, hk, rfl⟩, ?_⟩
    rintro ⟨l, hl, heq⟩
    apply hyn
    refine ⟨l - k, H.sub_mem hl hk, ?_⟩
    change a + l = y + k at heq
    change a + (l - k) = y
    calc
      a + (l - k) = (a + l) - k := by abel
      _ = y := by rw [heq]; simp
  · rintro x ⟨⟨y, hy, k, hk, rfl⟩, hxn⟩
    refine ⟨y, ⟨hy, ?_⟩, k, hk, rfl⟩
    rintro ⟨l, hl, heq⟩
    apply hxn
    refine ⟨l + k, H.add_mem hl hk, ?_⟩
    change a + l = y at heq
    change a + (l + k) = y + k
    rw [← heq]
    abel

variable {X : ℕ → Type*} [∀ n, AddCommGroup (X n)] [∀ n, Fintype (X n)]

local instance criticalBackgroundLoebSpace (U : Ultrafilter ℕ) :
    MeasurableSpace ((U : Filter ℕ).Product X) := loebMeasurableSpace U

theorem loeb_critical_background_periodic
    (U : Ultrafilter ℕ) (hU : (U : Filter ℕ) ≤ atTop)
    (H : AddSubgroup ((U : Filter ℕ).Product X))
    (hH : MeasurableSet (H : Set ((U : Filter ℕ).Product X)))
    (A B : Set ((U : Filter ℕ).Product X)) (hAm : MeasurableSet A) (hBm : MeasurableSet B)
    (a : (U : Filter ℕ).Product X) (ha : a ∈ A)
    (hid : loebMeasure U hU (A + (H : Set ((U : Filter ℕ).Product X))) +
        loebMeasure U hU (B + (H : Set ((U : Filter ℕ).Product X))) =
      loebMeasure U hU (A + B) + loebMeasure U hU (H : Set ((U : Filter ℕ).Product X)))
    (hactive : loebMeasure U hU A + loebMeasure U hU B = loebMeasure U hU (A + B) +
      loebMeasure U hU (A ∩ (a +ᵥ (H : Set ((U : Filter ℕ).Product X))))) :
    loebMeasure U hU ((B + (H : Set ((U : Filter ℕ).Product X))) \ B) = 0 ∧
      loebMeasure U hU (((A \ (a +ᵥ (H : Set ((U : Filter ℕ).Product X)))) +
        (H : Set ((U : Filter ℕ).Product X))) \ (A \ (a +ᵥ (H : Set ((U : Filter ℕ).Product X))))) = 0 := by
  let G := (U : Filter ℕ).Product X
  let μ := loebMeasure (X := X) U hU
  letI : IsProbabilityMeasure μ := isProbabilityMeasure_loebMeasure U hU
  let C := a +ᵥ (H : Set G)
  have hCm : MeasurableSet C := measurable_loeb_coset U hU H hH a
  have hAineq := loeb_coset_section_measure_le U hU H hH A a ha
  have hBsub : B ⊆ B + (H : Set G) := by
    intro x hx
    exact ⟨x, hx, 0, H.zero_mem, add_zero x⟩
  have hBineq := measure_mono (μ := μ) hBsub
  have hAr := ENNReal.toReal_mono (by finiteness) hAineq
  rw [ENNReal.toReal_add (measure_ne_top μ _) (measure_ne_top μ _),
    ENNReal.toReal_add (measure_ne_top μ _) (measure_ne_top μ _)] at hAr
  have hBr := ENNReal.toReal_mono (by finiteness) hBineq
  have hIr := congrArg ENNReal.toReal hid
  rw [ENNReal.toReal_add (measure_ne_top μ _) (measure_ne_top μ _),
    ENNReal.toReal_add (measure_ne_top μ _) (measure_ne_top μ _)] at hIr
  have hDr := congrArg ENNReal.toReal hactive
  rw [ENNReal.toReal_add (measure_ne_top μ _) (measure_ne_top μ _),
    ENNReal.toReal_add (measure_ne_top μ _) (measure_ne_top μ _)] at hDr
  have hBmass : μ (B + (H : Set G)) = μ B := by
    apply le_antisymm _ hBineq
    apply (ENNReal.toReal_le_toReal (measure_ne_top μ _) (measure_ne_top μ _)).mp
    linarith
  have hCsub : C ⊆ A + (H : Set G) := by
    rintro x ⟨k, hk, rfl⟩
    exact ⟨a, ha, k, hk, rfl⟩
  have hwhole : μ (A + (H : Set G)) = μ ((A + (H : Set G)) \ C) + μ (H : Set G) := by
    have hp := measure_sdiff_add_inter (μ := μ) (A + (H : Set G)) hCm
    rw [inter_eq_right.mpr hCsub, loebMeasure_coset] at hp
    exact hp.symm
  have hpart : μ A = μ (A \ C) + μ (A ∩ C) :=
    (measure_sdiff_add_inter A hCm).symm
  have hWr := congrArg ENNReal.toReal hwhole
  rw [ENNReal.toReal_add (measure_ne_top μ _) (measure_ne_top μ _)] at hWr
  have hPr := congrArg ENNReal.toReal hpart
  rw [ENNReal.toReal_add (measure_ne_top μ _) (measure_ne_top μ _)] at hPr
  have hBmassR := congrArg ENNReal.toReal hBmass
  have hbackground : μ (((A \ C) + (H : Set G))) = μ (A \ C) := by
    rw [sdiff_coset_add_subgroup]
    apply le_antisymm
    · apply (ENNReal.toReal_le_toReal (measure_ne_top μ _) (measure_ne_top μ _)).mp
      change (μ ((A + (H : Set G)) \ C)).toReal ≤ (μ (A \ C)).toReal
      change (μ A).toReal + (μ B).toReal = (μ (A + B)).toReal + (μ (A ∩ C)).toReal at hDr
      linarith
    · apply measure_mono
      rintro x ⟨hxA, hxC⟩
      exact ⟨⟨x, hxA, 0, H.zero_mem, add_zero x⟩, hxC⟩
  constructor
  · rw [measure_sdiff hBsub hBm.nullMeasurableSet (measure_ne_top μ _), hBmass, tsub_self]
  · have hsub : A \ C ⊆ (A \ C) + (H : Set G) := by
      intro x hx
      exact ⟨x, hx, 0, H.zero_mem, add_zero x⟩
    rw [measure_sdiff hsub (hAm.diff hCm).nullMeasurableSet (measure_ne_top μ _), hbackground, tsub_self]

end Erdos335.Loeb

end
