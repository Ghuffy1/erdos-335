import Erdos335.LoebEqualityPeriod

/-!
# Background sums remain in the critical core

A full background coset cannot contribute to the partially filled
exceptional output of a nonperiodic equality extension.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Filter Set Topology MeasureTheory
open scoped ENNReal Pointwise

noncomputable section

namespace Erdos335.Loeb

local instance backgroundSumsLoebSpace (U : Ultrafilter ℕ) (q : ℕ → ℕ+) :
    MeasurableSpace ((U : Filter ℕ).Product (fun n => ZMod (q n : ℕ))) := loebMeasurableSpace U

theorem loeb_equality_extension_background_add_subset
    (U : Ultrafilter ℕ) (hU : (U : Filter ℕ) ≤ atTop) (q : ℕ → ℕ+)
    (A B₀ B : Set ((U : Filter ℕ).Product (fun n => ZMod (q n : ℕ))))
    (hAm : MeasurableSet A) (hB₀m : MeasurableSet B₀)
    (hApos : 0 < loebMeasure U hU A) (hB₀pos : 0 < loebMeasure U hU B₀)
    (hB₀B : B₀ ⊆ B)
    (hcore : internalInnerMeasure U hU (A + B₀) < loebMeasure U hU A + loebMeasure U hU B₀)
    (hequality : internalInnerMeasure U hU (A + B) = loebMeasure U hU A + loebMeasure U hU B₀)
    (a : (U : Filter ℕ).Product (fun n => ZMod (q n : ℕ))) :
    let G := (U : Filter ℕ).Product (fun n => ZMod (q n : ℕ))
    let H := AddAction.stabilizer G (A + B₀)
    loebMeasure U hU A + loebMeasure U hU B₀ = loebMeasure U hU (A + B₀) +
        loebMeasure U hU (A ∩ (a +ᵥ (H : Set G))) →
      loebMeasure U hU (A ∩ (a +ᵥ (H : Set G))) < loebMeasure U hU (H : Set G) →
      loebMeasure U hU (((A \ (a +ᵥ (H : Set G))) + (H : Set G)) \ (A \ (a +ᵥ (H : Set G)))) = 0 →
      (A \ (a +ᵥ (H : Set G))) + B ⊆ A + B₀ := by
  dsimp only
  intro hactive hpartial hperiod
  let G := (U : Filter ℕ).Product (fun n => ZMod (q n : ℕ))
  let μ := loebMeasure (X := fun n => ZMod (q n : ℕ)) U hU
  letI : IsProbabilityMeasure μ := isProbabilityMeasure_loebMeasure U hU
  let H := AddAction.stabilizer G (A + B₀)
  let A₁ := A \ (a +ᵥ (H : Set G))
  obtain ⟨hCm, hHm, _, _⟩ := loeb_measurable_kneser_identity U hU q A B₀ hAm hB₀m hApos hB₀pos hcore
  have hA₁m : MeasurableSet A₁ := hAm.diff (measurable_loeb_coset U hU H hHm a)
  rintro x ⟨c, hc, b, hb, rfl⟩
  by_contra hout
  let D := A₁ ∩ (c +ᵥ (H : Set G))
  let E := b +ᵥ D
  have hDm : MeasurableSet D := hA₁m.inter (measurable_loeb_coset U hU H hHm c)
  have hEm : MeasurableSet E := by
    have heq : E = (fun y => -b + y) ⁻¹' D := by
      ext y
      constructor
      · rintro ⟨z, hz, rfl⟩
        simpa only [mem_preimage, vadd_eq_add, neg_add_cancel_left] using hz
      · intro hy
        exact ⟨-b + y, hy, by simp [vadd_eq_add]⟩
    rw [heq]
    exact hDm.preimage (measurable_add_left U hU (-b))
  have hDmass : μ D = μ (H : Set G) :=
    loeb_measure_section_eq_of_essential_period U hU H A₁ hA₁m hperiod c hc
  have hdisj : Disjoint (A + B₀) E := by
    apply Set.disjoint_left.mpr
    rintro y hy ⟨z, ⟨hz, ⟨k, hk, rfl⟩⟩, rfl⟩
    have hfix : (-k) +ᵥ (A + B₀) = A + B₀ := H.neg_mem hk
    apply hout
    rw [← hfix]
    exact ⟨b + (c + k), hy, by simp only [vadd_eq_add]; abel⟩
  have hsub : (A + B₀) ∪ E ⊆ A + B := by
    rintro y (hy | hy)
    · exact add_subset_add (show A ⊆ A from Subset.rfl) hB₀B hy
    · obtain ⟨z, hz, rfl⟩ := hy
      exact ⟨z, hz.1.1, b, hb, add_comm z b⟩
  have hbound : μ (A + B₀) + μ (H : Set G) ≤ internalInnerMeasure U hU (A + B) := by
    calc
      μ (A + B₀) + μ (H : Set G) = μ (A + B₀) + μ E := by
        rw [show μ E = μ D from loebMeasure_image_add_left U hU b D, hDmass]
      _ = μ ((A + B₀) ∪ E) := (measure_union hdisj hEm).symm
      _ = internalInnerMeasure U hU ((A + B₀) ∪ E) :=
        (internalInnerMeasure_eq U hU _ (hCm.union hEm)).symm
      _ ≤ internalInnerMeasure U hU (A + B) := internalInnerMeasure_mono U hU hsub
  rw [hequality, hactive] at hbound
  have hle := (ENNReal.add_le_add_iff_left (measure_ne_top μ (A + B₀))).mp hbound
  exact (not_le_of_gt hpartial) hle

end Erdos335.Loeb

end
