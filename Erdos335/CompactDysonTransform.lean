import Mathlib.MeasureTheory.Group.Measure
import Mathlib.MeasureTheory.Measure.Basic
import Mathlib.Tactic

/-!
# Dyson transforms for measurable subsets of a group

These are the set and measure identities in Griesmer's compact inverse
proof, equations (5.41) and (5.42). Mathlib's finite-set counterpart is
`Finset.addDysonETransform`.
-/

set_option autoImplicit false

open Set MeasureTheory
open scoped Pointwise ENNReal

namespace Erdos335.Loeb

variable {G : Type*} [AddCommGroup G]

def dysonGroupLeft (A B : Set G) (e : G) : Set G := A ∪ (e +ᵥ B)

def dysonGroupRight (A B : Set G) (e : G) : Set G :=
  B ∩ (fun x => e + x) ⁻¹' A

theorem dysonGroup_sum_subset (A B : Set G) (e : G) :
    dysonGroupLeft A B e + dysonGroupRight A B e ⊆ A + B := by
  rintro z ⟨x, hx, y, hy, rfl⟩
  rcases hx with hxA | ⟨b, hb, rfl⟩
  · exact ⟨x, hxA, y, hy.1, rfl⟩
  · exact ⟨e + y, hy.2, b, hb, by simp only [vadd_eq_add]; ac_rfl⟩

theorem dysonGroup_translate_right (A B : Set G) (e : G) :
    e +ᵥ dysonGroupRight A B e = A ∩ (e +ᵥ B) := by
  ext x
  constructor
  · rintro ⟨b, hb, rfl⟩
    exact ⟨hb.2, ⟨b, hb.1, rfl⟩⟩
  · rintro ⟨hx, b, hb, rfl⟩
    exact ⟨b, ⟨hb, hx⟩, rfl⟩

theorem vadd_set_eq_neg_preimage (S : Set G) (e : G) :
    e +ᵥ S = (fun x => -e + x) ⁻¹' S := by
  ext x
  constructor
  · rintro ⟨s, hs, rfl⟩
    simpa only [mem_preimage, vadd_eq_add, neg_add_cancel_left] using hs
  · intro hx
    exact ⟨-e + x, hx, by simp [vadd_eq_add]⟩

theorem measurableSet_dysonGroup
    [MeasurableSpace G] [MeasurableAdd₂ G]
    (A B : Set G) (hA : MeasurableSet A) (hB : MeasurableSet B) (e : G) :
    MeasurableSet (dysonGroupLeft A B e) ∧ MeasurableSet (dysonGroupRight A B e) := by
  constructor
  · unfold dysonGroupLeft
    rw [vadd_set_eq_neg_preimage]
    exact hA.union (hB.preimage (measurable_const.add measurable_id))
  · exact hB.inter (hA.preimage (measurable_const.add measurable_id))

theorem dysonGroup_measure_identity
    [MeasurableSpace G] [MeasurableAdd₂ G]
    (μ : Measure G) [μ.IsAddLeftInvariant]
    (A B : Set G) (hB : MeasurableSet B) (e : G) :
    μ (dysonGroupLeft A B e) + μ (dysonGroupRight A B e) = μ A + μ B := by
  have htranslate (S : Set G) : μ (e +ᵥ S) = μ S := by
    rw [vadd_set_eq_neg_preimage]
    exact measure_preimage_add μ (-e) S
  have hmeas : MeasurableSet (e +ᵥ B) := by
    rw [vadd_set_eq_neg_preimage]
    exact hB.preimage (measurable_const.add measurable_id)
  have h := measure_union_add_inter (μ := μ) A hmeas
  rw [← dysonGroup_translate_right, htranslate, htranslate] at h
  exact h

end Erdos335.Loeb
