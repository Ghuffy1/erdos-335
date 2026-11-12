import Erdos335.LoebInnerAE
import Erdos335.QuasiPeriodicSets
import Erdos335.CompactDysonTransform

/-!
# Translation of inner measure and quasi-periodic data
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Filter Set MeasureTheory
open scoped Pointwise ENNReal

noncomputable section

namespace Erdos335.Loeb

theorem vadd_set_add_eq {G : Type*} [AddCommGroup G] (t : G) (A B : Set G) :
    (t +ᵥ A) + B = t +ᵥ (A + B) := by
  ext x
  constructor
  · rintro ⟨u, ⟨a, ha, rfl⟩, b, hb, rfl⟩
    exact ⟨a + b, ⟨a, ha, b, hb, rfl⟩, by simp only [vadd_eq_add]; abel⟩
  · rintro ⟨u, ⟨a, ha, b, hb, rfl⟩, rfl⟩
    exact ⟨t + a, ⟨a, ha, rfl⟩, b, hb, by simp only [vadd_eq_add]; abel⟩

theorem add_vadd_set_eq {G : Type*} [AddCommGroup G] (t : G) (A B : Set G) :
    A + (t +ᵥ B) = t +ᵥ (A + B) := by
  rw [add_comm A, vadd_set_add_eq, add_comm B A]

variable {X : ℕ → Type*} [∀ n, AddCommGroup (X n)] [∀ n, Fintype (X n)]

local instance translationStructureLoebSpace (U : Ultrafilter ℕ) :
    MeasurableSpace ((U : Filter ℕ).Product X) := loebMeasurableSpace U

theorem internalInnerMeasure_le_vadd
    (U : Ultrafilter ℕ) (hU : (U : Filter ℕ) ≤ atTop)
    (S : Set ((U : Filter ℕ).Product X)) (t : (U : Filter ℕ).Product X) :
    internalInnerMeasure U hU S ≤ internalInnerMeasure U hU (t +ᵥ S) := by
  conv_lhs => unfold internalInnerMeasure
  apply iSup_le
  intro D
  have hDm : MeasurableSet D.val := by
    obtain ⟨A, hA⟩ := D.property.1
    rw [← hA]
    exact measurable_internalSet U A
  have htm : MeasurableSet (t +ᵥ D.val) := by
    rw [vadd_set_eq_neg_preimage]
    exact hDm.preimage (measurable_add_left U hU (-t))
  have hsub : t +ᵥ D.val ⊆ t +ᵥ S := image_mono D.property.2
  calc
    loebMeasure U hU D.val = loebMeasure U hU (t +ᵥ D.val) :=
      (loebMeasure_image_add_left U hU t D.val).symm
    _ ≤ internalInnerMeasure U hU (t +ᵥ S) :=
      loeb_inner_measure_ge_of_ae_subset U hU _ _ htm hsub.eventuallySubset

theorem internalInnerMeasure_vadd
    (U : Ultrafilter ℕ) (hU : (U : Filter ℕ) ≤ atTop)
    (S : Set ((U : Filter ℕ).Product X)) (t : (U : Filter ℕ).Product X) :
    internalInnerMeasure U hU (t +ᵥ S) = internalInnerMeasure U hU S := by
  apply le_antisymm
  · simpa only [neg_vadd_vadd] using internalInnerMeasure_le_vadd U hU (t +ᵥ S) (-t)
  · exact internalInnerMeasure_le_vadd U hU S t

theorem loeb_vadd_congr_ae
    (U : Ultrafilter ℕ) (hU : (U : Filter ℕ) ≤ atTop)
    (S T : Set ((U : Filter ℕ).Product X)) (t : (U : Filter ℕ).Product X)
    (h : S =ᵐ[loebMeasure U hU] T) :
    t +ᵥ S =ᵐ[loebMeasure U hU] t +ᵥ T := by
  rw [vadd_set_eq_neg_preimage, vadd_set_eq_neg_preimage]
  have hmap : S =ᵐ[Measure.map (fun x => -t + x) (loebMeasure U hU)] T := by
    rw [loebMeasure_map_add_left U hU (-t)]
    exact h
  exact ae_of_ae_map (measurable_add_left U hU (-t)).aemeasurable hmap

def QuasiPeriodicDecomposition.loebTranslate
    (U : Ultrafilter ℕ) (hU : (U : Filter ℕ) ≤ atTop)
    {H : AddSubgroup ((U : Filter ℕ).Product X)} {A : Set ((U : Filter ℕ).Product X)}
    (p : QuasiPeriodicDecomposition (loebMeasure U hU) H A)
    (t : (U : Filter ℕ).Product X) :
    QuasiPeriodicDecomposition (loebMeasure U hU) H (t +ᵥ A) where
  active := t +ᵥ p.active
  background := t +ᵥ p.background
  anchor := t + p.anchor
  active_measurable := by
    rw [vadd_set_eq_neg_preimage]
    exact p.active_measurable.preimage (measurable_add_left U hU (-t))
  background_measurable := by
    rw [vadd_set_eq_neg_preimage]
    exact p.background_measurable.preimage (measurable_add_left U hU (-t))
  active_nonempty := p.active_nonempty.image _
  partition := (congrArg (fun S => t +ᵥ S) p.partition).trans (by rw [vadd_set_union])
  active_subset_coset := by
    rintro x ⟨a, ha, rfl⟩
    obtain ⟨k, hk, hka⟩ := p.active_subset_coset ha
    refine ⟨k, hk, ?_⟩
    change p.anchor + k = a at hka
    change (t + p.anchor) + k = t + a
    rw [add_assoc, hka]
  separated := by
    apply Set.disjoint_left.mpr
    rintro x ⟨u, ⟨a, ha, rfl⟩, k, hk, rfl⟩ ⟨b, hb, heq⟩
    have hab : a + k = b := by
      change t + b = (t + a) + k at heq
      exact add_left_cancel (by simpa only [add_assoc] using heq.symm)
    exact Set.disjoint_left.mp p.separated ⟨a, ha, k, hk, hab⟩ hb
  background_periodic := by
    rw [vadd_set_add_eq, ← vadd_set_sdiff]
    exact (loebMeasure_image_add_left U hU t _).trans p.background_periodic

end Erdos335.Loeb

end
