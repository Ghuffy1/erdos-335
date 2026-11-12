import Erdos335.LoebInnerAE
import Erdos335.LoebCosetSums

/-!
# Nonextendible pairs and coset containment

If adjoining a coset creates no additional sumset inner measure,
nonextendibility forces that coset to be contained in the input up to a
null set. This is used in the positive-piece null-lifting argument.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Filter Set Topology MeasureTheory
open scoped ENNReal Pointwise

noncomputable section

namespace Erdos335.Loeb

def MeasureNonextendible {G : Type*} [AddCommGroup G] [MeasurableSpace G]
    (μ : Measure G) (inner : Set G → ℝ≥0∞) (A B : Set G) : Prop :=
  ∀ A' B' : Set G, MeasurableSet A' → MeasurableSet B' → A ⊆ A' → B ⊆ B' →
    inner (A' + B') = inner (A + B) → μ A' + μ B' ≤ μ A + μ B

variable {X : ℕ → Type*} [∀ n, AddCommGroup (X n)] [∀ n, Fintype (X n)]

local instance nonextendibleLoebSpace (U : Ultrafilter ℕ) :
    MeasurableSpace ((U : Filter ℕ).Product X) := loebMeasurableSpace U

theorem loeb_nonextendible_left_extension_eq
    (U : Ultrafilter ℕ) (hU : (U : Filter ℕ) ≤ atTop)
    (A B A' : Set ((U : Filter ℕ).Product X))
    (hBm : MeasurableSet B) (hA'm : MeasurableSet A') (hAA' : A ⊆ A')
    (hne : MeasureNonextendible (loebMeasure U hU) (internalInnerMeasure U hU) A B)
    (hsame : internalInnerMeasure U hU (A' + B) = internalInnerMeasure U hU (A + B)) :
    loebMeasure U hU A' = loebMeasure U hU A := by
  let μ := loebMeasure (X := X) U hU
  letI : IsProbabilityMeasure μ := isProbabilityMeasure_loebMeasure U hU
  apply le_antisymm
  · exact (ENNReal.add_le_add_iff_right (measure_ne_top μ B)).mp
      (hne A' B hA'm hBm hAA' Subset.rfl hsame)
  · exact measure_mono hAA'

theorem loeb_nonextendible_absorbed_coset
    (U : Ultrafilter ℕ) (hU : (U : Filter ℕ) ≤ atTop)
    (H : AddSubgroup ((U : Filter ℕ).Product X))
    (A B : Set ((U : Filter ℕ).Product X)) (g : (U : Filter ℕ).Product X)
    (hHm : MeasurableSet (H : Set ((U : Filter ℕ).Product X)))
    (hAm : MeasurableSet A) (hBm : MeasurableSet B)
    (hne : MeasureNonextendible (loebMeasure U hU) (internalInnerMeasure U hU) A B)
    (habsorb : (g +ᵥ (H : Set ((U : Filter ℕ).Product X))) + B ≤ᵐ[loebMeasure U hU] A + B) :
    loebMeasure U hU ((g +ᵥ (H : Set ((U : Filter ℕ).Product X))) \ A) = 0 := by
  let G := (U : Filter ℕ).Product X
  let μ := loebMeasure (X := X) U hU
  letI : IsProbabilityMeasure μ := isProbabilityMeasure_loebMeasure U hU
  let A' := A ∪ (g +ᵥ (H : Set G))
  have hA'm : MeasurableSet A' := hAm.union (measurable_loeb_coset U hU H hHm g)
  have hAA' : A ⊆ A' := subset_union_left
  have hsum : A' + B = (A + B) ∪ ((g +ᵥ (H : Set G)) + B) := union_add
  have hAE : A' + B =ᵐ[μ] A + B := by
    rw [hsum]
    filter_upwards [habsorb] with x hx
    change x ∈ (g +ᵥ (H : Set G)) + B → x ∈ A + B at hx
    apply propext
    simp only [mem_union]
    tauto
  have hmass : μ A' = μ A := loeb_nonextendible_left_extension_eq U hU A B A'
    hBm hA'm hAA' hne (internalInnerMeasure_congr_ae U hU _ _ hAE)
  have hzero : μ (A' \ A) = 0 := by
    rw [measure_sdiff hAA' hAm.nullMeasurableSet (measure_ne_top μ _), hmass, tsub_self]
  exact measure_mono_null (sdiff_subset_sdiff_left subset_union_right) hzero

end Erdos335.Loeb

end
