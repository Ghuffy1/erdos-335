import Erdos335.LoebEmbeddingMeasurability
import Erdos335.LoebSubgroup
import Erdos335.LoebEssentialStabilizer

/-!
# Essential periods under positive internal embeddings
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter MeasureTheory
open scoped ENNReal Pointwise symmDiff

noncomputable section

namespace Erdos335.Loeb

theorem image_vadd_addHom {G K : Type*} [AddCommGroup G] [AddCommGroup K]
    (e : G →+ K) (t : G) (S : Set G) :
    e '' (t +ᵥ S) = e t +ᵥ (e '' S) := by
  ext y
  constructor
  · rintro ⟨x, ⟨s, hs, rfl⟩, rfl⟩
    exact ⟨e s, ⟨s, hs, rfl⟩, (e.map_add t s).symm⟩
  · rintro ⟨x, ⟨s, hs, rfl⟩, rfl⟩
    exact ⟨t + s, ⟨s, hs, rfl⟩, e.map_add t s⟩

variable {X Y : ℕ → Type*} [∀ n, AddCommGroup (X n)] [∀ n, AddCommGroup (Y n)]
variable [∀ n, Finite (X n)] [∀ n, Finite (Y n)]

local instance embeddingPeriodSourceSpace (U : Ultrafilter ℕ) :
    MeasurableSpace ((U : Filter ℕ).Product X) := loebMeasurableSpace U
local instance embeddingPeriodTargetSpace (U : Ultrafilter ℕ) :
    MeasurableSpace ((U : Filter ℕ).Product Y) := loebMeasurableSpace U

theorem loeb_image_ae_eq_iff
    (U : Ultrafilter ℕ) (hU : (U : Filter ℕ) ≤ atTop)
    (p : ∀ n, X n →+ Y n) (hp : ∀ n, Function.Injective (p n))
    (hpos : 0 < loebMeasure U hU (Set.range (productMapHom (U : Filter ℕ) p)))
    (A B : Set ((U : Filter ℕ).Product X)) :
    productMapHom (U : Filter ℕ) p '' A =ᵐ[loebMeasure U hU]
      productMapHom (U : Filter ℕ) p '' B ↔ A =ᵐ[loebMeasure U hU] B := by
  let e := productMapHom (U : Filter ℕ) p
  have he : Function.Injective (productMapHom (U : Filter ℕ) p) :=
    productMap_injective (U : Filter ℕ) (fun n => p n) hp
  rw [← measure_symmDiff_eq_zero_iff, ← measure_symmDiff_eq_zero_iff,
    ← Set.image_symmDiff he A B]
  change loebMeasure U hU (productMap (U : Filter ℕ) (fun n => p n) '' (A ∆ B)) = 0 ↔ _
  rw [loebMeasure_image_injection U hU (fun n => p n) hp hpos]
  have hne : loebMeasure U hU (Set.range (productMap (U : Filter ℕ) (fun n => p n))) ≠ 0 := hpos.ne'
  simp only [mul_eq_zero, hne, false_or]

theorem loeb_no_positive_periods_of_internal_embedding
    (U : Ultrafilter ℕ) (hU : (U : Filter ℕ) ≤ atTop)
    (p : ∀ n, X n →+ Y n) (hp : ∀ n, Function.Injective (p n))
    (hpos : 0 < loebMeasure U hU (Set.range (productMapHom (U : Filter ℕ) p)))
    (S : Set ((U : Filter ℕ).Product X))
    (hno : ∀ H : AddSubgroup ((U : Filter ℕ).Product Y),
      MeasurableSet (H : Set ((U : Filter ℕ).Product Y)) →
      0 < loebMeasure U hU (H : Set ((U : Filter ℕ).Product Y)) →
      ¬ ∀ t ∈ H, t +ᵥ (productMapHom (U : Filter ℕ) p '' S) =ᵐ[loebMeasure U hU]
        productMapHom (U : Filter ℕ) p '' S) :
    ∀ H : AddSubgroup ((U : Filter ℕ).Product X),
      MeasurableSet (H : Set ((U : Filter ℕ).Product X)) →
      0 < loebMeasure U hU (H : Set ((U : Filter ℕ).Product X)) →
      ¬ ∀ t ∈ H, t +ᵥ S =ᵐ[loebMeasure U hU] S := by
  let e := productMapHom (U : Filter ℕ) p
  have he := measurableEmbedding_positive_internal_injection U hU (fun n => p n) hp hpos
  intro H hHm hHpos hperiod
  have hmapm : MeasurableSet ((H.map e) : Set ((U : Filter ℕ).Product Y)) :=
    he.measurableSet_image.mpr hHm
  have hmappos : 0 < loebMeasure U hU ((H.map e) : Set ((U : Filter ℕ).Product Y)) := by
    change 0 < loebMeasure U hU
      (productMap (U : Filter ℕ) (fun n => p n) '' (H : Set ((U : Filter ℕ).Product X)))
    rw [loebMeasure_image_injection U hU (fun n => p n) hp hpos]
    exact ENNReal.mul_pos hpos.ne' hHpos.ne'
  apply hno (H.map e) hmapm hmappos
  intro y hy
  obtain ⟨x, hx, rfl⟩ := hy
  have h := (loeb_image_ae_eq_iff U hU p hp hpos (x +ᵥ S) S).mpr (hperiod x hx)
  rwa [image_vadd_addHom] at h

end Erdos335.Loeb

end
