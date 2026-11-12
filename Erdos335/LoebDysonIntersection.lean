import Erdos335.LoebQuasiPeriodicLifting
import Erdos335.LoebFullCosetPeriod

/-!
# The overlap in a critical Dyson transform

For a nonextendible pair, a positive period of the transformed sum makes
the overlap A intersect B essentially periodic. This is Claim 1 in
Griesmer's Lemma 5.20, in the cyclic Loeb setting.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Filter Set Topology MeasureTheory
open scoped Pointwise ENNReal

noncomputable section

namespace Erdos335.Loeb

local instance dysonIntersectionLoebSpace (U : Ultrafilter ℕ) (q : ℕ → ℕ+) :
    MeasurableSpace ((U : Filter ℕ).Product (fun n => ZMod (q n : ℕ))) := loebMeasurableSpace U

theorem loeb_nonextendible_dyson_overlap_periodic
    (U : Ultrafilter ℕ) (hU : (U : Filter ℕ) ≤ atTop) (q : ℕ → ℕ+)
    (A B : Set ((U : Filter ℕ).Product (fun n => ZMod (q n : ℕ))))
    (H : AddSubgroup ((U : Filter ℕ).Product (fun n => ZMod (q n : ℕ))))
    (hAm : MeasurableSet A) (hBm : MeasurableSet B)
    (hHm : MeasurableSet (H : Set ((U : Filter ℕ).Product (fun n => ZMod (q n : ℕ)))))
    (hHpos : 0 < loebMeasure (X := fun n => ZMod (q n : ℕ)) U hU (H : Set _))
    (hne : MeasureNonextendible (loebMeasure U hU) (internalInnerMeasure U hU) A B)
    (hperiod : ((A ∪ B) + (A ∩ B)) + (H : Set _) = (A ∪ B) + (A ∩ B)) :
    loebMeasure U hU (((A ∩ B) + (H : Set _)) \ (A ∩ B)) = 0 := by
  let G := (U : Filter ℕ).Product (fun n => ZMod (q n : ℕ))
  let μ := loebMeasure (X := fun n => ZMod (q n : ℕ)) U hU
  have hTsub : (A ∪ B) + (A ∩ B) ⊆ A + B := by
    rintro z ⟨u, (hu | hu), v, hv, rfl⟩
    · exact ⟨u, hu, v, hv.2, rfl⟩
    · exact ⟨v, hv.1, u, hu, add_comm _ _⟩
  apply loeb_essential_period_of_full_cosets U hU q H hHm hHpos (A ∩ B)
  intro x hx
  have habsorb (S : Set G) (hS : S ⊆ A ∪ B) :
      (x +ᵥ (H : Set G)) + S ⊆ A + B := by
    rintro z ⟨y, ⟨k, hk, hky⟩, s, hs, rfl⟩
    have hT : (s + x) + k ∈ ((A ∪ B) + (A ∩ B)) + (H : Set G) :=
      ⟨s + x, ⟨s, hS hs, x, hx, rfl⟩, k, hk, rfl⟩
    rw [hperiod] at hT
    have heq : (s + x) + k = y + s := by
      change x + k = y at hky
      rw [← hky]
      abel
    have hz := hTsub hT
    change (s + x) + k ∈ A + B at hz
    rw [heq] at hz
    exact hz
  have hAzero : μ ((x +ᵥ (H : Set G)) \ A) = 0 :=
    loeb_nonextendible_absorbed_coset U hU H A B x hHm hAm hBm hne
      (habsorb B subset_union_right).eventuallySubset
  have hBzero : μ ((x +ᵥ (H : Set G)) \ B) = 0 := by
    apply loeb_nonextendible_absorbed_coset U hU H B A x hHm hBm hAm hne.swap
    simpa only [add_comm B A] using (habsorb A subset_union_left).eventuallySubset
  have hsub : (x +ᵥ (H : Set G)) \ (A ∩ B) ⊆
      ((x +ᵥ (H : Set G)) \ A) ∪ ((x +ᵥ (H : Set G)) \ B) := by
    rintro z ⟨hz, hout⟩
    by_cases hza : z ∈ A
    · exact Or.inr ⟨hz, fun hzb => hout ⟨hza, hzb⟩⟩
    · exact Or.inl ⟨hz, hza⟩
  apply measure_mono_null hsub
  apply nonpos_iff_eq_zero.mp
  calc
    μ (((x +ᵥ (H : Set G)) \ A) ∪ ((x +ᵥ (H : Set G)) \ B)) ≤
        μ ((x +ᵥ (H : Set G)) \ A) + μ ((x +ᵥ (H : Set G)) \ B) := measure_union_le _ _
    _ = 0 := by rw [hAzero, hBzero, add_zero]

end Erdos335.Loeb

end
