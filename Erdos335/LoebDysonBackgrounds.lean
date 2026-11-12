import Erdos335.LoebDysonIntersection

/-!
# Periodic background parts in the Dyson argument
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Filter Set Topology MeasureTheory
open scoped Pointwise ENNReal

noncomputable section

namespace Erdos335.Loeb

theorem complement_add_period
    {G : Type*} [AddCommGroup G] (H : AddSubgroup G) (P : Set G)
    (hP : P + (H : Set G) = P) : Pᶜ + (H : Set G) = Pᶜ := by
  apply subset_antisymm
  · rintro x ⟨p, hp, h, hh, rfl⟩ hx
    apply hp
    have hx' : p + h + -h ∈ P + (H : Set G) := ⟨p + h, hx, -h, H.neg_mem hh, rfl⟩
    rw [hP] at hx'
    simpa only [add_neg_cancel_right] using hx'
  · intro x hx
    exact ⟨x, hx, 0, H.zero_mem, add_zero x⟩

local instance dysonBackgroundLoebSpace (U : Ultrafilter ℕ) (q : ℕ → ℕ+) :
    MeasurableSpace ((U : Filter ℕ).Product (fun n => ZMod (q n : ℕ))) := loebMeasurableSpace U

theorem loeb_nonextendible_part_periodic
    (U : Ultrafilter ℕ) (hU : (U : Filter ℕ) ≤ atTop) (q : ℕ → ℕ+)
    (A B P T : Set ((U : Filter ℕ).Product (fun n => ZMod (q n : ℕ))))
    (H : AddSubgroup ((U : Filter ℕ).Product (fun n => ZMod (q n : ℕ))))
    (hAm : MeasurableSet A) (hBm : MeasurableSet B)
    (hHm : MeasurableSet (H : Set ((U : Filter ℕ).Product (fun n => ZMod (q n : ℕ)))))
    (hHpos : 0 < loebMeasure (X := fun n => ZMod (q n : ℕ)) U hU (H : Set _))
    (hne : MeasureNonextendible (loebMeasure U hU) (internalInnerMeasure U hU) A B)
    (hP : P + (H : Set _) = P) (hT : T + (H : Set _) = T)
    (hTsub : T ⊆ A + B) (hsum : (A ∩ P) + B ⊆ T) :
    loebMeasure U hU (((A ∩ P) + (H : Set _)) \ (A ∩ P)) = 0 := by
  let G := (U : Filter ℕ).Product (fun n => ZMod (q n : ℕ))
  let μ := loebMeasure (X := fun n => ZMod (q n : ℕ)) U hU
  apply loeb_essential_period_of_full_cosets U hU q H hHm hHpos (A ∩ P)
  intro x hx
  have hcoset : x +ᵥ (H : Set G) ⊆ P := by
    rintro y ⟨k, hk, rfl⟩
    have hy : x + k ∈ P + (H : Set G) := ⟨x, hx.2, k, hk, rfl⟩
    rwa [hP] at hy
  have habsorb : (x +ᵥ (H : Set G)) + B ⊆ A + B := by
    rintro y ⟨z, ⟨k, hk, hkz⟩, b, hb, rfl⟩
    have hbase : x + b ∈ T := hsum ⟨x, hx, b, hb, rfl⟩
    have hsat : (x + b) + k ∈ T + (H : Set G) := ⟨x + b, hbase, k, hk, rfl⟩
    rw [hT] at hsat
    have heq : (x + b) + k = z + b := by
      change x + k = z at hkz
      rw [← hkz]
      abel
    have hout := hTsub hsat
    change (x + b) + k ∈ A + B at hout
    rwa [heq] at hout
  have hzero : μ ((x +ᵥ (H : Set G)) \ A) = 0 :=
    loeb_nonextendible_absorbed_coset U hU H A B x hHm hAm hBm hne habsorb.eventuallySubset
  apply measure_mono_null _ hzero
  rintro y ⟨hy, hout⟩
  exact ⟨hy, fun hya => hout ⟨hya, hcoset hy⟩⟩

end Erdos335.Loeb

end
