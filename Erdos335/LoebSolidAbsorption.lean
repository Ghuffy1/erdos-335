import Erdos335.LoebCosetSums

/-!
# Absorbing a solid translate into a periodic set

A translate of a set with positive measure in every occupied coset is
contained literally in a periodic set whenever it is contained almost
everywhere. Its whole coset saturation is contained as well.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Filter Set Topology MeasureTheory
open scoped ENNReal Pointwise

noncomputable section

namespace Erdos335.Loeb

variable {X : ℕ → Type*} [∀ n, AddCommGroup (X n)] [∀ n, Fintype (X n)]

local instance absorptionLoebSpace (U : Ultrafilter ℕ) :
    MeasurableSpace ((U : Filter ℕ).Product X) := loebMeasurableSpace U

theorem loeb_solid_translate_absorption
    (U : Ultrafilter ℕ) (hU : (U : Filter ℕ) ≤ atTop)
    (H : AddSubgroup ((U : Filter ℕ).Product X))
    (B C : Set ((U : Filter ℕ).Product X)) (g : (U : Filter ℕ).Product X)
    (hperiod : C + (H : Set ((U : Filter ℕ).Product X)) = C)
    (hsolid : ∀ b ∈ B,
      0 < loebMeasure U hU (B ∩ (b +ᵥ (H : Set ((U : Filter ℕ).Product X)))))
    (hnull : loebMeasure U hU (((fun x => g + x) '' B) \ C) = 0) :
    (fun x => g + x) '' (B + (H : Set ((U : Filter ℕ).Product X))) ⊆ C := by
  let G := (U : Filter ℕ).Product X
  let μ := loebMeasure (X := X) U hU
  rintro x ⟨y, ⟨b, hb, k, hk, rfl⟩, rfl⟩
  by_contra hx
  let D := B ∩ (b +ᵥ (H : Set G))
  have hsub : (fun t => g + t) '' D ⊆ ((fun t => g + t) '' B) \ C := by
    rintro z ⟨t, ⟨ht, ⟨l, hl, rfl⟩⟩, rfl⟩
    refine ⟨⟨b + l, ht, rfl⟩, ?_⟩
    intro hz
    have hc : g + (b + k) ∈ C + (H : Set G) :=
      ⟨g + (b + l), hz, k - l, H.sub_mem hk hl, by simp [vadd_eq_add]; abel⟩
    rw [hperiod] at hc
    exact hx hc
  have hzero : μ ((fun t => g + t) '' D) = 0 := measure_mono_null hsub hnull
  rw [loebMeasure_image_add_left U hU] at hzero
  exact (hsolid b hb).ne' hzero

end Erdos335.Loeb

end
