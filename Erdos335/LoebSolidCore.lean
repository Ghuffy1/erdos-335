import Erdos335.LoebFiniteCosetCover

/-!
# Full-measure solid cores at a positive finite period

Deleting the null sections of the finitely many occupied cosets leaves
a measurable set with positive measure in each coset it meets.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Filter Set Topology MeasureTheory
open scoped Pointwise ENNReal

noncomputable section

namespace Erdos335.Loeb

local instance solidCoreLoebSpace (U : Ultrafilter ℕ) (q : ℕ → ℕ+) :
    MeasurableSpace ((U : Filter ℕ).Product (fun n => ZMod (q n : ℕ))) := loebMeasurableSpace U

theorem exists_loeb_solid_full_measure_subset
    (U : Ultrafilter ℕ) (hU : (U : Filter ℕ) ≤ atTop) (q : ℕ → ℕ+)
    (H : AddSubgroup ((U : Filter ℕ).Product (fun n => ZMod (q n : ℕ))))
    (hHm : MeasurableSet (H : Set ((U : Filter ℕ).Product (fun n => ZMod (q n : ℕ)))))
    (hHpos : 0 < loebMeasure (X := fun n => ZMod (q n : ℕ)) U hU (H : Set _))
    (A : Set ((U : Filter ℕ).Product (fun n => ZMod (q n : ℕ)))) (hAm : MeasurableSet A) :
    ∃ A₀ : Set ((U : Filter ℕ).Product (fun n => ZMod (q n : ℕ))),
      MeasurableSet A₀ ∧ A₀ ⊆ A ∧ loebMeasure U hU A₀ = loebMeasure U hU A ∧
      ∀ a ∈ A₀, 0 < loebMeasure U hU (A₀ ∩ (a +ᵥ (H : Set _))) := by
  classical
  let G := (U : Filter ℕ).Product (fun n => ZMod (q n : ℕ))
  let μ := loebMeasure (X := fun n => ZMod (q n : ℕ)) U hU
  letI : IsProbabilityMeasure μ := isProbabilityMeasure_loebMeasure U hU
  obtain ⟨R, _, hcover⟩ := loeb_exists_finite_coset_cover U hU q H hHm hHpos A
  let badSection (r : R) : Set G :=
    if μ (A ∩ ((r : G) +ᵥ (H : Set G))) = 0 then A ∩ ((r : G) +ᵥ (H : Set G)) else ∅
  let bad : Set G := ⋃ r : R, badSection r
  have hbadSectionm (r : R) : MeasurableSet (badSection r) := by
    dsimp only [badSection]
    split_ifs
    · exact hAm.inter (measurable_loeb_coset U hU H hHm r)
    · exact MeasurableSet.empty
  have hbadm : MeasurableSet bad := MeasurableSet.iUnion hbadSectionm
  have hbadzero : μ bad = 0 := by
    apply measure_iUnion_null
    intro r
    dsimp only [badSection]
    split_ifs with h
    · exact h
    · exact measure_empty
  let A₀ := A \ bad
  have hA₀m : MeasurableSet A₀ := hAm.diff hbadm
  have hsub : A₀ ⊆ A := sdiff_subset
  have hmissing : μ (A \ A₀) = 0 := by
    apply measure_mono_null _ hbadzero
    intro x hx
    by_contra hn
    exact hx.2 ⟨hx.1, hn⟩
  have hAE : A₀ =ᵐ[μ] A := hsub.eventuallySubset.antisymm (ae_le_set.mpr hmissing)
  refine ⟨A₀, hA₀m, hsub, measure_congr hAE, ?_⟩
  intro a ha
  have haCover : a ∈ (R : Set G) + (H : Set G) := by
    rw [← hcover]
    exact ⟨a, ha.1, 0, H.zero_mem, add_zero a⟩
  obtain ⟨r, hr, k, hk, hrk⟩ := haCover
  have hsection : μ (A ∩ (r +ᵥ (H : Set G))) ≠ 0 := by
    intro hz
    apply ha.2
    apply mem_iUnion.mpr
    refine ⟨⟨r, hr⟩, ?_⟩
    dsimp only [badSection]
    rw [if_pos hz]
    exact ⟨ha.1, k, hk, hrk⟩
  have hcoset : a +ᵥ (H : Set G) = r +ᵥ (H : Set G) := by
    apply subset_antisymm
    · rintro x ⟨l, hl, hlx⟩
      refine ⟨k + l, H.add_mem hk hl, ?_⟩
      change r + k = a at hrk
      change a + l = x at hlx
      change r + (k + l) = x
      rw [← add_assoc, hrk, hlx]
    · rintro x ⟨l, hl, hlx⟩
      refine ⟨l - k, H.sub_mem hl hk, ?_⟩
      change r + k = a at hrk
      change r + l = x at hlx
      change a + (l - k) = x
      rw [← hrk, ← hlx]
      abel
  have hinter : A₀ ∩ (a +ᵥ (H : Set G)) =ᵐ[μ] A ∩ (a +ᵥ (H : Set G)) := by
    filter_upwards [hAE] with x hx
    simp only [mem_inter_iff, hx]
  rw [measure_congr hinter, hcoset]
  simpa using (pos_iff_ne_zero.mpr hsection)

end Erdos335.Loeb

end
