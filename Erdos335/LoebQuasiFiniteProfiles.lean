import Erdos335.LoebProfileBounds
import Erdos335.QuasiPeriodicSets

/-!
# Finite residue profiles of a quasi-periodic decomposition
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Filter Set MeasureTheory
open scoped Pointwise ENNReal Classical

noncomputable section

namespace Erdos335.Loeb

local instance quasiFiniteProfilesLoebSpace (U : Ultrafilter ℕ) (q : ℕ → ℕ+) :
    MeasurableSpace ((U : Filter ℕ).Product (fun n => ZMod (q n : ℕ))) := loebMeasurableSpace U

theorem loeb_quasiPeriodic_residue_profile
    (U : Ultrafilter ℕ) (hU : (U : Filter ℕ) ≤ atTop) (q : ℕ → ℕ+)
    (S : Set ((U : Filter ℕ).Product (fun n => ZMod (q n : ℕ))))
    (H : AddSubgroup ((U : Filter ℕ).Product (fun n => ZMod (q n : ℕ))))
    (p : QuasiPeriodicDecomposition (loebMeasure U hU) H S)
    (h : ℕ+) (hd : ∀ᶠ n in U, (h : ℕ) ∣ (q n : ℕ))
    (hker : (finiteQuotient U (fun n => naturalCyclicProjection (q n) h)).ker = H)
    (r : ZMod (h : ℕ)) :
    loebResidueProfile U hU q h S r =
      if r = finiteQuotient U (fun n => naturalCyclicProjection (q n) h) p.anchor
        then ((h : ℕ) : ℝ) * (loebMeasure U hU p.active).toReal
      else if r ∈ (finiteQuotient U (fun n => naturalCyclicProjection (q n) h)) '' S then 1 else 0 := by
  let G := (U : Filter ℕ).Product (fun n => ZMod (q n : ℕ))
  let μ : Measure G := loebMeasure (X := fun n => ZMod (q n : ℕ)) U hU
  let φ := finiteQuotient U (fun n => naturalCyclicProjection (q n) h)
  have coset (a : G) : φ ⁻¹' {φ a} = a +ᵥ (H : Set G) :=
    (addHom_fiber_eq_coset φ a).trans
      (congrArg (fun K : AddSubgroup G => a +ᵥ (K : Set G)) hker)
  by_cases hr : r = φ p.anchor
  · rw [if_pos hr]
    have heq : S ∩ φ ⁻¹' {r} = p.active := by
      rw [hr, coset p.anchor]
      exact p.active_eq_inter_coset.symm
    change ((h : ℕ) : ℝ) * (μ (S ∩ φ ⁻¹' {r})).toReal = _
    rw [heq]
  · rw [if_neg hr]
    by_cases hs : r ∈ φ '' S
    · rw [if_pos hs]
      obtain ⟨w, hw, hwr⟩ := hs
      have hwbg : w ∈ p.background := by
        have hp := hw
        rw [p.partition] at hp
        rcases hp with hb | ha
        · exact hb
        · have heq : φ w = φ p.anchor := by
            change w ∈ φ ⁻¹' {φ p.anchor}
            rw [coset p.anchor]
            exact p.active_subset_coset ha
          exact False.elim (hr (hwr.symm.trans heq))
      have hcoset : w +ᵥ (H : Set G) ≤ᵐ[μ] p.background := by
        apply ae_le_set.mpr
        apply measure_mono_null _ p.background_periodic
        apply sdiff_subset_sdiff_left
        rintro x ⟨k, hk, rfl⟩
        exact ⟨w, hwbg, k, hk, rfl⟩
      apply loebResidueProfile_one_of_fiber_ae_subset U hU q h hd
      have hfiber : φ ⁻¹' {r} = w +ᵥ (H : Set G) := by rw [← hwr, coset w]
      rw [hfiber]
      exact hcoset.trans (subset_union_left.trans p.partition.ge).eventuallySubset
    · rw [if_neg hs]
      have heq : S ∩ φ ⁻¹' {r} = ∅ := by
        apply subset_antisymm
        · rintro x ⟨hxS, hxr⟩
          exact False.elim (hs ⟨x, hxS, hxr⟩)
        · exact empty_subset _
      change ((h : ℕ) : ℝ) * (μ (S ∩ φ ⁻¹' {r})).toReal = 0
      rw [heq, measure_empty, ENNReal.toReal_zero, mul_zero]

end Erdos335.Loeb

end
