import Erdos335.LoebQuasiFiniteProfiles
import Erdos335.NaturalQuotientRefinement

/-!
# Refined nonexceptional profiles and the mass of a null active part
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Filter Set MeasureTheory
open scoped Pointwise ENNReal BigOperators Classical

noncomputable section

namespace Erdos335.Loeb

local instance quasiOffActiveLoebSpace (U : Ultrafilter ℕ) (q : ℕ → ℕ+) :
    MeasurableSpace ((U : Filter ℕ).Product (fun n => ZMod (q n : ℕ))) := loebMeasurableSpace U

theorem loeb_quasiPeriodic_refined_off_active
    (U : Ultrafilter ℕ) (hU : (U : Filter ℕ) ≤ atTop) (q : ℕ → ℕ+)
    (W : Set ((U : Filter ℕ).Product (fun n => ZMod (q n : ℕ))))
    (H : AddSubgroup ((U : Filter ℕ).Product (fun n => ZMod (q n : ℕ))))
    (p : QuasiPeriodicDecomposition (loebMeasure U hU) H W)
    {F : Type*} [AddCommGroup F] [DecidableEq F]
    (f : ((U : Filter ℕ).Product (fun n => ZMod (q n : ℕ))) →+ F) (hker : f.ker = H)
    (h : ℕ+) (hd : ∀ᶠ n in U, (h : ℕ) ∣ (q n : ℕ)) (π : ZMod (h : ℕ) →+ F)
    (hcomp : ∀ x, π (finiteQuotient U (fun n => naturalCyclicProjection (q n) h) x) = f x)
    (r : ZMod (h : ℕ)) (hr : π r ≠ f p.anchor) :
    loebResidueProfile U hU q h W r = 0 ∨ loebResidueProfile U hU q h W r = 1 := by
  let G := (U : Filter ℕ).Product (fun n => ZMod (q n : ℕ))
  let μ : Measure G := loebMeasure U hU
  let g := finiteQuotient U (fun n => naturalCyclicProjection (q n) h)
  have coset (x a : G) : x ∈ a +ᵥ (H : Set G) ↔ f x = f a := by
    rw [← hker, ← addHom_fiber_eq_coset]
    rfl
  by_cases hs : π r ∈ f '' W
  · right
    obtain ⟨w, hw, hwr⟩ := hs
    have hwbg : w ∈ p.background := by
      have hp := hw
      rw [p.partition] at hp
      rcases hp with hb | ha
      · exact hb
      · exact False.elim (hr (hwr.symm.trans ((coset w p.anchor).mp (p.active_subset_coset ha))))
    have hcoset : w +ᵥ (H : Set G) ≤ᵐ[μ] p.background := by
      apply ae_le_set.mpr
      apply measure_mono_null _ p.background_periodic
      apply sdiff_subset_sdiff_left
      rintro x ⟨k, hk, rfl⟩
      exact ⟨w, hwbg, k, hk, rfl⟩
    apply loebResidueProfile_one_of_fiber_ae_subset U hU q h hd
    have hfiber : g ⁻¹' {r} ⊆ w +ᵥ (H : Set G) := by
      intro x hx
      apply (coset x w).mpr
      rw [← hcomp x, show g x = r from hx, ← hwr]
    exact hfiber.eventuallySubset.trans
      (hcoset.trans (subset_union_left.trans p.partition.ge).eventuallySubset)
  · left
    have heq : W ∩ g ⁻¹' {r} = ∅ := by
      apply subset_antisymm
      · rintro x ⟨hx, hxr⟩
        exact False.elim (hs ⟨x, hx, by rw [← hcomp x, show g x = r from hxr]⟩)
      · exact empty_subset _
    change ((h : ℕ) : ℝ) * (μ (W ∩ g ⁻¹' {r})).toReal = 0
    rw [heq, measure_empty, ENNReal.toReal_zero, mul_zero]

theorem loeb_quasiPeriodic_null_mass_integer
    (U : Ultrafilter ℕ) (hU : (U : Filter ℕ) ≤ atTop) (q : ℕ → ℕ+)
    (W : Set ((U : Filter ℕ).Product (fun n => ZMod (q n : ℕ))))
    (H : AddSubgroup ((U : Filter ℕ).Product (fun n => ZMod (q n : ℕ))))
    (p : QuasiPeriodicDecomposition (loebMeasure U hU) H W)
    (hzero : loebMeasure U hU p.active = 0)
    (h : ℕ+) (hd : ∀ᶠ n in U, (h : ℕ) ∣ (q n : ℕ))
    (hker : (finiteQuotient U (fun n => naturalCyclicProjection (q n) h)).ker = H) :
    ∃ M : ℤ, ((h : ℕ) : ℝ) * (loebMeasure U hU W).toReal = M := by
  let f := finiteQuotient U (fun n => naturalCyclicProjection (q n) h)
  let R := (f '' W).toFinite.toFinset
  let c := f p.anchor
  have hR : f '' W = (R : Set _) := by ext r; simp [R]
  have hp (r : ZMod (h : ℕ)) : loebResidueProfile U hU q h W r =
      if r ∈ R.erase c then (1 : ℝ) else 0 := by
    have hh := loeb_quasiPeriodic_residue_profile U hU q W H p h hd hker r
    change loebResidueProfile U hU q h W r =
      (if r = c then ((h : ℕ) : ℝ) * (loebMeasure U hU p.active).toReal
        else if r ∈ f '' W then 1 else 0) at hh
    rw [hzero, ENNReal.toReal_zero, mul_zero, hR] at hh
    by_cases hr : r = c
    · subst r
      simpa using hh
    · simpa [hr] using hh
  have hs := sum_loebResidueProfile U hU q h W
  simp_rw [hp] at hs
  simp at hs
  have hfilter : (Finset.univ.filter (fun r : ZMod (h : ℕ) => r ≠ c ∧ r ∈ R)) = R.erase c := by
    ext r
    simp
  rw [hfilter] at hs
  refine ⟨(R.erase c).card, ?_⟩
  exact_mod_cast hs.symm

end Erdos335.Loeb

end
