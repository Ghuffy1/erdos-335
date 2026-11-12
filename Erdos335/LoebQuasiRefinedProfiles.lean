import Erdos335.LoebQuasiFiniteProfiles
import Erdos335.NaturalQuotientRefinement

/-!
# Refining the exceptional fiber of a quasi-periodic decomposition
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Filter Set MeasureTheory
open scoped Pointwise ENNReal Classical

noncomputable section

namespace Erdos335.Loeb

local instance quasiRefinedProfilesLoebSpace (U : Ultrafilter ℕ) (q : ℕ → ℕ+) :
    MeasurableSpace ((U : Filter ℕ).Product (fun n => ZMod (q n : ℕ))) := loebMeasurableSpace U

theorem loeb_quasiPeriodic_refined_profile
    (U : Ultrafilter ℕ) (hU : (U : Filter ℕ) ≤ atTop) (q : ℕ → ℕ+)
    (W : Set ((U : Filter ℕ).Product (fun n => ZMod (q n : ℕ))))
    (H : AddSubgroup ((U : Filter ℕ).Product (fun n => ZMod (q n : ℕ))))
    (p : QuasiPeriodicDecomposition (loebMeasure U hU) H W)
    {F : Type*} [AddCommGroup F] [DecidableEq F]
    (f : ((U : Filter ℕ).Product (fun n => ZMod (q n : ℕ))) →+ F) (hker : f.ker = H)
    (h : ℕ+) (hd : ∀ᶠ n in U, (h : ℕ) ∣ (q n : ℕ)) (π : ZMod (h : ℕ) →+ F)
    (hcomp : ∀ x, π (finiteQuotient U (fun n => naturalCyclicProjection (q n) h) x) = f x)
    (length : ℝ)
    (hactive : ∀ r, loebResidueProfile U hU q h p.active r = if π r = f p.anchor then length else 0)
    (r : ZMod (h : ℕ)) :
    loebResidueProfile U hU q h W r =
      if π r = f p.anchor then length else if π r ∈ f '' W then 1 else 0 := by
  let G := (U : Filter ℕ).Product (fun n => ZMod (q n : ℕ))
  let μ : Measure G := loebMeasure (X := fun n => ZMod (q n : ℕ)) U hU
  let g := finiteQuotient U (fun n => naturalCyclicProjection (q n) h)
  have coset (x a : G) : x ∈ a +ᵥ (H : Set G) ↔ f x = f a := by
    rw [← hker, ← addHom_fiber_eq_coset]
    rfl
  by_cases hr : π r = f p.anchor
  · rw [if_pos hr]
    have heq : W ∩ g ⁻¹' {r} = p.active ∩ g ⁻¹' {r} := by
      apply subset_antisymm
      · rintro x ⟨hxW, hxr⟩
        refine ⟨?_, hxr⟩
        rw [p.active_eq_inter_coset]
        refine ⟨hxW, (coset x p.anchor).mpr ?_⟩
        rw [← hcomp x, show g x = r from hxr]
        exact hr
      · exact inter_subset_inter_left _ (subset_union_right.trans p.partition.ge)
    have hp : loebResidueProfile U hU q h W r = loebResidueProfile U hU q h p.active r :=
      congrArg (fun S : Set G => ((h : ℕ) : ℝ) * (μ S).toReal) heq
    rw [hp, hactive, if_pos hr]
  · rw [if_neg hr]
    by_cases hs : π r ∈ f '' W
    · rw [if_pos hs]
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
    · rw [if_neg hs]
      have heq : W ∩ g ⁻¹' {r} = ∅ := by
        apply subset_antisymm
        · rintro x ⟨hxW, hxr⟩
          exact False.elim (hs ⟨x, hxW, by rw [← hcomp x, show g x = r from hxr]⟩)
        · exact empty_subset _
      change ((h : ℕ) : ℝ) * (μ (W ∩ g ⁻¹' {r})).toReal = 0
      rw [heq, measure_empty, ENNReal.toReal_zero, mul_zero]

end Erdos335.Loeb

end
