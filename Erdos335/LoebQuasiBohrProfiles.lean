import Erdos335.LoebBohrPairProfiles
import Erdos335.LoebProfileBounds

/-!
# Refined profiles of a quasi-periodic pair with a positive Bohr terminal
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000

open Filter Set MeasureTheory
open scoped Pointwise ENNReal Classical

noncomputable section

namespace Erdos335.Loeb

local instance quasiBohrProfilesLoebSpace (U : Ultrafilter ℕ) (q : ℕ → ℕ+) :
    MeasurableSpace ((U : Filter ℕ).Product (fun n => ZMod (q n : ℕ))) := loebMeasurableSpace U

theorem loeb_quasiBohr_right_residue_profile
    (U : Ultrafilter ℕ) (hU : (U : Filter ℕ) ≤ atTop) (q : ℕ → ℕ+)
    (A B : Set ((U : Filter ℕ).Product (fun n => ZMod (q n : ℕ))))
    (p : QuasiPeriodicPairData (loebMeasure U hU) (internalInnerMeasure U hU) A B)
    (b : InternalBohrPairData U hU q p.left.active p.right.active)
    (hperiod : p.period = (finiteQuotient U b.residue).ker)
    (h : ℕ+) (hd : ∀ᶠ n in U, (h : ℕ) ∣ (q n : ℕ)) (hmh : (b.modulus : ℕ) ∣ (h : ℕ))
    (r : ZMod (h : ℕ)) :
    loebResidueProfile U hU q h B r =
      if naturalCyclicProjection h b.modulus r = finiteQuotient U b.residue b.right_anchor
        then b.right_length
      else if naturalCyclicProjection h b.modulus r ∈ (finiteQuotient U b.residue) '' B
        then 1 else 0 := by
  classical
  let G := (U : Filter ℕ).Product (fun n => ZMod (q n : ℕ))
  let μ : Measure G := loebMeasure (X := fun n => ZMod (q n : ℕ)) U hU
  let f := finiteQuotient U b.residue
  let g := finiteQuotient U (fun n => naturalCyclicProjection (q n) h)
  let π := naturalCyclicProjection h b.modulus
  have hmd := hd.mono fun n hn => dvd_trans hmh hn
  have hquotient : f = finiteQuotient U (fun n => naturalCyclicProjection (q n) b.modulus) := by
    apply finiteQuotient_eq_of_eventually_natural
    · exact b.natural_residue.mono fun n hn => hn.2
    · exact hmd.mono fun n hn k => naturalCyclicProjection_natCast (q n) b.modulus hn k
  have hcomp (x : G) : π (g x) = f x := by
    rw [hquotient]
    exact congrArg (fun k => k x) (finiteQuotient_natural_refinement U q h b.modulus hd hmh)
  have coset_eq (x a : G) (hx : x ∈ a +ᵥ (p.period : Set G)) : f x = f a := by
    have hx' : x ∈ a +ᵥ (f.ker : Set G) := by simpa only [hperiod] using hx
    rwa [← addHom_fiber_eq_coset] at hx'
  have coset_mem (x a : G) (hx : f x = f a) : x ∈ a +ᵥ (p.period : Set G) := by
    have hx' : x ∈ a +ᵥ (f.ker : Set G) := by
      rw [← addHom_fiber_eq_coset]
      exact hx
    simpa only [hperiod] using hx'
  have hanchor : f p.right.anchor = f b.right_anchor := by
    obtain ⟨x, hx⟩ := p.right.active_nonempty
    have hp := coset_eq x p.right.anchor (p.right.active_subset_coset hx)
    have hb : f x = f b.right_anchor := by
      have hc := (b.right_containment hx).1
      rwa [← addHom_fiber_eq_coset] at hc
    exact hp.symm.trans hb
  by_cases hr : π r = f b.right_anchor
  · rw [if_pos hr]
    have heq : B ∩ g ⁻¹' {r} = p.right.active ∩ g ⁻¹' {r} := by
      apply subset_antisymm
      · rintro x ⟨hxB, hxr⟩
        refine ⟨?_, hxr⟩
        rw [p.right.active_eq_inter_coset]
        refine ⟨hxB, coset_mem x p.right.anchor ?_⟩
        rw [← hcomp x, show g x = r from hxr, hr, hanchor]
      · exact inter_subset_inter_left _ (subset_union_right.trans p.right.partition.ge)
    have hprof : loebResidueProfile U hU q h B r = loebResidueProfile U hU q h p.right.active r :=
      congrArg (fun S : Set G => ((h : ℕ) : ℝ) * (μ S).toReal) heq
    rw [hprof]
    have hp := (b.residue_profiles h hd hmh).2 r
    have hr' : naturalCyclicProjection h b.modulus r = finiteQuotient U b.residue b.right_anchor := hr
    rw [if_pos hr'] at hp
    exact hp
  · rw [if_neg hr]
    by_cases hs : π r ∈ f '' B
    · rw [if_pos hs]
      obtain ⟨w, hw, hwr⟩ := hs
      have hwbg : w ∈ p.right.background := by
        have hpart := hw
        rw [p.right.partition] at hpart
        rcases hpart with hb | ha
        · exact hb
        · have he := coset_eq w p.right.anchor (p.right.active_subset_coset ha)
          exact False.elim (hr (hwr.symm.trans (he.trans hanchor)))
      have hcoset : w +ᵥ (p.period : Set G) ≤ᵐ[μ] p.right.background := by
        apply ae_le_set.mpr
        apply measure_mono_null _ p.right.background_periodic
        apply sdiff_subset_sdiff_left
        rintro x ⟨k, hk, rfl⟩
        exact ⟨w, hwbg, k, hk, rfl⟩
      apply loebResidueProfile_one_of_fiber_ae_subset U hU q h hd
      have hfiber : g ⁻¹' {r} ⊆ w +ᵥ (p.period : Set G) := by
        intro x hx
        apply coset_mem x w
        rw [← hcomp x, show g x = r from hx, ← hwr]
      exact hfiber.eventuallySubset.trans
        (hcoset.trans (subset_union_left.trans p.right.partition.ge).eventuallySubset)
    · rw [if_neg hs]
      have heq : B ∩ g ⁻¹' {r} = ∅ := by
        apply subset_antisymm
        · rintro x ⟨hxB, hxr⟩
          exact False.elim (hs ⟨x, hxB, by rw [← hcomp x, show g x = r from hxr]⟩)
        · exact empty_subset _
      change ((h : ℕ) : ℝ) * (μ (B ∩ g ⁻¹' {r})).toReal = 0
      rw [heq, measure_empty, ENNReal.toReal_zero, mul_zero]

end Erdos335.Loeb

end
