import Erdos335.HighGapGlobalProfile
import Erdos335.OrdinaryPositiveFrame
import Erdos335.FiniteFrameDensityNecessity
import Erdos335.ActiveSectionUniformDensity
import Erdos335.UniformResidueInverse
import Mathlib.Data.Nat.Factorial.Basic

/-!
# The actual Bohr branch under the two-sided High hypotheses

Private proof development. Verification status is recorded separately. The covering modulus is constructed internally.
The finite frame uses the ordinary input densities and the reference
profile's literal support, cardinality and unique-expression fields.
The total sumset density then supplies the active-section sum density.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2400000

open Filter Set Topology MeasureTheory
open Erdos335.Loeb
open scoped Pointwise ENNReal

noncomputable section

namespace Erdos335.Proposed

private theorem residueFiber_eq_literal_of_positive
    (A : Set ℕ) (hA : A ⊆ Set.Ioi 0) (m : ℕ+) (r : ZMod (m : ℕ)) :
    residueFiber A r = {n : ℕ | n ∈ A ∧ (n : ZMod (m : ℕ)) = r} := by
  ext n
  change (n ∈ A ∧ 0 < n ∧ (n : ZMod (m : ℕ)) ∈ ({r} : Finset _)) ↔
    (n ∈ A ∧ (n : ZMod (m : ℕ)) = r)
  simp only [Finset.mem_singleton]
  constructor
  · exact fun hn => ⟨hn.1, hn.2.2⟩
  · exact fun hn => ⟨hn.1, hA hn.1, hn.2⟩

theorem high_gap_bohr_branch
    (U : Ultrafilter ℕ) (hU : (U : Filter ℕ) ≤ atTop)
    (A B : Set ℕ) (hApos : A ⊆ Set.Ioi 0) (hBpos : B ⊆ Set.Ioi 0)
    (a b δA δB : ℝ) (ha : 0 < a) (hb : 0 < b)
    (hAdensity : HasDensity A a) (hBdensity : HasDensity B b)
    (hCdensity : HasDensity (A + B) (a + b))
    (hgap : a + b < gamma A B)
    (hhighA : gamma A B < a + b + δA)
    (hhighB : gamma A B < a + b + δB)
    (hcapA : ∀ h : ℕ+, a + δA ≤ ((residues (h : ℕ) A).card : ℝ) / (h : ℕ))
    (hcapB : ∀ h : ℕ+, b + δB ≤ ((residues (h : ℕ) B).card : ℝ) / (h : ℕ)) :
    BohrBranch A B := by
  classical
  have hDelta : 0 < gamma A B - (a + b) := sub_pos.mpr hgap
  obtain ⟨D, hD⟩ := exists_nat_gt (1 / (gamma A B - (a + b)))
  let M : ℕ+ := ⟨D.factorial, Nat.factorial_pos D⟩
  have hM : ∀ h : ℕ+, ((h : ℕ) : ℝ) * (gamma A B - (a + b)) < 1 →
      (h : ℕ) ∣ (M : ℕ) := by
    intro h hsmall
    have hquot : ((h : ℕ) : ℝ) < 1 / (gamma A B - (a + b)) :=
      (lt_div_iff₀ hDelta).mpr hsmall
    have hle : (h : ℕ) ≤ D := by exact_mod_cast (hquot.trans hD).le
    exact Nat.dvd_factorial h.pos hle
  obtain ⟨h, _, fA, fB, output, p, hSupport, hDensityA, hDensityB, hRefined⟩ :=
    exists_high_gap_global_positive_profile U hU A B a b δA δB ha hb
      hAdensity hBdensity hCdensity hgap hhighA hhighB hcapA hcapB M hM
  have hh : ((h : ℕ) : ℝ) ≠ 0 := by exact_mod_cast h.ne_zero
  have hcancel (c : ℝ) : ((h : ℕ) : ℝ) * (c / (h : ℕ)) = c := by
    field_simp [hh]
  have hid : naturalCyclicProjection h h = AddMonoidHom.id (ZMod (h : ℕ)) := by
    ext r
    rw [naturalCyclicProjection_val h h dvd_rfl, ZMod.natCast_zmod_val]
    rfl
  have hMovingVal (r : ZMod (h : ℕ)) : fA h r =
      if r = p.activeMoving then p.movingMass else if r ∈ p.movingSupport then 1 else 0 := by
    simpa only [positiveResiduePattern, hid, AddMonoidHom.id_apply] using
      p.moving_profile h dvd_rfl r
  have hPrefixVal (r : ZMod (h : ℕ)) : fB h r =
      if r = p.activePrefix then p.prefixMass else if r ∈ residues (h : ℕ) B then 1 else 0 := by
    simpa only [positiveResiduePattern, hid, AddMonoidHom.id_apply] using
      p.prefix_profile h dvd_rfl r
  have hSectionA (r : ZMod (h : ℕ)) : HasDensity (residueSection A h r) (fA h r) := by
    have hFiber : HasDensity (residueFiber A r) (fA h r / (h : ℕ)) := by
      simpa only [residueFiber_eq_literal_of_positive A hApos h r] using hDensityA h r
    simpa only [hcancel] using
      hasDensity_residueSection_of_fiber A h r (fA h r / (h : ℕ)) hApos hFiber
  have hSectionB (r : ZMod (h : ℕ)) : HasDensity (residueSection B h r) (fB h r) := by
    have hFiber : HasDensity (residueFiber B r) (fB h r / (h : ℕ)) := by
      simpa only [residueFiber_eq_literal_of_positive B hBpos h r] using hDensityB h r
    simpa only [hcancel] using
      hasDensity_residueSection_of_fiber B h r (fB h r / (h : ℕ)) hBpos hFiber
  let f : FiniteFrame A B := {
    modulus := h
    activeA := p.activeMoving
    activeB := p.activePrefix
    activeA_mem := p.support_subset p.activeMoving_mem
    activeB_mem := p.activePrefix_mem
    backgroundA := by
      intro r hr hri
      have hmem : r ∈ p.movingSupport := by rwa [hSupport]
      have hvalue : fA h r = 1 := by rw [hMovingVal r, if_neg hri, if_pos hmem]
      simpa only [hvalue] using hSectionA r
    backgroundB := by
      intro r hr hrj
      have hvalue : fB h r = 1 := by rw [hPrefixVal r, if_neg hrj, if_pos hr]
      simpa only [hvalue] using hSectionB r
    uniqueExpression := by
      intro r hr t ht hrt
      apply p.unique_expression r _ t ht hrt
      rwa [hSupport]
    card_sum := by simpa only [hSupport] using p.cardinality
  }
  have hactiveA : HasDensity (residueSection A f.modulus f.activeA) p.movingMass := by
    have hvalue : fA h p.activeMoving = p.movingMass := by
      rw [hMovingVal, if_pos rfl]
    simpa only [hvalue] using hSectionA p.activeMoving
  have hactiveB : HasDensity (residueSection B f.modulus f.activeB) p.prefixMass := by
    have hvalue : fB h p.activePrefix = p.prefixMass := by
      rw [hPrefixVal, if_pos rfl]
    simpa only [hvalue] using hSectionB p.activePrefix
  have hsum := f.active_sections_sum_hasDensity hApos hBpos a b
    p.movingMass p.prefixMass hAdensity hBdensity hCdensity hactiveA hactiveB
  have hUniformA : ∀ m : ℕ+, ∀ r : ZMod (m : ℕ),
      HasDensity (residueFiber (residueSection A f.modulus f.activeA) r)
        (p.movingMass / (m : ℕ)) := by
    apply residueSection_uniform_residue_density A h p.activeMoving p.movingMass hApos
    intro m r hr
    have hd := (hRefined (h * m) (show (h : ℕ) ∣ ((h * m : ℕ+) : ℕ) from ⟨m, rfl⟩) r).1
    simpa only [residueFiber_eq_literal_of_positive A hApos (h * m) r,
      positiveResiduePattern, hr, ite_true] using hd
  have hUniformB : ∀ m : ℕ+, ∀ r : ZMod (m : ℕ),
      HasDensity (residueFiber (residueSection B f.modulus f.activeB) r)
        (p.prefixMass / (m : ℕ)) := by
    apply residueSection_uniform_residue_density B h p.activePrefix p.prefixMass hBpos
    intro m r hr
    have hd := (hRefined (h * m) (show (h : ℕ) ∣ ((h * m : ℕ+) : ℕ) from ⟨m, rfl⟩) r).2
    simpa only [residueFiber_eq_literal_of_positive B hBpos (h * m) r,
      positiveResiduePattern, hr, ite_true] using hd
  obtain ⟨θ, startA, startB, hθ, hAarc, hBarc, hAholes, hBholes⟩ :=
    parallel_irrational_arcs_of_uniform_residue_densities
      (residueSection A f.modulus f.activeA) (residueSection B f.modulus f.activeB)
      (fun _ hk => hk.1) (fun _ hk => hk.1)
      p.movingMass p.prefixMass p.moving_positive p.prefix_positive p.mass_sum_lt_one
      hactiveA hactiveB hsum hUniformA hUniformB
  exact ⟨f, θ, startA, startB, p.movingMass, p.prefixMass, hθ,
    p.moving_positive, p.prefix_positive, p.mass_sum_lt_one, hAarc, hBarc, hAholes, hBholes⟩

end Erdos335.Proposed

end
