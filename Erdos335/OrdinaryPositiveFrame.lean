import Erdos335.PositivePairProfiles
import Erdos335.ResidueSectionDensity
import Erdos335.Bohr

/-!
# An ordinary finite frame from a matched literal positive profile

Private proof development. Verification status is recorded separately.
Literal support equality and the ordinary base-modulus fiber densities
are explicit inputs. The construction does not discard sparse residues.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000

open Filter Set Topology
open scoped Pointwise

namespace Erdos335.Proposed

theorem section_sum_hasDensity_of_fiber_sum
    (A B : Set ℕ) (q : ℕ+) (r t : ZMod (q : ℕ)) (d : ℝ)
    (h : HasDensity (residueFiber A r + residueFiber B t) d) :
    HasDensity (residueSection A q r + residueSection B q t) (((q : ℕ) : ℝ) * d) := by
  let S := residueSection A q r + residueSection B q t
  have hSpos : S ⊆ Set.Ioi 0 := sumset_positive (fun _ hn => hn.1) (fun _ hn => hn.1)
  have hDpos : dilate S q ⊆ Set.Ioi 0 := dilate_positive hSpos q
  have hshift := h.shift ((q : ℕ) + (q : ℕ))
  have heq : shift (residueFiber A r + residueFiber B t) ((q : ℕ) + (q : ℕ)) =
      shift (dilate S q) (positiveRepresentative q r + positiveRepresentative q t) := by
    rw [shift_add, shift_fiber_eq_dilate, shift_fiber_eq_dilate, ← shift_add, ← dilate_add]
  rw [heq] at hshift
  have hD : HasDensity (dilate S q) d := (hasDensity_shift_iff _ _ _).mp hshift
  have hF : HasDensity (residueFiber (dilate S q) (0 : ZMod (q : ℕ))) d := by
    rw [residueFiber_dilate S q hSpos]
    exact hD
  have hsection := hasDensity_residueSection_of_fiber (dilate S q) q 0 d hDpos hF
  have hsec : residueSection (dilate S q) q 0 = S := by
    rw [section_eq_zeroSection _ _ _ hDpos]
    simpa only [ZMod.val_zero, ite_true] using zeroSection_dilate S q
  rwa [hsec] at hsection

theorem ordinary_positive_finite_frame
    (A B : Set ℕ) (a b : ℝ) (hA : A ⊆ Set.Ioi 0) (hB : B ⊆ Set.Ioi 0)
    (h : ℕ+) (moving prefixProfile output : Loeb.NaturalResidueProfile)
    (p : Loeb.LocalPositiveResidueProfile h A B a b moving prefixProfile output)
    (hSupport : p.movingSupport = residues (h : ℕ) A)
    (hMoving : ∀ r : ZMod (h : ℕ), HasDensity (residueFiber A r) (moving h r / (h : ℕ)))
    (hPrefix : ∀ r : ZMod (h : ℕ), HasDensity (residueFiber B r) (prefixProfile h r / (h : ℕ)))
    (hOutput : HasDensity (residueFiber (A + B) (p.activeMoving + p.activePrefix))
      (output h (p.activeMoving + p.activePrefix) / (h : ℕ))) :
    ∃ f : FiniteFrame A B, f.modulus = h ∧
      HasDensity (residueSection A f.modulus f.activeA) p.movingMass ∧
      HasDensity (residueSection B f.modulus f.activeB) p.prefixMass ∧
      HasDensity (residueSection A f.modulus f.activeA + residueSection B f.modulus f.activeB)
        (p.movingMass + p.prefixMass) := by
  classical
  have hh : ((h : ℕ) : ℝ) ≠ 0 := by exact_mod_cast h.ne_zero
  have hcancel (c : ℝ) : ((h : ℕ) : ℝ) * (c / (h : ℕ)) = c := by field_simp
  have hid : Loeb.naturalCyclicProjection h h = AddMonoidHom.id (ZMod (h : ℕ)) := by
    ext r
    rw [Loeb.naturalCyclicProjection_val h h dvd_rfl, ZMod.natCast_zmod_val]
    rfl
  have hMovingVal (r : ZMod (h : ℕ)) : moving h r =
      if r = p.activeMoving then p.movingMass else if r ∈ p.movingSupport then 1 else 0 := by
    have hp := p.moving_profile h dvd_rfl r
    simpa only [Loeb.positiveResiduePattern, hid, AddMonoidHom.id_apply] using hp
  have hPrefixVal (r : ZMod (h : ℕ)) : prefixProfile h r =
      if r = p.activePrefix then p.prefixMass else if r ∈ residues (h : ℕ) B then 1 else 0 := by
    have hp := p.prefix_profile h dvd_rfl r
    simpa only [Loeb.positiveResiduePattern, hid, AddMonoidHom.id_apply] using hp
  have hOutputVal (r : ZMod (h : ℕ)) : output h r =
      if r = p.activeMoving + p.activePrefix then p.movingMass + p.prefixMass
      else if r ∈ p.movingSupport + residues (h : ℕ) B then 1 else 0 := by
    have hp := p.output_profile h dvd_rfl r
    simpa only [Loeb.positiveResiduePattern, hid, AddMonoidHom.id_apply] using hp
  have hSectionA (r : ZMod (h : ℕ)) : HasDensity (residueSection A h r) (moving h r) := by
    simpa only [hcancel] using
      hasDensity_residueSection_of_fiber A h r (moving h r / (h : ℕ)) hA (hMoving r)
  have hSectionB (r : ZMod (h : ℕ)) : HasDensity (residueSection B h r) (prefixProfile h r) := by
    simpa only [hcancel] using
      hasDensity_residueSection_of_fiber B h r (prefixProfile h r / (h : ℕ)) hB (hPrefix r)
  let f : FiniteFrame A B := {
    modulus := h
    activeA := p.activeMoving
    activeB := p.activePrefix
    activeA_mem := p.support_subset p.activeMoving_mem
    activeB_mem := p.activePrefix_mem
    backgroundA := by
      intro r hr hri
      have hmem : r ∈ p.movingSupport := by rwa [hSupport]
      have hvalue : moving h r = 1 := by rw [hMovingVal r, if_neg hri, if_pos hmem]
      simpa only [hvalue] using hSectionA r
    backgroundB := by
      intro r hr hrj
      have hvalue : prefixProfile h r = 1 := by rw [hPrefixVal r, if_neg hrj, if_pos hr]
      simpa only [hvalue] using hSectionB r
    uniqueExpression := by
      intro r hr t ht hrt
      apply p.unique_expression r _ t ht hrt
      rwa [hSupport]
    card_sum := by simpa only [hSupport] using p.cardinality
  }
  have hactiveA : HasDensity (residueSection A h p.activeMoving) p.movingMass := by
    have hvalue : moving h p.activeMoving = p.movingMass := by rw [hMovingVal, if_pos rfl]
    simpa only [hvalue] using hSectionA p.activeMoving
  have hactiveB : HasDensity (residueSection B h p.activePrefix) p.prefixMass := by
    have hvalue : prefixProfile h p.activePrefix = p.prefixMass := by rw [hPrefixVal, if_pos rfl]
    simpa only [hvalue] using hSectionB p.activePrefix
  have hactiveOutput : HasDensity (residueFiber (A + B) (p.activeMoving + p.activePrefix))
      ((p.movingMass + p.prefixMass) / (h : ℕ)) := by
    have hvalue : output h (p.activeMoving + p.activePrefix) = p.movingMass + p.prefixMass := by
      rw [hOutputVal, if_pos rfl]
    simpa only [hvalue] using hOutput
  have hactiveSum : HasDensity
      (residueFiber A p.activeMoving + residueFiber B p.activePrefix)
      ((p.movingMass + p.prefixMass) / (h : ℕ)) := by
    change HasDensity (residueFiber (A + B) (f.activeA + f.activeB))
      ((p.movingMass + p.prefixMass) / (h : ℕ)) at hactiveOutput
    rw [f.outputFiber_eq hA hB] at hactiveOutput
    exact hactiveOutput
  have hsectionSum : HasDensity
      (residueSection A h p.activeMoving + residueSection B h p.activePrefix)
      (p.movingMass + p.prefixMass) := by
    simpa only [hcancel] using section_sum_hasDensity_of_fiber_sum A B h
      p.activeMoving p.activePrefix ((p.movingMass + p.prefixMass) / (h : ℕ)) hactiveSum
  exact ⟨f, rfl, hactiveA, hactiveB, hsectionSum⟩

end Erdos335.Proposed
