import Erdos335.LoebTwoNullPrefixes
import Erdos335.LoebPrefixAgreement
import Erdos335.ConstrainedProfileComparison
import Erdos335.LoebQuasiPeriodicActiveBounds
import Erdos335.LoebQuasiPeriodicFiniteFrame
import Erdos335.LoebQuasiFiniteProfiles
import Erdos335.LoebNaturalPeriodMasks
import Erdos335.LoebPeriodicWindowInputs
import Erdos335.CyclicQuotients
import Erdos335.FiniteExceptionalCapacity
import Mathlib.Data.PNat.Prime

/-!
# Same-quotient fractional data for a nonperiodic null-prefix terminal

Private proof development. Verification status is recorded separately. These lemmas reconstruct the natural quotient
of the original quasi-period, retaining the relation between the prefix
mask and the fractional total mass needed by the two-prefix contradiction.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Filter Set Topology MeasureTheory
open Erdos335.IntermediateScale
open scoped Pointwise ENNReal

noncomputable section

namespace Erdos335.Loeb

local instance lowPairedWindowsLoebSpace (U : Ultrafilter ℕ) (q : ℕ → ℕ+) :
    MeasurableSpace ((U : Filter ℕ).Product (fun n => ZMod (q n : ℕ))) :=
  loebMeasurableSpace U

theorem positive_subgroup_natural_quotient_data
    (U : Ultrafilter ℕ) (hU : (U : Filter ℕ) ≤ atTop) (q : ℕ → ℕ+)
    (H : AddSubgroup ((U : Filter ℕ).Product (fun n => ZMod (q n : ℕ))))
    (hHm : MeasurableSet (H : Set ((U : Filter ℕ).Product (fun n => ZMod (q n : ℕ)))))
    (hHpos : 0 < loebMeasure U hU (H : Set ((U : Filter ℕ).Product (fun n => ZMod (q n : ℕ))))) :
    ∃ h : ℕ+, (∀ᶠ n in U, (h : ℕ) ∣ (q n : ℕ)) ∧
      (finiteQuotient U (fun n => naturalCyclicProjection (q n) h)).ker = H ∧
      loebMeasure U hU (H : Set ((U : Filter ℕ).Product (fun n => ZMod (q n : ℕ)))) =
        1 / (h : ℕ) := by
  obtain ⟨h, ρ, hρ, hker, hmass⟩ :=
    positive_measurable_subgroup_is_natural_finite_kernel U hU q H hHm hHpos
  have hd : ∀ᶠ n in U, (h : ℕ) ∣ (q n : ℕ) := by
    filter_upwards [hρ] with n hn
    have ht := hn.2 (q n : ℕ)
    rw [ZMod.natCast_self, map_zero] at ht
    exact (ZMod.natCast_eq_zero_iff (q n : ℕ) (h : ℕ)).mp ht.symm
  have heq := finiteQuotient_eq_of_eventually_natural U q h ρ
    (fun n => naturalCyclicProjection (q n) h) (hρ.mono fun _ hn => hn.2)
    (hd.mono fun n hn t => naturalCyclicProjection_natCast (q n) h hn t)
  rw [heq] at hker
  exact ⟨h, hd, hker, hmass⟩

theorem loeb_quasi_periodic_mass_with_active
    (U : Ultrafilter ℕ) (hU : (U : Filter ℕ) ≤ atTop) (q : ℕ → ℕ+)
    (S : Set ((U : Filter ℕ).Product (fun n => ZMod (q n : ℕ))))
    (H : AddSubgroup ((U : Filter ℕ).Product (fun n => ZMod (q n : ℕ))))
    (hHm : MeasurableSet (H : Set ((U : Filter ℕ).Product (fun n => ZMod (q n : ℕ)))))
    (p : QuasiPeriodicDecomposition (loebMeasure U hU) H S)
    (h : ℕ+) (hd : ∀ᶠ n in U, (h : ℕ) ∣ (q n : ℕ))
    (hker : (finiteQuotient U (fun n => naturalCyclicProjection (q n) h)).ker = H)
    (hmH : loebMeasure U hU (H : Set ((U : Filter ℕ).Product (fun n => ZMod (q n : ℕ)))) =
      1 / (h : ℕ))
    (R : Finset (ZMod (h : ℕ)))
    (hR : (finiteQuotient U (fun n => naturalCyclicProjection (q n) h)) '' S = (R : Set _)) :
    (h : ℕ) * (loebMeasure U hU S).toReal = (R.card : ℝ) - 1 +
      (h : ℕ) * (loebMeasure U hU p.active).toReal := by
  let μ := loebMeasure (X := fun n => ZMod (q n : ℕ)) U hU
  letI : IsProbabilityMeasure μ := isProbabilityMeasure_loebMeasure U hU
  have hSat : μ (S + (H : Set _)) = (R.card : ℝ≥0∞) / (h : ℕ) := by
    rw [← hker, addHom_saturation_eq_preimage_image, hR]
    exact loebMeasure_naturalCyclicProjection_preimage U hU q h hd R
  have hidentity := congrArg ENNReal.toReal
    (loeb_quasiPeriodic_saturation_identity U hU q S H hHm p)
  rw [ENNReal.toReal_add (measure_ne_top μ _) (measure_ne_top μ _),
    ENNReal.toReal_add (measure_ne_top μ _) (measure_ne_top μ _), hSat, hmH] at hidentity
  simp only [ENNReal.toReal_div, ENNReal.toReal_natCast, ENNReal.toReal_one] at hidentity
  have hh : ((h : ℕ) : ℝ) ≠ 0 := by exact_mod_cast h.ne_zero
  field_simp [hh] at hidentity
  nlinarith

theorem loeb_null_prefix_fractional_data
    (U : Ultrafilter ℕ) (hU : (U : Filter ℕ) ≤ atTop) (q : ℕ → ℕ+)
    (A B : Set ℕ) (start : ℕ → ℕ) (a b : ℝ)
    (P W : Set ((U : Filter ℕ).Product (fun n => ZMod (q n : ℕ))))
    (p : QuasiPeriodicPairData (loebMeasure U hU) (internalInnerMeasure U hU) P W)
    (hPactual : P =ᵐ[loebMeasure U hU] internalSet U
      (fun n => (cyclicWindow B 0 (q n : ℕ) : Set (ZMod (q n : ℕ)))))
    (hWactual : W =ᵐ[loebMeasure U hU] internalSet U
      (fun n => (cyclicWindow A (start n) (q n : ℕ) : Set (ZMod (q n : ℕ)))))
    (hmP : (loebMeasure U hU P).toReal = b)
    (hmW : (loebMeasure U hU W).toReal = a)
    (hzero : loebMeasure U hU p.left.active = 0)
    (hnotPeriodic : ¬ ∃ (h : ℕ+) (R : Finset (ZMod (h : ℕ))),
      (∀ᶠ n in U, (h : ℕ) ∣ (q n : ℕ)) ∧
        internalSet U
          (fun n => (cyclicWindow A (start n) (q n : ℕ) : Set (ZMod (q n : ℕ))))
          =ᵐ[loebMeasure U hU]
            (finiteQuotient U (fun n => naturalCyclicProjection (q n) h)) ⁻¹' (R : Set _)) :
    ∃ (h : ℕ+) (R : Finset (ZMod (h : ℕ))) (k : ℕ) (x : ℝ),
      (∀ᶠ n in U, (h : ℕ) ∣ (q n : ℕ)) ∧
      (finiteQuotient U (fun n => naturalCyclicProjection (q n) h)).ker = p.period ∧
      (∀ r : ZMod (h : ℕ), actualWindowProfile U hU q h B (fun _ => 0) r =
        if r ∈ R then (1 : ℝ) else 0) ∧
      0 < x ∧ x < 1 ∧ (a + b) * (h : ℕ) = (k : ℝ) + x := by
  classical
  let G := (U : Filter ℕ).Product (fun n => ZMod (q n : ℕ))
  let μ : Measure G := loebMeasure U hU
  letI : IsProbabilityMeasure μ := isProbabilityMeasure_loebMeasure U hU
  let actualA : Set G := internalSet U
    (fun n => (cyclicWindow A (start n) (q n : ℕ) : Set (ZMod (q n : ℕ))))
  have hnot : ¬ ∀ t ∈ p.period, t +ᵥ actualA =ᵐ[μ] actualA := by
    intro hperiod
    obtain ⟨h, R, hd, hmask⟩ := loeb_ae_periods_have_natural_mask U hU q actualA
      (measurable_internalSet U _) p.period p.period_measurable p.period_positive hperiod
    exact hnotPeriodic ⟨h, R, hd, hmask⟩
  obtain ⟨h, hd, hker, hmH⟩ := positive_subgroup_natural_quotient_data U hU q
    p.period p.period_measurable p.period_positive
  let φ := finiteQuotient U (fun n => naturalCyclicProjection (q n) h)
  let prefixCarrier := (φ '' P).toFinite.toFinset
  let movingCarrier := (φ '' W).toFinite.toFinset
  let prefixAnchor := φ p.left.anchor
  let R := prefixCarrier.erase prefixAnchor
  let x : ℝ := (h : ℕ) * (μ p.right.active).toReal
  let k : ℕ := prefixCarrier.card + movingCarrier.card - 2
  have hPrefixCarrier : φ '' P = (prefixCarrier : Set _) := by
    ext r
    simp [prefixCarrier]
  have hMovingCarrier : φ '' W = (movingCarrier : Set _) := by
    ext r
    simp [movingCarrier]
  have hactive := loeb_quasiPeriodic_active_mass_bounds U hU q actualA W p.period
    p.right hWactual hnot
  have hhpos : (0 : ℝ) < (h : ℕ) := by exact_mod_cast h.pos
  have hxpos : 0 < x := mul_pos hhpos
    (ENNReal.toReal_pos hactive.1.ne' (measure_ne_top μ _))
  have hactiveLt := (ENNReal.toReal_lt_toReal (measure_ne_top μ _)
    (measure_ne_top μ _)).mpr hactive.2
  rw [hmH, ENNReal.toReal_div, ENNReal.toReal_one, ENNReal.toReal_natCast] at hactiveLt
  have hxlt : x < 1 := by
    dsimp only [x]
    have hmul := (lt_div_iff₀ hhpos).mp hactiveLt
    nlinarith
  have hPrefixMass := loeb_quasi_periodic_mass_with_active U hU q P p.period
    p.period_measurable p.left h hd hker hmH prefixCarrier hPrefixCarrier
  rw [hmP, hzero, ENNReal.toReal_zero, mul_zero, add_zero] at hPrefixMass
  have hMovingMass := loeb_quasi_periodic_mass_with_active U hU q W p.period
    p.period_measurable p.right h hd hker hmH movingCarrier hMovingCarrier
  rw [hmW] at hMovingMass
  change (h : ℕ) * a = (movingCarrier.card : ℝ) - 1 + x at hMovingMass
  obtain ⟨hPrefixAnchor, hMovingAnchor, _⟩ := loeb_quasiPeriodic_finite_quotient_expression
    U hU q P W p φ hker prefixCarrier movingCarrier hPrefixCarrier hMovingCarrier
  have hPrefixCard : 0 < prefixCarrier.card := Finset.card_pos.mpr ⟨_, hPrefixAnchor⟩
  have hMovingCard : 0 < movingCarrier.card := Finset.card_pos.mpr ⟨_, hMovingAnchor⟩
  have hkcast : (k : ℝ) = (prefixCarrier.card : ℝ) + movingCarrier.card - 2 := by
    dsimp only [k]
    rw [Nat.cast_sub (show 2 ≤ prefixCarrier.card + movingCarrier.card by omega), Nat.cast_add]
    norm_num
  have htotal : (a + b) * (h : ℕ) = (k : ℝ) + x := by
    rw [hkcast]
    nlinarith
  have hPrefixProfile (r : ZMod (h : ℕ)) : loebResidueProfile U hU q h P r =
      if r ∈ R then (1 : ℝ) else 0 := by
    have hr := loeb_quasiPeriodic_residue_profile U hU q P p.period p.left h hd hker r
    change loebResidueProfile U hU q h P r =
      (if r = prefixAnchor then (h : ℕ) * (μ p.left.active).toReal
        else if r ∈ φ '' P then 1 else 0) at hr
    rw [hzero, ENNReal.toReal_zero, mul_zero, hPrefixCarrier] at hr
    by_cases heq : r = prefixAnchor
    · subst r
      simpa [R] using hr
    · simpa [R, heq] using hr
  have hPm : MeasurableSet P :=
    p.left.partition.symm ▸ (p.left.background_measurable.union p.left.active_measurable)
  have hPmask : P =ᵐ[μ] φ ⁻¹' (R : Set _) := by
    have hmask := loeb_ae_eq_shifted_mask_of_full_profile U hU q h hd P hPm R 0
      (by simpa only [sub_zero] using hPrefixProfile)
    have himage : R.image (fun r : ZMod (h : ℕ) => r - 0) = R := by
      ext r
      simp
    simpa only [himage] using hmask
  have hBmask : internalSet U
      (fun n => (cyclicWindow B 0 (q n : ℕ) : Set (ZMod (q n : ℕ))))
      =ᵐ[μ] φ ⁻¹' (R : Set _) := hPactual.symm.trans hPmask
  refine ⟨h, R, k, x, hd, hker, ?_, hxpos, hxlt, htotal⟩
  intro r
  have hr := actual_window_profile_of_residue_mask U hU q h hd B (fun _ => 0) R hBmask r
  simpa only [Nat.cast_zero, finiteValue_const, add_zero, Finset.image_id'] using hr

theorem finite_full_preimage_add_image
    {G F : Type*} [AddCommGroup G] [Fintype G] [DecidableEq G]
    [AddCommGroup F] [DecidableEq F]
    (φ : G →+ F) (P : Finset F) (S : Finset G) :
    (Finset.univ.filter (fun x : G => φ x ∈ P)) + S =
      Finset.univ.filter (fun x : G => φ x ∈ P + S.image φ) := by
  ext z
  constructor
  · intro hz
    obtain ⟨x, hx, s, hs, rfl⟩ := Finset.mem_add.mp hz
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_univ _, ?_⟩
    rw [map_add]
    exact Finset.add_mem_add (Finset.mem_filter.mp hx).2
      (Finset.mem_image.mpr ⟨s, hs, rfl⟩)
  · intro hz
    obtain ⟨p, hp, t, ht, hpt⟩ := Finset.mem_add.mp (Finset.mem_filter.mp hz).2
    obtain ⟨s, hs, rfl⟩ := Finset.mem_image.mp ht
    apply Finset.mem_add.mpr
    refine ⟨z - s, Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩,
      s, hs, sub_add_cancel z s⟩
    rw [map_sub, ← hpt, add_sub_cancel_right]
    exact hp

theorem natural_refined_baseline_capacity
    (m h : ℕ+) (hhm : (h : ℕ) ∣ (m : ℕ))
    (P : Finset (ZMod (h : ℕ))) (B : Set ℕ) :
    (((Finset.univ.filter (fun r : ZMod (m : ℕ) => naturalCyclicProjection m h r ∈ P) +
      residues (m : ℕ) B).card : ℝ) / (m : ℕ)) =
      ((P + residues (h : ℕ) B).card : ℝ) / (h : ℕ) := by
  classical
  rw [finite_full_preimage_add_image]
  rw [residues_image_of_natCast m h (naturalCyclicProjection m h)
    (naturalCyclicProjection_natCast m h hhm) B]
  exact natural_preimage_capacity m h hhm (P + residues (h : ℕ) B)

theorem actual_zero_prefix_indicator_refines
    (U : Ultrafilter ℕ) (hU : (U : Filter ℕ) ≤ atTop) (q : ℕ → ℕ+)
    (m h : ℕ+) (hdm : ∀ᶠ n in U, (m : ℕ) ∣ (q n : ℕ))
    (hhm : (h : ℕ) ∣ (m : ℕ)) (A : Set ℕ) (R : Finset (ZMod (h : ℕ)))
    (hR : ∀ r, actualWindowProfile U hU q h A (fun _ => 0) r =
      if r ∈ R then (1 : ℝ) else 0) :
    ∀ r : ZMod (m : ℕ), actualWindowProfile U hU q m A (fun _ => 0) r =
      if naturalCyclicProjection m h r ∈ R then (1 : ℝ) else 0 := by
  classical
  let T := Finset.univ.filter (fun r : ZMod (m : ℕ) => naturalCyclicProjection m h r ∈ R)
  have hdh : ∀ᶠ n in U, (h : ℕ) ∣ (q n : ℕ) :=
    hdm.mono fun _ hn => dvd_trans hhm hn
  have hmask := actual_window_mask_of_indicator_profile U hU q h hdh A (fun _ => 0) R hR
  rw [windowResidueMap_preimage] at hmask
  simp only [Nat.cast_zero, finiteValue_const, sub_zero, Finset.image_id'] at hmask
  have hT : (naturalCyclicProjection m h) ⁻¹' (R : Set _) = (T : Set _) := by
    ext r
    simp [T]
  rw [natural_quotient_preimage_composition U q m h hdm hhm (R : Set _), hT] at hmask
  intro r
  have hp := actual_window_profile_of_residue_mask U hU q m hdm A (fun _ => 0) T hmask r
  simpa only [Nat.cast_zero, finiteValue_const, add_zero, Finset.image_id',
    T, Finset.mem_filter, Finset.mem_univ, true_and] using hp

theorem loeb_two_coarse_null_prefixes_impossible
    (U : Ultrafilter ℕ) (hU : (U : Filter ℕ) ≤ atTop) (q : ℕ → ℕ+)
    (hq : Tendsto (fun n => (q n : ℕ)) atTop atTop)
    (m hA hB : ℕ+) (hdm : ∀ᶠ n in U, (m : ℕ) ∣ (q n : ℕ))
    (hAm : (hA : ℕ) ∣ (m : ℕ)) (hBm : (hB : ℕ) ∣ (m : ℕ))
    (A B : Set ℕ) (a b : ℝ) (ha : 0 < a) (hb : 0 < b)
    (hmA : (loebMeasure U hU (internalSet U
      (fun n => (cyclicWindow A 0 (q n : ℕ) : Set (ZMod (q n : ℕ)))))).toReal = a)
    (hmB : (loebMeasure U hU (internalSet U
      (fun n => (cyclicWindow B 0 (q n : ℕ) : Set (ZMod (q n : ℕ)))))).toReal = b)
    (hmC : (loebMeasure U hU (internalSet U
      (fun n => (cyclicWindow (A + B) 0 (q n : ℕ) : Set (ZMod (q n : ℕ)))))).toReal = a + b)
    (hgap : a + b < gamma A B)
    (P : Finset (ZMod (hA : ℕ))) (Q : Finset (ZMod (hB : ℕ)))
    (hPA : ∀ r, actualWindowProfile U hU q hA A (fun _ => 0) r =
      if r ∈ P then (1 : ℝ) else 0)
    (hQB : ∀ r, actualWindowProfile U hU q hB B (fun _ => 0) r =
      if r ∈ Q then (1 : ℝ) else 0)
    (kA kB : ℕ) (xA xB : ℝ)
    (hxA : 0 < xA) (hxAone : xA < 1) (hxB : 0 < xB) (hxBone : xB < 1)
    (hpartialA : (a + b) * (hA : ℕ) = (kA : ℝ) + xA)
    (hpartialB : (a + b) * (hB : ℕ) = (kB : ℝ) + xB) : False := by
  classical
  let Pm := Finset.univ.filter
    (fun r : ZMod (m : ℕ) => naturalCyclicProjection m hA r ∈ P)
  let Qm := Finset.univ.filter
    (fun r : ZMod (m : ℕ) => naturalCyclicProjection m hB r ∈ Q)
  have hPm : ∀ r, actualWindowProfile U hU q m A (fun _ => 0) r =
      if r ∈ Pm then (1 : ℝ) else 0 := by
    simpa only [Pm, Finset.mem_filter, Finset.mem_univ, true_and] using
      actual_zero_prefix_indicator_refines U hU q m hA hdm hAm A P hPA
  have hQm : ∀ r, actualWindowProfile U hU q m B (fun _ => 0) r =
      if r ∈ Qm then (1 : ℝ) else 0 := by
    simpa only [Qm, Finset.mem_filter, Finset.mem_univ, true_and] using
      actual_zero_prefix_indicator_refines U hU q m hB hdm hBm B Q hQB
  have hleft : ((Pm + residues (m : ℕ) B).card : ℝ) / (m : ℕ) =
      ((P + residues (hA : ℕ) B).card : ℝ) / (hA : ℕ) :=
    natural_refined_baseline_capacity m hA hAm P B
  have hright : ((residues (m : ℕ) A + Qm).card : ℝ) / (m : ℕ) =
      ((Q + residues (hB : ℕ) A).card : ℝ) / (hB : ℕ) := by
    simpa only [add_comm] using natural_refined_baseline_capacity m hB hBm Q A
  exact loeb_two_null_prefix_frames_impossible U hU q hq m hdm A B a b ha hb
    hmA hmB hmC hgap Pm Qm hPm hQm hA hB
    (P + residues (hA : ℕ) B).card (Q + residues (hB : ℕ) A).card
    kA kB xA xB hxA hxAone hxB hxBone hpartialA hpartialB hleft hright

theorem loeb_two_null_prefix_models_force_periodic
    (U : Ultrafilter ℕ) (hU : (U : Filter ℕ) ≤ atTop)
    (qA qB : ℕ → ℕ+) (H : ℕ → ℕ)
    (hdivA : ∀ h : ℕ+, ∀ᶠ n in atTop, (h : ℕ) ∣ (qA n : ℕ))
    (hdivB : ∀ h : ℕ+, ∀ᶠ n in atTop, (h : ℕ) ∣ (qB n : ℕ))
    (hqA : Tendsto (fun n => (qA n : ℕ)) atTop atTop)
    (hH : ∀ n, 0 < H n) (hHqA : ∀ n, H n ≤ (qA n : ℕ))
    (hHqB : ∀ n, H n ≤ (qB n : ℕ))
    (hqAgap : Tendsto (fun n => (((qA n : ℕ) - H n : ℕ) : ℝ) / (qA n : ℕ))
      atTop (𝓝 0))
    (hqBgap : Tendsto (fun n => (((qB n : ℕ) - H n : ℕ) : ℝ) / (qB n : ℕ))
      atTop (𝓝 0))
    (A B : Set ℕ) (start : ℕ → ℕ) (a b : ℝ) (ha : 0 < a) (hb : 0 < b)
    (hAdensity : HasDensity A a) (hBdensity : HasDensity B b)
    (hCdensity : HasDensity (A + B) (a + b)) (hgap : a + b < gamma A B)
    (prefixBModel movingAModel : Set ((U : Filter ℕ).Product (fun n => ZMod (qA n : ℕ))))
    (prefixAModel movingBModel : Set ((U : Filter ℕ).Product (fun n => ZMod (qB n : ℕ))))
    (pA : QuasiPeriodicPairData (loebMeasure U hU) (internalInnerMeasure U hU)
      prefixBModel movingAModel)
    (pB : QuasiPeriodicPairData (loebMeasure U hU) (internalInnerMeasure U hU)
      prefixAModel movingBModel)
    (hPrefixB : prefixBModel =ᵐ[loebMeasure U hU] internalSet U
      (fun n => (cyclicWindow B 0 (qA n : ℕ) : Set (ZMod (qA n : ℕ)))))
    (hMovingA : movingAModel =ᵐ[loebMeasure U hU] internalSet U
      (fun n => (cyclicWindow A (start n) (qA n : ℕ) : Set (ZMod (qA n : ℕ)))))
    (hPrefixA : prefixAModel =ᵐ[loebMeasure U hU] internalSet U
      (fun n => (cyclicWindow A 0 (qB n : ℕ) : Set (ZMod (qB n : ℕ)))))
    (hMovingB : movingBModel =ᵐ[loebMeasure U hU] internalSet U
      (fun n => (cyclicWindow B (start n) (qB n : ℕ) : Set (ZMod (qB n : ℕ)))))
    (hmPrefixB : (loebMeasure U hU prefixBModel).toReal = b)
    (hmMovingA : (loebMeasure U hU movingAModel).toReal = a)
    (hmPrefixA : (loebMeasure U hU prefixAModel).toReal = a)
    (hmMovingB : (loebMeasure U hU movingBModel).toReal = b)
    (hzeroA : loebMeasure U hU pA.left.active = 0)
    (hzeroB : loebMeasure U hU pB.left.active = 0) :
    (∃ (h : ℕ+) (R : Finset (ZMod (h : ℕ))),
      (∀ᶠ n in U, (h : ℕ) ∣ (qA n : ℕ)) ∧
        internalSet U
          (fun n => (cyclicWindow A (start n) (qA n : ℕ) : Set (ZMod (qA n : ℕ))))
          =ᵐ[loebMeasure U hU]
            (finiteQuotient U (fun n => naturalCyclicProjection (qA n) h)) ⁻¹' (R : Set _)) ∨
    (∃ (h : ℕ+) (R : Finset (ZMod (h : ℕ))),
      (∀ᶠ n in U, (h : ℕ) ∣ (qB n : ℕ)) ∧
        internalSet U
          (fun n => (cyclicWindow B (start n) (qB n : ℕ) : Set (ZMod (qB n : ℕ))))
          =ᵐ[loebMeasure U hU]
            (finiteQuotient U (fun n => naturalCyclicProjection (qB n) h)) ⁻¹' (R : Set _)) := by
  classical
  by_cases hperiodicA : ∃ (h : ℕ+) (R : Finset (ZMod (h : ℕ))),
      (∀ᶠ n in U, (h : ℕ) ∣ (qA n : ℕ)) ∧
        internalSet U
          (fun n => (cyclicWindow A (start n) (qA n : ℕ) : Set (ZMod (qA n : ℕ))))
          =ᵐ[loebMeasure U hU]
            (finiteQuotient U (fun n => naturalCyclicProjection (qA n) h)) ⁻¹' (R : Set _)
  · exact Or.inl hperiodicA
  apply Or.inr
  by_contra hperiodicB
  obtain ⟨hB, Q, kB, xB, _, _, hQB, hxB, hxBone, hpartialB⟩ :=
    loeb_null_prefix_fractional_data U hU qA A B start a b prefixBModel movingAModel
      pA hPrefixB hMovingA hmPrefixB hmMovingA hzeroA hperiodicA
  obtain ⟨hA, P, kA, xA, _, _, hPA, hxA, hxAone, hpartialA⟩ :=
    loeb_null_prefix_fractional_data U hU qB B A start b a prefixAModel movingBModel
      pB hPrefixA hMovingB hmPrefixA hmMovingB hzeroB hperiodicB
  have hPAtqA : ∀ r, actualWindowProfile U hU qA hA A (fun _ => 0) r =
      if r ∈ P then (1 : ℝ) else 0 := by
    intro r
    exact (constrained_actual_window_profiles_agree U hU A (fun _ => 0) H qA qB
      hH hHqA hHqB hqAgap hqBgap hA (hdivA hA) (hdivB hA) r).trans (hPA r)
  let m : ℕ+ := PNat.lcm hA hB
  have hAm : (hA : ℕ) ∣ (m : ℕ) := Nat.dvd_lcm_left (hA : ℕ) (hB : ℕ)
  have hBm : (hB : ℕ) ∣ (m : ℕ) := Nat.dvd_lcm_right (hA : ℕ) (hB : ℕ)
  exact loeb_two_coarse_null_prefixes_impossible U hU qA hqA m hA hB
    ((hdivA m).filter_mono hU) hAm hBm A B a b ha hb
    (loeb_zero_window_mass_of_density U hU qA hqA A a hAdensity)
    (loeb_zero_window_mass_of_density U hU qA hqA B b hBdensity)
    (loeb_zero_window_mass_of_density U hU qA hqA (A + B) (a + b) hCdensity)
    hgap P Q hPAtqA hQB kA kB xA xB hxA hxAone hxB hxBone
    (by simpa only [add_comm b a] using hpartialA) hpartialB

end Erdos335.Loeb

end
