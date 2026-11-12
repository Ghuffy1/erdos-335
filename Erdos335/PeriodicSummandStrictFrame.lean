import Erdos335.LoebFixedPeriodicCore
import Erdos335.LoebPrefixDensityConverse
import Erdos335.FiniteNaturalCriticalCore
import Erdos335.LoebLocalDeficitProfiles

/-!
# Ordinary finite frames for a periodic summand with a strict baseline
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1500000

open Filter Set Topology MeasureTheory
open Erdos335.IntermediateScale
open scoped Pointwise ENNReal

noncomputable section

namespace Erdos335.Loeb

local instance periodicStrictFrameLoebSpace (U : Ultrafilter ℕ) (q : ℕ → ℕ+) :
    MeasurableSpace ((U : Filter ℕ).Product (fun n => ZMod (q n : ℕ))) := loebMeasurableSpace U

theorem periodic_summand_strict_frame
    (A B : Set ℕ) (a b : ℝ) (hA : A ⊆ Set.Ioi 0) (hB : B ⊆ Set.Ioi 0)
    (ha : 0 < a) (hb : 0 < b) (hdA : HasDensity A a) (hdB : HasDensity B b)
    (hdC : HasDensity (A + B) (a + b)) (hgap : a + b < gamma A B)
    (m : ℕ+) (P : Finset (ZMod (m : ℕ))) (hAP : DensityEquivalent A (periodicSet P))
    (hstrict : ((P + residues (m : ℕ) B).card : ℝ) / (m : ℕ) < a + b) :
    ∃ (h : ℕ+) (i j : ZMod (h : ℕ)) (d : ℝ),
      (h : ℕ) ∣ (m : ℕ) ∧ i ∈ residues (h : ℕ) A ∧ j ∈ residues (h : ℕ) B ∧
      (residues (h : ℕ) A + residues (h : ℕ) B).card + 1 =
        (residues (h : ℕ) A).card + (residues (h : ℕ) B).card ∧
      (∀ r ∈ residues (h : ℕ) A, r ≠ i → HasDensity (residueFiber A r) ((1 : ℝ) / (h : ℕ))) ∧
      HasDensity (residueFiber A i) 0 ∧
      (∀ r ∈ residues (h : ℕ) B, r ≠ j → HasDensity (residueFiber B r) ((1 : ℝ) / (h : ℕ))) ∧
      HasDensity (residueFiber B j) d ∧ 0 < d ∧ d < (1 : ℝ) / (h : ℕ) ∧
      (∀ r ∈ residues (h : ℕ) A, ∀ t ∈ residues (h : ℕ) B,
        r + t = i + j → r = i ∧ t = j) := by
  classical
  have hmpos : (0 : ℝ) < (m : ℕ) := by exact_mod_cast m.pos
  have hPa : a = (P.card : ℝ) / (m : ℕ) :=
    hdA.unique (hAP.symm.hasDensity (hasDensity_periodicSet P))
  have hPne : P.Nonempty := by
    apply Finset.card_pos.mp
    by_contra hn
    have hz : P.card = 0 := by omega
    rw [hz, Nat.cast_zero, zero_div] at hPa
    linarith
  have hTb : b ≤ ((residues (m : ℕ) B).card : ℝ) / (m : ℕ) := hdB.le_residue_cover hB _
  have hTne : (residues (m : ℕ) B).Nonempty := by
    apply Finset.card_pos.mp
    by_contra hn
    have hz : (residues (m : ℕ) B).card = 0 := by omega
    rw [hz, Nat.cast_zero, zero_div] at hTb
    linarith
  have hsmall : (P + residues (m : ℕ) B).card < P.card + (residues (m : ℕ) B).card := by
    have hreal : ((P + residues (m : ℕ) B).card : ℝ) / (m : ℕ) <
        ((P.card : ℝ) + (residues (m : ℕ) B).card) / (m : ℕ) := by
      rw [add_div, ← hPa]
      linarith
    exact_mod_cast (div_lt_div_iff_of_pos_right hmpos).mp hreal
  obtain ⟨h, hhm, hcard0, hpre, hratio⟩ := exists_finite_natural_critical_core m P
    (residues (m : ℕ) B) hPne hTne hsmall
  let π := naturalCyclicProjection m h
  let S := P.image π
  let R := residues (h : ℕ) A
  let T := residues (h : ℕ) B
  let q := positiveMultipleSequence m
  have hq : Tendsto (fun n => (q n : ℕ)) atTop atTop := positiveMultipleSequence_tendsto m
  have hTimage : (residues (m : ℕ) B).image π = T :=
    residues_image_of_natCast m h π (fun n => naturalCyclicProjection_natCast m h hhm n) B
  have himage : (P + residues (m : ℕ) B).image π = S + T := by
    apply Finset.coe_injective
    rw [Finset.coe_image, Finset.coe_add, Set.image_add, ← Finset.coe_image,
      ← Finset.coe_image, hTimage, Finset.coe_add]
  have hcard : (S + T).card + 1 = S.card + T.card := by
    change ((P + residues (m : ℕ) B).image π).card + 1 = S.card +
      ((residues (m : ℕ) B).image π).card at hcard0
    simpa only [himage, hTimage] using hcard0
  have hdeficit : ((S + T).card : ℝ) < ((h : ℕ) : ℝ) * (a + b) := by
    have hquotient : ((S + T).card : ℝ) / (h : ℕ) < a + b := by
      rw [← himage, hratio]
      exact hstrict
    have hh : (0 : ℝ) < (h : ℕ) := by exact_mod_cast h.pos
    simpa only [mul_comm] using (div_lt_iff₀ hh).mp hquotient
  have local_data (U : Ultrafilter ℕ) (hU : (U : Filter ℕ) ≤ atTop) :
      ∃ i j : ZMod (h : ℕ), i ∈ R ∧ j ∈ T ∧ i ∉ S ∧ R = insert i S ∧
        (R + T) \ (S + T) = {i + j} ∧
        (∀ r ∈ S, actualWindowProfile U hU q h A (fun _ => 0) r = 1) ∧
        (∀ r ∈ T.erase j, actualWindowProfile U hU q h B (fun _ => 0) r = 1) ∧
        actualWindowProfile U hU q h B (fun _ => 0) j = ((h : ℕ) : ℝ) * b - ((T.card : ℝ) - 1) ∧
        ((h : ℕ) : ℝ) * b - ((T.card : ℝ) - 1) < 1 ∧
        (∀ r ∈ R, ∀ t ∈ T, r + t = i + j → r = i ∧ t = j) := by
    have hdm : ∀ᶠ n in U, (m : ℕ) ∣ (q n : ℕ) :=
      Eventually.of_forall fun n => ⟨n + 1, rfl⟩
    have hdh : ∀ᶠ n in U, (h : ℕ) ∣ (q n : ℕ) := hdm.mono fun n hn => dvd_trans hhm hn
    have mass (V : Set ℕ) (d : ℝ) (hV : HasDensity V d) :
        (loebMeasure U hU (internalSet U
          (fun n => (cyclicWindow V 0 (q n : ℕ) : Set (ZMod (q n : ℕ)))))).toReal = d := by
      apply loeb_finset_measure_eq U hU q _ d
      have hv := ((hasDensity_iff_prefixCount V d).mp hV).comp hq
      simpa only [Function.comp_def, cyclicWindow_card_eq_prefixCount, tailShift,
        add_zero, setOf_mem_eq] using hv
    have hmask := loeb_prefix_mask_of_density_equivalence U hU q hq m hdm A hA P hAP
    have hPprofile := actual_window_profile_of_residue_mask U hU q m hdm A (fun _ => 0) P hmask
    simp only [finiteValue_const, Nat.cast_zero, add_zero, Finset.image_id'] at hPprofile
    obtain ⟨hS, hzero, hfull⟩ := loeb_fixed_periodic_core_profiles U hU q hq m h hdm hhm A B
      (fun _ => 0) P hPprofile hpre
    exact actual_window_local_deficit_template U hU q hq h hdh A B (fun _ => 0) a b
      (mass A a hdA) (mass B b hdB) (mass (A + B) (a + b) hdC) hgap S hS hcard hzero hfull hdeficit
  let U₀ : Ultrafilter ℕ := Ultrafilter.of atTop
  have hU₀ : (U₀ : Filter ℕ) ≤ atTop := Ultrafilter.of_le atTop
  obtain ⟨i, j, hi, hj, hiS, hR, hdiff, hAf, hBf, hactive, hactiveLt, hunique⟩ := local_data U₀ hU₀
  have fixed (U : Ultrafilter ℕ) (hU : (U : Filter ℕ) ≤ atTop) :
      (∀ r ∈ S, actualWindowProfile U hU q h A (fun _ => 0) r = 1) ∧
      (∀ r ∈ T.erase j, actualWindowProfile U hU q h B (fun _ => 0) r = 1) ∧
      actualWindowProfile U hU q h B (fun _ => 0) j = ((h : ℕ) : ℝ) * b - ((T.card : ℝ) - 1) := by
    obtain ⟨i', j', hi', _, hiS', _, hdiff', hAf', hBf', hactive', _, _⟩ := local_data U hU
    have hieq : i' = i := by
      rw [hR] at hi'
      exact (Finset.mem_insert.mp hi').resolve_right hiS'
    subst i'
    have hsum : i + j' = i + j := by
      have heq : ({i + j'} : Finset (ZMod (h : ℕ))) = {i + j} := hdiff'.symm.trans hdiff
      exact Finset.singleton_injective heq
    have hjeq : j' = j := add_left_cancel hsum
    subst j'
    exact ⟨hAf', hBf', hactive'⟩
  have hzeroA (U : Ultrafilter ℕ) (hU : (U : Filter ℕ) ≤ atTop) :
      actualWindowProfile U hU q h A (fun _ => 0) i = 0 := by
    have hdm : ∀ᶠ n in U, (m : ℕ) ∣ (q n : ℕ) := Eventually.of_forall fun n => ⟨n + 1, rfl⟩
    have hmask := loeb_prefix_mask_of_density_equivalence U hU q hq m hdm A hA P hAP
    have hPprofile := actual_window_profile_of_residue_mask U hU q m hdm A (fun _ => 0) P hmask
    simp only [finiteValue_const, Nat.cast_zero, add_zero, Finset.image_id'] at hPprofile
    exact (loeb_fixed_periodic_core_profiles U hU q hq m h hdm hhm A B (fun _ => 0) P hPprofile hpre).2.1 i hiS
  have measure_of_profile (V : Set ℕ) (r : ZMod (h : ℕ)) (v : ℝ)
      (hp : ∀ (U : Ultrafilter ℕ) (hU : (U : Filter ℕ) ≤ atTop),
        actualWindowProfile U hU q h V (fun _ => 0) r = v) (hV : V ⊆ Set.Ioi 0) :
      HasDensity (residueFiber V r) (v / (h : ℕ)) := by
    apply residueFiber_density_of_all_prefix_measures V hV m h hhm r (v / (h : ℕ))
    intro U hU
    have hv := hp U hU
    simp only [actualWindowProfile, loebResidueProfile, finiteValue_const, Nat.cast_zero, sub_zero] at hv
    exact (eq_div_iff (by exact_mod_cast h.ne_zero : ((h : ℕ) : ℝ) ≠ 0)).mpr (by
      simpa only [mul_comm] using hv)
  have hwhole : (R + T).card + 1 = R.card + T.card := by
    have hsub := Finset.add_subset_add (show S ⊆ R by rw [hR]; exact Finset.subset_insert _ _) (Finset.Subset.refl T)
    have hd := Finset.card_sdiff_of_subset hsub
    rw [hdiff, Finset.card_singleton] at hd
    have hc := Finset.card_le_card hsub
    have hr : R.card = S.card + 1 := by rw [hR, Finset.card_insert_of_notMem hiS]
    omega
  let v := ((h : ℕ) : ℝ) * b - ((T.card : ℝ) - 1)
  have hvpos : 0 < v := by
    have hBound : ((h : ℕ) : ℝ) * a ≤ S.card := by
      have hmask := loeb_prefix_mask_of_density_equivalence U₀ hU₀ q hq m
        (Eventually.of_forall fun n => ⟨n + 1, rfl⟩) A hA P hAP
      have hPprofile := actual_window_profile_of_residue_mask U₀ hU₀ q m
        (Eventually.of_forall fun n => ⟨n + 1, rfl⟩) A (fun _ => 0) P hmask
      simp only [finiteValue_const, Nat.cast_zero, add_zero, Finset.image_id'] at hPprofile
      have hSzero := (loeb_fixed_periodic_core_profiles U₀ hU₀ q hq m h
        (Eventually.of_forall fun n => ⟨n + 1, rfl⟩) hhm A B (fun _ => 0) P hPprofile hpre).2.1
      have hAprofile : ∀ r, actualWindowProfile U₀ hU₀ q h A (fun _ => 0) r =
          if r ∈ S then (1 : ℝ) else 0 := by
        intro r
        by_cases hr : r ∈ S
        · rw [if_pos hr]; exact hAf r hr
        · rw [if_neg hr]; exact hSzero r hr
      have hmA := actual_window_indicator_mass U₀ hU₀ q h
        (Eventually.of_forall fun n => dvd_mul_of_dvd_left hhm (n + 1)) A (fun _ => 0) S hAprofile
      have hdensity := ((hasDensity_iff_prefixCount A a).mp hdA).comp hq
      have hmActual := loeb_finset_measure_eq U₀ hU₀ q (fun n => cyclicWindow A 0 (q n : ℕ)) a
        (by simpa only [Function.comp_def, cyclicWindow_card_eq_prefixCount, tailShift, add_zero, setOf_mem_eq] using hdensity)
      rw [hmActual] at hmA
      have heq := (eq_div_iff (by exact_mod_cast h.ne_zero : ((h : ℕ) : ℝ) ≠ 0)).mp hmA
      nlinarith
    have hcardReal : ((S + T).card : ℝ) + 1 = (S.card : ℝ) + T.card := by exact_mod_cast hcard
    dsimp only [v]
    nlinarith
  have hhpos : (0 : ℝ) < (h : ℕ) := by exact_mod_cast h.pos
  refine ⟨h, i, j, v / (h : ℕ), hhm, hi, hj, hwhole, ?_, ?_, ?_, ?_,
    div_pos hvpos hhpos, (div_lt_div_iff_of_pos_right hhpos).mpr hactiveLt, hunique⟩
  · intro r hr hri
    have hrS : r ∈ S := by
      change r ∈ R at hr
      rw [hR] at hr
      exact (Finset.mem_insert.mp hr).resolve_left hri
    exact measure_of_profile A r 1 (fun U hU => (fixed U hU).1 r hrS) hA
  · simpa only [zero_div] using measure_of_profile A i 0 hzeroA hA
  · intro r hr hrj
    exact measure_of_profile B r 1 (fun U hU => (fixed U hU).2.1 r (Finset.mem_erase.mpr ⟨hrj, hr⟩)) hB
  · exact measure_of_profile B j v (fun U hU => (fixed U hU).2.2) hB

end Erdos335.Loeb

end
