import Erdos335.CircleCriticalTranslation
import Erdos335.CircleRegularCut
import Erdos335.PeriodicIndicatorInterval
import Mathlib.Analysis.SpecificLimits.Basic

/-!
# Interval structure after a regular cut of a critical circle sumset
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter Topology MeasureTheory
open scoped Pointwise

namespace Erdos335.Loeb

theorem unitCircle_ae_interval_cut_of_localized_critical_pairs
    (S : Set (AddCircle (1 : ℝ))) (hS : MeasurableSet S)
    (hSpos : 0 < volume S) (hcomp : 0 < volume Sᶜ)
    (A B : ℕ → Set (AddCircle (1 : ℝ)))
    (hB : ∀ n, MeasurableSet (B n)) (hpositive : ∀ n, 0 < volume (B n))
    (hsum : ∀ n, A n + B n ≤ᵐ[volume] S)
    (hmass : ∀ n, (volume S).toReal = (volume (A n)).toReal + (volume (B n)).toReal)
    (hlocal : ∀ V ∈ 𝓝 (0 : AddCircle (1 : ℝ)), ∀ᶠ n in atTop, B n - B n ⊆ V) :
    ∃ c a b : ℝ, 0 ≤ a ∧ a < b ∧ b ≤ 1 ∧
      (((↑) : ℝ → AddCircle (1 : ℝ)) ⁻¹' (-(c : AddCircle (1 : ℝ)) +ᵥ S) ∩ Ioo 0 1)
        =ᵐ[volume] Ioo a b := by
  have : Fact (0 < (1 : ℝ)) := ⟨zero_lt_one⟩
  obtain ⟨c, _, hc, hderiv⟩ := exists_unitCircle_regular_cut S hS hcomp
  let R : Set (AddCircle (1 : ℝ)) := -(c : AddCircle (1 : ℝ)) +ᵥ S
  let T : Set ℝ := ((↑) : ℝ → AddCircle (1 : ℝ)) ⁻¹' R
  have hR : MeasurableSet R := by
    dsimp [R]
    rw [vadd_set_eq_neg_preimage]
    exact hS.preimage (measurable_const_add (- -(c : AddCircle (1 : ℝ))))
  have hT : MeasurableSet T := hR.preimage AddCircle.measurable_mk'
  have hmassR : volume R = volume S := by
    dsimp [R]
    rw [vadd_set_eq_neg_preimage, measure_preimage_add]
  have hmem (x : ℝ) : x ∈ T ↔ ((x + c : ℝ) : AddCircle (1 : ℝ)) ∈ S := by
    change (x : AddCircle (1 : ℝ)) ∈ (-(c : AddCircle (1 : ℝ)) +ᵥ S) ↔ _
    rw [vadd_set_eq_neg_preimage]
    simp only [mem_preimage, neg_neg, AddCircle.coe_add, add_comm]
  have hind (x : ℝ) : T.indicator (fun _ => (1 : ℝ)) x =
      S.indicator (fun _ => (1 : ℝ)) ((x + c : ℝ) : AddCircle (1 : ℝ)) := by
    by_cases hx : x ∈ T
    · rw [indicator_of_mem hx, indicator_of_mem ((hmem x).mp hx)]
    · rw [indicator_of_notMem hx, indicator_of_notMem (fun h => hx ((hmem x).mpr h))]
  have hindR (x : ℝ) : T.indicator (fun _ => (1 : ℝ)) x =
      R.indicator (fun _ => (1 : ℝ)) (x : AddCircle (1 : ℝ)) := by
    by_cases hx : (x : AddCircle (1 : ℝ)) ∈ R <;> simp [T, hx]
  have hperiod : Function.Periodic (T.indicator (fun _ => (1 : ℝ))) 1 := by
    intro x
    rw [hind, hind, show x + 1 + c = (x + c) + 1 by ring, AddCircle.coe_add_period]
  have hzero : 0 ∉ T := by
    intro hz
    have h := (hmem 0).mp hz
    exact hc (by simpa only [zero_add] using h)
  have hderivT : HasDerivAt (fun y => ∫ x in 0..y, T.indicator (fun _ => (1 : ℝ)) x) 0 0 := by
    simpa only [hind] using hderiv
  have hpositiveT : 0 < volume (T ∩ Ioo (0 : ℝ) 1) := by
    rw [volume_unitCircle_lift_openInterval R hR, hmassR]
    exact hSpos
  let ε : ℕ → ℝ := fun n => 1 / ((n : ℝ) + 1)
  have hε (n : ℕ) : 0 < ε n := by dsimp [ε]; positivity
  have hεlimit : Tendsto ε atTop (𝓝 0) := tendsto_one_div_add_atTop_nhds_zero_nat
  obtain ⟨t, ht, hlimit, hloss⟩ := exists_unitCircle_sharp_translation_sequence S hS A B
    hB hpositive hsum hmass hlocal ε hε
  have hcoefficient : Tendsto (fun n => 1 + ε n) atTop (𝓝 1) := by
    simpa only [add_zero] using tendsto_const_nhds.add hεlimit
  obtain ⟨a, b, ha, hab, hb, heq⟩ := periodic_indicator_ae_interval_of_translation_bound
    T hT hperiod hzero hderivT hpositiveT t (fun n => 1 + ε n) hlimit
    (fun n => (ht n).1) (fun n => (ht n).2) hcoefficient (by
      intro n
      simpa only [hindR] using hloss (-(c : AddCircle (1 : ℝ))) n)
  exact ⟨c, a, b, ha, hab, hb, heq⟩

end Erdos335.Loeb
