import Erdos335.NaturalQuotientRefinement
import Erdos335.QuasiPeriodicPeriodRestriction

/-!
# A positive literal saturation gap prevents a singleton active piece
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000

open Filter Set MeasureTheory
open scoped Pointwise ENNReal

noncomputable section

namespace Erdos335.Loeb

local instance literalActiveSizeLoebSpace (U : Ultrafilter ℕ) (q : ℕ → ℕ+) :
    MeasurableSpace ((U : Filter ℕ).Product (fun n => ZMod (q n : ℕ))) := loebMeasurableSpace U

theorem loeb_literal_active_not_subsingleton
    (U : Ultrafilter ℕ) (hU : (U : Filter ℕ) ≤ atTop) (q : ℕ → ℕ+)
    (hdiv : ∀ h : ℕ+, ∀ᶠ n in U, (h : ℕ) ∣ (q n : ℕ))
    (A : Set ℕ) (E : ℕ → Set ℕ) (hEA : ∀ᶠ n in U, E n ⊆ A)
    (hexhaust : ∀ a ∈ A, ∀ᶠ n in U, a ∈ E n)
    (a δ : ℝ) (hδ : 0 < δ)
    (hmass : (loebMeasure U hU (internalSet U
      (fun n => ((↑) : ℕ → ZMod (q n : ℕ)) '' E n))).toReal = a)
    (hcapacity : ∀ h : ℕ+, a + δ ≤ ((residues (h : ℕ) A).card : ℝ) / (h : ℕ))
    (H : AddSubgroup ((U : Filter ℕ).Product (fun n => ZMod (q n : ℕ))))
    (hHm : MeasurableSet (H : Set ((U : Filter ℕ).Product (fun n => ZMod (q n : ℕ)))))
    (hHpos : 0 < loebMeasure U hU (H : Set ((U : Filter ℕ).Product (fun n => ZMod (q n : ℕ)))))
    (p : QuasiPeriodicDecomposition (loebMeasure U hU) H
      (internalSet U (fun n => ((↑) : ℕ → ZMod (q n : ℕ)) '' E n))) :
    ¬p.active.Subsingleton := by
  intro hsingle
  let G := (U : Filter ℕ).Product (fun n => ZMod (q n : ℕ))
  let μ : Measure G := loebMeasure (X := fun n => ZMod (q n : ℕ)) U hU
  obtain ⟨m, ρ, hρ, hker, _⟩ := positive_measurable_subgroup_is_natural_finite_kernel U hU q H hHm hHpos
  have heq := finiteQuotient_eq_of_eventually_natural U q m ρ
    (fun n => naturalCyclicProjection (q n) m) (hρ.mono fun n hn => hn.2)
    ((hdiv m).mono fun n hn k => naturalCyclicProjection_natCast (q n) m hn k)
  rw [heq] at hker
  obtain ⟨n, hn⟩ := exists_nat_gt (1 / δ)
  have hn0 : 0 < n := by
    have hp : (0 : ℝ) < n := (one_div_pos.mpr hδ).trans hn
    exact_mod_cast hp
  let k : ℕ+ := ⟨n, hn0⟩
  let L := m * k
  have hmL : (m : ℕ) ∣ (L : ℕ) := ⟨k, rfl⟩
  let f := finiteQuotient U (fun i => naturalCyclicProjection (q i) L)
  let K := f.ker
  have hKH : K ≤ H := by
    intro x hx
    rw [← hker]
    change finiteQuotient U (fun i => naturalCyclicProjection (q i) m) x = 0
    have hc := congrArg (fun g => g x) (finiteQuotient_natural_refinement U q L m (hdiv L) hmL)
    rw [← hc]
    change naturalCyclicProjection L m (f x) = 0
    rw [show f x = 0 from hx, map_zero]
  have hKm : MeasurableSet (K : Set G) := by
    change MeasurableSet ((finiteQuotient U (fun i => naturalCyclicProjection (q i) L)).ker : Set G)
    rw [finiteQuotient_ker]
    exact measurable_internalSet U _
  have hKmass : μ (K : Set G) = (1 : ℝ≥0∞) / (L : ℕ) := by
    change loebMeasure U hU ((finiteQuotient U (fun i => naturalCyclicProjection (q i) L)).ker : Set G) = _
    rw [finiteQuotient_ker, loebMeasure_internalSubgroup_of_eventually_quotients U hU
      (fun i => naturalCyclicProjection (q i) L)
      ((hdiv L).mono fun i hi => naturalCyclicProjection_surjective (q i) L hi)]
    simp
  have hKpos : 0 < μ (K : Set G) := by
    rw [hKmass]
    exact ENNReal.div_pos (by norm_num) (by simp)
  obtain ⟨x, hx⟩ := p.active_nonempty
  have hactive : p.active ⊆ x +ᵥ (K : Set G) := by
    intro y hy
    have hyx : y = x := hsingle hy hx
    subst y
    exact ⟨0, K.zero_mem, by simp⟩
  let p' := p.restrictPeriod hKH x hactive
  have hgap := loeb_literal_exhaustion_saturation_gap U hU q A E hEA hexhaust a δ hmass hcapacity K hKm hKpos
  have hbound := loeb_quasiPeriodic_period_bound_of_saturation_gap U hU q
    (internalSet U (fun i => ((↑) : ℕ → ZMod (q i : ℕ)) '' E i)) K p' δ hgap
  rw [hKmass, ENNReal.toReal_div, ENNReal.toReal_one, ENNReal.toReal_natCast] at hbound
  have hm1 : (1 : ℝ) ≤ (m : ℕ) := by exact_mod_cast m.pos
  have hLn : (n : ℝ) ≤ (L : ℕ) := by
    change (n : ℝ) ≤ ((m : ℕ) * n : ℕ)
    push_cast
    nlinarith
  have hLnδ := mul_le_mul_of_nonneg_left hLn hδ.le
  have hnδ : (1 : ℝ) < δ * n := by
    have h := (div_lt_iff₀ hδ).mp hn
    nlinarith
  have hLpos : (0 : ℝ) < (L : ℕ) := by exact_mod_cast L.pos
  have hsmall : (1 : ℝ) / (L : ℕ) < δ := (div_lt_iff₀ hLpos).mpr (by linarith)
  exact not_le_of_gt hsmall hbound

end Erdos335.Loeb

end
