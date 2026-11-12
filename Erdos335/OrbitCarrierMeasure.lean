import Erdos335.ArcDensity
import Erdos335.OrbitTranslateDensity
import Mathlib.MeasureTheory.Measure.Portmanteau

/-!
# Haar measure bounds for carriers of an irrational integer orbit

Private proof development. Verification status is recorded separately.
The bounds use the existing empirical equidistribution theorem and the
closed-set and open-set conclusions of the Portmanteau theorem.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000

open Filter Set Topology MeasureTheory
open scoped ENNReal Pointwise

noncomputable section

namespace Erdos335.Proposed

private theorem empirical_orbit_measure_eq_prefix
    (a : AddCircle (1 : ℝ)) (S : Set (AddCircle (1 : ℝ)))
    (hS : MeasurableSet S) (N : ℕ) :
    (NumStability.empiricalProbability a N : Measure (AddCircle (1 : ℝ))) S =
      ENNReal.ofReal ((prefixCount {n : ℕ | n • a ∈ S} (N + 1) : ℝ) / (N + 1 : ℕ)) := by
  rw [NumStability.empiricalProbability_apply a N hS, fin_count_eq_prefixCount]
  rw [ENNReal.ofReal_div_of_pos (by positivity)]
  simp only [ENNReal.ofReal_natCast]

private theorem density_successor_prefix_tendsto
    (E : Set ℕ) (x : ℝ) (hE : HasDensity E x) :
    Tendsto (fun N => (prefixCount E (N + 1) : ℝ) / (N + 1 : ℕ)) atTop (𝓝 x) :=
  (tendsto_add_atTop_iff_nat 1).mpr ((hasDensity_iff_prefixCount E x).mp hE)

theorem density_le_closed_orbit_carrier_measure
    (θ : ℝ) (hθ : Irrational θ) (E : Set ℕ) (x : ℝ) (hE : HasDensity E x)
    (K : Set (AddCircle (1 : ℝ))) (hK : IsClosed K)
    (hcarrier : ∀ n ∈ E, n • (θ : AddCircle (1 : ℝ)) ∈ K) :
    x ≤ (volume K).toReal := by
  classical
  letI : IsProbabilityMeasure (volume : Measure (AddCircle (1 : ℝ))) :=
    ⟨by simpa using AddCircle.measure_univ (1 : ℝ)⟩
  let a : AddCircle (1 : ℝ) := (θ : AddCircle (1 : ℝ))
  let P : Set ℕ := {n | n • a ∈ K}
  have hcounts (N : ℕ) : prefixCount E (N + 1) ≤ prefixCount P (N + 1) := by
    unfold prefixCount
    apply Finset.card_le_card
    intro n hn
    obtain ⟨hnN, hnE⟩ := Finset.mem_filter.mp hn
    exact Finset.mem_filter.mpr ⟨hnN, hcarrier n hnE⟩
  have hcomparison (N : ℕ) :
      ENNReal.ofReal ((prefixCount E (N + 1) : ℝ) / (N + 1 : ℕ)) ≤
        (NumStability.empiricalProbability a N : Measure (AddCircle (1 : ℝ))) K := by
    rw [empirical_orbit_measure_eq_prefix a K hK.measurableSet N]
    apply ENNReal.ofReal_le_ofReal
    exact div_le_div_of_nonneg_right (by exact_mod_cast hcounts N) (by positivity)
  have hlimit := (ENNReal.continuous_ofReal.tendsto x).comp
    (density_successor_prefix_tendsto E x hE)
  dsimp only [Function.comp_def] at hlimit
  have hmono := limsup_le_limsup (f := atTop) (Eventually.of_forall hcomparison)
  rw [hlimit.limsup_eq] at hmono
  have hport :
      atTop.limsup (fun N =>
        (NumStability.empiricalProbability a N : Measure (AddCircle (1 : ℝ))) K) ≤ volume K := by
    have hraw := ProbabilityMeasure.limsup_measure_closed_le_of_tendsto
      (NumStability.empiricalProbability_tendsto_haar (irrational_addOrder hθ)) hK
    change atTop.limsup (fun N =>
      (NumStability.empiricalProbability (θ : AddCircle (1 : ℝ)) N :
        Measure (AddCircle (1 : ℝ))) K) ≤ AddCircle.haarAddCircle K at hraw
    rw [NumStability.haar_eq_volume_unit] at hraw
    exact hraw
  exact (ENNReal.ofReal_le_iff_le_toReal (measure_ne_top volume K)).mp (hmono.trans hport)

theorem open_orbit_measure_le_density_of_negligible_excess
    (θ : ℝ) (hθ : Irrational θ) (O : Set (AddCircle (1 : ℝ))) (hO : IsOpen O)
    (C : Set ℕ) (c : ℝ) (hC : HasDensity C c)
    (hexcess : Negligible (positiveOrbitPullback θ O \ C)) :
    (volume O).toReal ≤ c := by
  classical
  let a : AddCircle (1 : ℝ) := (θ : AddCircle (1 : ℝ))
  let P : Set ℕ := {n | n • a ∈ O}
  let Q : Set ℕ := P \ C
  have hQ : HasDensity Q 0 := by
    apply HasDensity.of_eventually_eq 0 ?_ hexcess
    intro n hn
    simp only [positiveOrbitPullback, P, Q, a, Set.mem_sdiff, Set.mem_setOf_eq, hn, true_and]
  have hcounts (N : ℕ) : prefixCount P (N + 1) ≤
      prefixCount C (N + 1) + prefixCount Q (N + 1) := by
    have hbound (L : ℕ) : prefixCount P L ≤ prefixCount C L + prefixCount Q L := by
      induction L with
      | zero => simp [prefixCount]
      | succ L ih =>
          dsimp only [Q] at ih
          simp only [prefixCount_succ]
          by_cases hLP : L ∈ P <;> by_cases hLC : L ∈ C <;>
            simp [Q, hLP, hLC] <;> omega
    exact hbound (N + 1)
  have hcomparison (N : ℕ) :
      (NumStability.empiricalProbability a N : Measure (AddCircle (1 : ℝ))) O ≤
        ENNReal.ofReal (((prefixCount C (N + 1) : ℝ) + prefixCount Q (N + 1)) /
          (N + 1 : ℕ)) := by
    rw [empirical_orbit_measure_eq_prefix a O hO.measurableSet N]
    apply ENNReal.ofReal_le_ofReal
    apply div_le_div_of_nonneg_right _ (by positivity)
    exact_mod_cast hcounts N
  have hrealLimit : Tendsto (fun N =>
      ((prefixCount C (N + 1) : ℝ) + prefixCount Q (N + 1)) / (N + 1 : ℕ))
      atTop (𝓝 c) := by
    simpa only [← add_div, add_zero] using
      (density_successor_prefix_tendsto C c hC).add (density_successor_prefix_tendsto Q 0 hQ)
  have hlimit := (ENNReal.continuous_ofReal.tendsto c).comp hrealLimit
  dsimp only [Function.comp_def] at hlimit
  have hmono := limsup_le_limsup (f := atTop) (Eventually.of_forall hcomparison)
  rw [hlimit.limsup_eq] at hmono
  have hport : volume O ≤
      atTop.liminf (fun N =>
        (NumStability.empiricalProbability a N : Measure (AddCircle (1 : ℝ))) O) := by
    have hraw := ProbabilityMeasure.le_liminf_measure_open_of_tendsto
      (NumStability.empiricalProbability_tendsto_haar (irrational_addOrder hθ)) hO
    change AddCircle.haarAddCircle O ≤ atTop.liminf (fun N =>
      (NumStability.empiricalProbability (θ : AddCircle (1 : ℝ)) N :
        Measure (AddCircle (1 : ℝ))) O) at hraw
    rw [NumStability.haar_eq_volume_unit] at hraw
    exact hraw
  have hbetween :
      atTop.liminf (fun N =>
        (NumStability.empiricalProbability a N : Measure (AddCircle (1 : ℝ))) O) ≤
      atTop.limsup (fun N =>
        (NumStability.empiricalProbability a N : Measure (AddCircle (1 : ℝ))) O) :=
    liminf_le_limsup
  have hbound : volume O ≤ ENNReal.ofReal c := hport.trans (hbetween.trans hmono)
  have hreal := ENNReal.toReal_mono ENNReal.ofReal_ne_top hbound
  simpa only [ENNReal.toReal_ofReal hC.nonneg] using hreal

theorem open_orbit_measure_le_of_hasDensity
    (θ : ℝ) (hθ : Irrational θ) (O : Set (AddCircle (1 : ℝ))) (hO : IsOpen O)
    (c : ℝ) (hP : HasDensity (positiveOrbitPullback θ O) c) :
    (volume O).toReal ≤ c := by
  apply open_orbit_measure_le_density_of_negligible_excess θ hθ O hO
    (positiveOrbitPullback θ O) c hP
  simpa only [sdiff_self] using (show Negligible (∅ : Set ℕ) from hasDensity_empty)

end Erdos335.Proposed

end
