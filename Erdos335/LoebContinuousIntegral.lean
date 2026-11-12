import Erdos335.LoebAverages
import Mathlib.MeasureTheory.Integral.IntegrableOn

/-!
# Integral transfer for compact-valued internal functions

Finite approximations compare coordinate averages and the Loeb integral of
a continuous test function of the pointwise ultralimit.
-/

set_option autoImplicit false

open Filter Set Topology MeasureTheory
open scoped ENNReal BigOperators

namespace Erdos335.Loeb

theorem dist_finite_averages_le {Y : Type*} [Fintype Y] [Nonempty Y]
    (f g : Y → ℝ) (r : ℝ) (h : ∀ y, dist (f y) (g y) ≤ r) :
    dist ((∑ y, f y) / (Nat.card Y : ℝ)) ((∑ y, g y) / (Nat.card Y : ℝ)) ≤ r := by
  have hc : (0 : ℝ) < Fintype.card Y := by exact_mod_cast Fintype.card_pos
  have hsum : ‖∑ y, (f y - g y)‖ ≤ (Fintype.card Y : ℝ) * r := by
    calc
      ‖∑ y, (f y - g y)‖ ≤ ∑ y, ‖f y - g y‖ := norm_sum_le _ _
      _ ≤ ∑ _ : Y, r := Finset.sum_le_sum fun y _ => h y
      _ = _ := by simp
  rw [dist_eq_norm, ← sub_div, ← Finset.sum_sub_distrib, norm_div, Nat.card_eq_fintype_card]
  simpa only [Real.norm_natCast] using
    (div_le_iff₀ hc).mpr (by simpa only [mul_comm] using hsum)

theorem dist_integrals_le_of_pointwise
    {Y : Type*} [MeasurableSpace Y] (μ : Measure Y) [IsProbabilityMeasure μ]
    (f g : Y → ℝ) (hf : Integrable f μ) (hg : Integrable g μ)
    (r : ℝ) (h : ∀ y, dist (f y) (g y) ≤ r) :
    dist (∫ y, f y ∂μ) (∫ y, g y ∂μ) ≤ r := by
  rw [dist_eq_norm, ← integral_sub hf hg]
  have hn : ∀ y, ‖f y - g y‖ ≤ r := by simpa only [dist_eq_norm] using h
  simpa using norm_integral_le_of_norm_le_const (μ := μ) (ae_of_all μ hn)

theorem integrable_continuous_ultralimit
    {X : ℕ → Type*} [∀ n, Finite (X n)] [∀ n, Nonempty (X n)]
    {E : Type*} [MetricSpace E] [CompactSpace E] [MeasurableSpace E] [BorelSpace E]
    (U : Ultrafilter ℕ) (hU : (U : Filter ℕ) ≤ atTop) (f : ∀ n, X n → E)
    (g : E → ℝ) (hg : Continuous g) :
    Integrable (fun x => g (ultralimitFunction U f x)) (loebMeasure U hU) := by
  let : MeasurableSpace ((U : Filter ℕ).Product X) := loebMeasurableSpace U
  let : IsProbabilityMeasure (loebMeasure (X := X) U hU) := isProbabilityMeasure_loebMeasure U hU
  obtain ⟨R, hR⟩ := (isCompact_range hg.norm).bddAbove
  apply Integrable.of_bound (hg.measurable.comp (measurable_ultralimitFunction U f)).aestronglyMeasurable R
  exact ae_of_all _ fun x => hR (mem_range_self (ultralimitFunction U f x))

theorem integrable_finiteFunction
    {X : ℕ → Type*} [∀ n, Finite (X n)] [∀ n, Nonempty (X n)]
    {G : Type*} [Finite G] [MeasurableSpace G] [MeasurableSingletonClass G]
    (U : Ultrafilter ℕ) (hU : (U : Filter ℕ) ≤ atTop) (f : ∀ n, X n → G)
    (v : G → ℝ) : Integrable (fun x => v (finiteFunction U f x)) (loebMeasure U hU) := by
  let : MeasurableSpace ((U : Filter ℕ).Product X) := loebMeasurableSpace U
  let μ := loebMeasure (X := X) U hU
  let : IsProbabilityMeasure μ := isProbabilityMeasure_loebMeasure U hU
  have hF := measurable_finiteFunction U f
  have hv : Integrable v (Measure.map (finiteFunction U f) μ) := Integrable.of_finite
  exact (integrable_map_measure hv.aestronglyMeasurable hF.aemeasurable).mp hv

theorem tendsto_continuous_coordinate_averages
    {X : ℕ → Type*} [∀ n, Fintype (X n)] [∀ n, Nonempty (X n)]
    {E : Type*} [MetricSpace E] [CompactSpace E] [MeasurableSpace E] [BorelSpace E]
    (U : Ultrafilter ℕ) (hU : (U : Filter ℕ) ≤ atTop) (f : ∀ n, X n → E)
    (g : E → ℝ) (hg : Continuous g) :
    Tendsto (fun n => (∑ x : X n, g (f n x)) / (Nat.card (X n) : ℝ))
      (U : Filter ℕ) (𝓝 (∫ x, g (ultralimitFunction U f x) ∂loebMeasure U hU)) := by
  classical
  let : MeasurableSpace ((U : Filter ℕ).Product X) := loebMeasurableSpace U
  let μ := loebMeasure (X := X) U hU
  let : IsProbabilityMeasure μ := isProbabilityMeasure_loebMeasure U hU
  apply Metric.tendsto_nhds.mpr
  intro ε hε
  let δ := ε / 4
  have hδ : 0 < δ := by dsimp [δ]; positivity
  obtain ⟨S, q, hq⟩ := exists_finite_continuous_approximation g hg δ hδ
  let : MeasurableSpace S := ⊤
  let : MeasurableSingletonClass S := ⟨fun _ => MeasurableSet.of_discrete⟩
  let Q : ∀ n, X n → S := fun n x => q (f n x)
  let v : S → ℝ := fun s => s.val
  let B := ∫ x, v (finiteFunction U Q x) ∂μ
  have hB : Tendsto (fun n => (∑ x : X n, v (Q n x)) / (Nat.card (X n) : ℝ))
      (U : Filter ℕ) (𝓝 B) := by
    simpa only [finite_weighted_average] using tendsto_finite_weighted_averages U hU Q v
  have hfinite : ∀ n, dist ((∑ x : X n, g (f n x)) / (Nat.card (X n) : ℝ))
      ((∑ x : X n, v (Q n x)) / (Nat.card (X n) : ℝ)) ≤ δ := by
    intro n
    exact dist_finite_averages_le _ _ δ (fun x => (hq (f n x)).le)
  have hpoint : ∀ x, dist (g (ultralimitFunction U f x)) (v (finiteFunction U Q x)) ≤ δ :=
    fun x => continuous_finite_approximation_bound U f Q g hg v δ
      (fun n y => (hq (f n y)).le) x
  have hIntegral : dist (∫ x, g (ultralimitFunction U f x) ∂μ) B ≤ δ :=
    dist_integrals_le_of_pointwise μ _ _ (integrable_continuous_ultralimit U hU f g hg)
      (integrable_finiteFunction U hU Q v) δ hpoint
  have hnear := hB.eventually (Metric.ball_mem_nhds B hδ)
  filter_upwards [hnear] with n hn
  change dist ((∑ x : X n, g (f n x)) / (Nat.card (X n) : ℝ))
    (∫ x, g (ultralimitFunction U f x) ∂μ) < ε
  have hn' : dist ((∑ x : X n, v (Q n x)) / (Nat.card (X n) : ℝ)) B < δ := hn
  have htotal := dist_triangle4
    ((∑ x : X n, g (f n x)) / (Nat.card (X n) : ℝ))
    ((∑ x : X n, v (Q n x)) / (Nat.card (X n) : ℝ)) B
    (∫ x, g (ultralimitFunction U f x) ∂μ)
  rw [dist_comm B] at htotal
  have hf := hfinite n
  dsimp [δ] at hf hn' hIntegral
  linarith

end Erdos335.Loeb
