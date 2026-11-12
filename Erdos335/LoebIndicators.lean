import Erdos335.LoebPositiveInputs
import Erdos335.LoebGroup

/-!
# Indicators and literal internal sumsets

Standard parts preserve internal indicator functions exactly. A positive
indicator convolution can occur only in the literal sumset.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Filter Set Topology MeasureTheory
open scoped Pointwise

namespace Erdos335.Loeb

theorem indicator_one_abs_le {A : Type*} (S : Set A) (x : A) :
    |S.indicator (fun _ => (1 : ℝ)) x| ≤ 1 := by
  classical
  by_cases hx : x ∈ S <;> simp [hx]

theorem boundedRealFunction_indicator
    {I : Type*} {X : I → Type*} (U : Ultrafilter I) (A : ∀ i, Set (X i)) :
    boundedRealFunction U (fun i => (A i).indicator (fun _ => (1 : ℝ))) 1
      (fun i x => indicator_one_abs_le (A i) x) =
        (internalSet U A).indicator (fun _ => (1 : ℝ)) := by
  classical
  funext x
  induction x using Quotient.inductionOn with
  | h a =>
    by_cases h : (a : (U : Filter I).Product X) ∈ internalSet U A
    · have hlim : Tendsto (fun i => (A i).indicator (fun _ => (1 : ℝ)) (a i))
          (U : Filter I) (𝓝 1) := by
        apply tendsto_const_nhds.congr'
        exact (mem_internalSet_iff U A a).mp h |>.mono (fun i hi => by simp [hi])
      exact (tendsto_nhds_unique (tendsto_boundedRealFunction U _ _ _ a) hlim).trans
        (Set.indicator_of_mem h (fun _ => (1 : ℝ))).symm
    ·
      have hn : ∀ᶠ i in U, a i ∉ A i := by
        rw [Ultrafilter.eventually_not]
        exact h
      have hlim : Tendsto (fun i => (A i).indicator (fun _ => (1 : ℝ)) (a i))
          (U : Filter I) (𝓝 0) := by
        apply tendsto_const_nhds.congr'
        exact hn.mono (fun i hi => by simp [hi])
      exact (tendsto_nhds_unique (tendsto_boundedRealFunction U _ _ _ a) hlim).trans
        (Set.indicator_of_notMem h (fun _ => (1 : ℝ))).symm

theorem integral_boundedRealFunction_indicator
    {X : ℕ → Type*} [∀ n, Finite (X n)] [∀ n, Nonempty (X n)]
    (U : Ultrafilter ℕ) (hU : (U : Filter ℕ) ≤ atTop) (A : ∀ n, Set (X n)) :
    (∫ x, boundedRealFunction U (fun n => (A n).indicator (fun _ => (1 : ℝ))) 1
      (fun n x => indicator_one_abs_le (A n) x) x ∂loebMeasure U hU) = (ultraCount U A).toReal := by
  let : MeasurableSpace ((U : Filter ℕ).Product X) := loebMeasurableSpace U
  rw [boundedRealFunction_indicator, integral_indicator (measurable_internalSet U A)]
  simp [measureReal_def, loebMeasure_internal]

theorem indicator_convolution_eq_zero_of_not_mem_add
    {G : Type*} [AddCommGroup G] [MeasurableSpace G]
    (μ : Measure G) (A B : Set G) (x : G) (hx : x ∉ A + B) :
    (∫ t, A.indicator (fun _ => (1 : ℝ)) t * B.indicator (fun _ => (1 : ℝ)) (x - t) ∂μ) = 0 := by
  classical
  have hzero (t : G) : A.indicator (fun _ => (1 : ℝ)) t *
      B.indicator (fun _ => (1 : ℝ)) (x - t) = 0 := by
    by_cases ht : t ∈ A
    · have hb : x - t ∉ B := by
        intro hb
        apply hx
        exact Set.mem_add.mpr ⟨t, ht, x - t, hb, by abel⟩
      simp [ht, hb]
    · simp [ht]
  calc
    (∫ t, A.indicator (fun _ => (1 : ℝ)) t * B.indicator (fun _ => (1 : ℝ)) (x - t) ∂μ) =
        ∫ _t : G, (0 : ℝ) ∂μ := integral_congr_ae (ae_of_all μ hzero)
    _ = 0 := integral_zero _ _

theorem positive_indicator_convolution_subset_add
    {G : Type*} [AddCommGroup G] [MeasurableSpace G]
    (μ : Measure G) (A B : Set G) :
    {x | 0 < ∫ t, A.indicator (fun _ => (1 : ℝ)) t *
      B.indicator (fun _ => (1 : ℝ)) (x - t) ∂μ} ⊆ A + B := by
  intro x hx
  change 0 < ∫ t, A.indicator (fun _ => (1 : ℝ)) t *
    B.indicator (fun _ => (1 : ℝ)) (x - t) ∂μ at hx
  by_contra h
  rw [indicator_convolution_eq_zero_of_not_mem_add μ A B x h] at hx
  exact (lt_irrefl 0) hx

theorem positive_internal_convolution_subset_add
    {X : ℕ → Type*} [∀ n, AddCommGroup (X n)] [∀ n, Fintype (X n)]
    (U : Ultrafilter ℕ) (hU : (U : Filter ℕ) ≤ atTop) (A B : ∀ n, Set (X n)) :
    {x | 0 < ∫ t,
      boundedRealFunction U (fun n => (A n).indicator (fun _ => (1 : ℝ))) 1
        (fun n x => indicator_one_abs_le (A n) x) t *
      boundedRealFunction U (fun n => (B n).indicator (fun _ => (1 : ℝ))) 1
        (fun n x => indicator_one_abs_le (B n) x) (x - t) ∂loebMeasure U hU} ⊆
      internalSet U (fun n => A n + B n) := by
  let : MeasurableSpace ((U : Filter ℕ).Product X) := loebMeasurableSpace U
  rw [boundedRealFunction_indicator, boundedRealFunction_indicator, internalSet_add]
  exact positive_indicator_convolution_subset_add (loebMeasure U hU) (internalSet U A) (internalSet U B)

end Erdos335.Loeb
