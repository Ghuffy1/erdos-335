import Erdos335.LoebNaturalKernels
import Erdos335.FinitePeriodTests

/-!
# Uniformly bounded natural periods under a fixed deficit

Kneser's inequality bounds the reciprocal index of the stabilizer below
by the measure deficit. All internal pairs with that deficit therefore
use one fixed finite family of natural kernels.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Filter Set Topology MeasureTheory
open scoped ENNReal Pointwise

noncomputable section

namespace Erdos335.Loeb

theorem exists_uniform_natural_period_bound
    (U : Ultrafilter ℕ) (hU : (U : Filter ℕ) ≤ atTop) (q : ℕ → ℕ+)
    (δ : ℝ) (hδ : 0 < δ) :
    ∃ D : ℕ, ∀ A B : ∀ n, Set (ZMod (q n : ℕ)),
      (internalSet U A).Nonempty → (internalSet U B).Nonempty →
      δ ≤ (loebMeasure U hU (internalSet U A)).toReal +
        (loebMeasure U hU (internalSet U B)).toReal -
        (loebMeasure U hU (internalSet U (fun n => A n + B n))).toReal →
      ∃ h : ℕ+, (h : ℕ) ≤ D ∧
        ∀ c ∈ internalSet U (fun n => A n + B n),
          ∀ k ∈ naturalCyclicKernel U q h, c + k ∈ internalSet U (fun n => A n + B n) := by
  let G := (U : Filter ℕ).Product (fun n => ZMod (q n : ℕ))
  letI : MeasurableSpace G := loebMeasurableSpace U
  let μ := loebMeasure (X := fun n => ZMod (q n : ℕ)) U hU
  letI : IsProbabilityMeasure μ := isProbabilityMeasure_loebMeasure U hU
  obtain ⟨D, hD⟩ := exists_reciprocal_modulus_bound δ hδ
  refine ⟨D, ?_⟩
  intro A B hA hB hgap
  let C := internalSet U (fun n => A n + B n)
  let H := AddAction.stabilizer ((U : Filter ℕ).Product (fun n => ZMod (q n : ℕ))) C
  have hsmall : μ C < μ (internalSet U A) + μ (internalSet U B) := by
    apply (ENNReal.toReal_lt_toReal (measure_ne_top μ _) (by finiteness)).mp
    rw [ENNReal.toReal_add (measure_ne_top μ _) (measure_ne_top μ _)]
    change δ ≤ (μ (internalSet U A)).toReal + (μ (internalSet U B)).toReal - (μ C).toReal at hgap
    linarith
  have hHpos : 0 < μ (H : Set _) :=
    subcritical_stabilizer_positive U hU A B hA hB hsmall
  have hHmeas : MeasurableSet (H : Set G) := by
    change MeasurableSet
      ((AddAction.stabilizer G (internalSet U (fun n => A n + B n))) : Set G)
    rw [← internalAddSubgroup_stabilizer]
    exact measurable_internalSet U _
  obtain ⟨h, hH, hmass⟩ := positive_measurable_subgroup_eq_natural_kernel U hU q H hHmeas hHpos
  have hKneser : μ (internalSet U A) + μ (internalSet U B) ≤ μ C + μ (H : Set _) := by
    have hk := loebMeasure_internal_add_le U hU A B hA hB
    simpa only [internalAddSubgroup_stabilizer] using hk
  have hreal := ENNReal.toReal_mono (by finiteness : μ C + μ (H : Set _) ≠ ∞) hKneser
  rw [ENNReal.toReal_add (measure_ne_top μ _) (measure_ne_top μ _),
    ENNReal.toReal_add (measure_ne_top μ _) (measure_ne_top μ _)] at hreal
  have hmassR : (μ (H : Set _)).toReal = (((h : ℕ) : ℝ))⁻¹ := by
    rw [hmass]
    simp
  rw [hmassR] at hreal
  have hindex : (h : ℕ) ≤ D := hD h (by linarith)
  refine ⟨h, hindex, ?_⟩
  intro c hc k hk
  rw [← hH] at hk
  have hperiod : k +ᵥ C = C := hk
  have hc' : k + c ∈ k +ᵥ C := ⟨c, hc, rfl⟩
  rw [hperiod] at hc'
  simpa only [add_comm] using hc'

end Erdos335.Loeb

end
