import Erdos335.LoebContinuousIntegral
import Mathlib.MeasureTheory.Function.L2Space

/-!
# Real Hilbert vectors associated with bounded internal functions
-/

set_option autoImplicit false

open Filter Set Topology MeasureTheory
open scoped BigOperators InnerProductSpace

namespace Erdos335.Loeb

variable {X : ℕ → Type*} [∀ n, Fintype (X n)] [∀ n, Nonempty (X n)]

noncomputable def realLoebFunction (U : Ultrafilter ℕ) (f : ∀ n, X n → ℝ)
    (hf : ∀ n x, f n x ∈ Icc (0 : ℝ) 1) : (U : Filter ℕ).Product X → ℝ :=
  fun x => (ultralimitFunction U (fun n y => (⟨f n y, hf n y⟩ : Icc (0 : ℝ) 1)) x).val

omit [∀ n, Fintype (X n)] [∀ n, Nonempty (X n)] in
theorem realLoebFunction_mem (U : Ultrafilter ℕ) (f : ∀ n, X n → ℝ)
    (hf : ∀ n x, f n x ∈ Icc (0 : ℝ) 1) (x : (U : Filter ℕ).Product X) :
    realLoebFunction U f hf x ∈ Icc (0 : ℝ) 1 :=
  (ultralimitFunction U (fun n y => (⟨f n y, hf n y⟩ : Icc (0 : ℝ) 1)) x).property

theorem measurable_realLoebFunction (U : Ultrafilter ℕ) (f : ∀ n, X n → ℝ)
    (hf : ∀ n x, f n x ∈ Icc (0 : ℝ) 1) :
    @Measurable ((U : Filter ℕ).Product X) ℝ (loebMeasurableSpace U) _
      (realLoebFunction U f hf) :=
  continuous_subtype_val.measurable.comp (measurable_ultralimitFunction U _)

theorem realLoebFunction_memLp (U : Ultrafilter ℕ) (hU : (U : Filter ℕ) ≤ atTop)
    (f : ∀ n, X n → ℝ) (hf : ∀ n x, f n x ∈ Icc (0 : ℝ) 1) :
    MemLp (realLoebFunction U f hf) 2 (loebMeasure U hU) := by
  let : MeasurableSpace ((U : Filter ℕ).Product X) := loebMeasurableSpace U
  let : IsProbabilityMeasure (loebMeasure (X := X) U hU) := isProbabilityMeasure_loebMeasure U hU
  apply MemLp.of_bound (measurable_realLoebFunction U f hf).aestronglyMeasurable 1
  apply ae_of_all
  intro x
  have hx := realLoebFunction_mem U f hf x
  simpa only [Real.norm_eq_abs, abs_of_nonneg hx.1] using hx.2

noncomputable def realLoebVector (U : Ultrafilter ℕ) (hU : (U : Filter ℕ) ≤ atTop)
    (f : ∀ n, X n → ℝ) (hf : ∀ n x, f n x ∈ Icc (0 : ℝ) 1) :
    Lp ℝ 2 (loebMeasure (X := X) U hU) := (realLoebFunction_memLp U hU f hf).toLp (realLoebFunction U f hf)

theorem realLoebVector_norm_sq (U : Ultrafilter ℕ) (hU : (U : Filter ℕ) ≤ atTop)
    (f : ∀ n, X n → ℝ) (hf : ∀ n x, f n x ∈ Icc (0 : ℝ) 1) :
    ‖realLoebVector U hU f hf‖ ^ 2 = ∫ x, realLoebFunction U f hf x ^ 2 ∂loebMeasure U hU := by
  rw [← real_inner_self_eq_norm_sq, L2.inner_def]
  apply integral_congr_ae
  filter_upwards [(realLoebFunction_memLp U hU f hf).coeFn_toLp] with x hx
  change ⟪(realLoebFunction_memLp U hU f hf).toLp (realLoebFunction U f hf) x,
    (realLoebFunction_memLp U hU f hf).toLp (realLoebFunction U f hf) x⟫_ℝ = _
  rw [hx, real_inner_self_eq_norm_sq, Real.norm_eq_abs, sq_abs]

theorem tendsto_realLoebVector_energy (U : Ultrafilter ℕ) (hU : (U : Filter ℕ) ≤ atTop)
    (f : ∀ n, X n → ℝ) (hf : ∀ n x, f n x ∈ Icc (0 : ℝ) 1) :
    Tendsto (fun n => (∑ x : X n, f n x ^ 2) / (Nat.card (X n) : ℝ))
      (U : Filter ℕ) (𝓝 (‖realLoebVector U hU f hf‖ ^ 2)) := by
  have h := tendsto_continuous_coordinate_averages U hU
    (fun n y => (⟨f n y, hf n y⟩ : Icc (0 : ℝ) 1))
    (fun z : Icc (0 : ℝ) 1 => z.val ^ 2) (by fun_prop)
  rw [realLoebVector_norm_sq]
  exact h

end Erdos335.Loeb
