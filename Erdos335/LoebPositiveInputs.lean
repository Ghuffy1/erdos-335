import Erdos335.LoebBoundedReal
import Erdos335.LoebBoundedOperations
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap

/-!
# Positive bounded internal inputs

Closed interval constraints survive standard parts. Real inputs and their
complex embeddings have the same standard parts and convolution integrals.
-/

set_option autoImplicit false

open Filter Set Topology MeasureTheory

namespace Erdos335.Loeb

theorem boundedRealFunction_mem_Icc
    {I : Type*} {X : I → Type*} (U : Ultrafilter I)
    (f : ∀ i, X i → ℝ) (M a b : ℝ) (hf : ∀ i x, |f i x| ≤ M)
    (hrange : ∀ i x, f i x ∈ Icc a b) (x : (U : Filter I).Product X) :
    boundedRealFunction U f M hf x ∈ Icc a b := by
  induction x using Quotient.inductionOn with
  | h x =>
    exact isClosed_Icc.mem_of_tendsto (tendsto_boundedRealFunction U f M hf x)
      (Eventually.of_forall (fun i => hrange i (x i)))

theorem boundedComplexFunction_ofReal
    {I : Type*} {X : I → Type*} (U : Ultrafilter I)
    (f : ∀ i, X i → ℝ) (M : ℝ) (hf : ∀ i x, |f i x| ≤ M)
    (hc : ∀ i x, ‖(f i x : ℂ)‖ ≤ M) (x : (U : Filter I).Product X) :
    boundedComplexFunction U (fun i x => (f i x : ℂ)) M hc x =
      (boundedRealFunction U f M hf x : ℂ) := by
  induction x using Quotient.inductionOn with
  | h x =>
    exact tendsto_nhds_unique
      (tendsto_boundedComplexFunction U _ M hc x)
      ((Complex.continuous_ofReal.tendsto _).comp (tendsto_boundedRealFunction U f M hf x))

theorem integrable_boundedRealFunction
    {X : ℕ → Type*} [∀ n, Finite (X n)] [∀ n, Nonempty (X n)]
    (U : Ultrafilter ℕ) (hU : (U : Filter ℕ) ≤ atTop)
    (f : ∀ n, X n → ℝ) (M : ℝ) (hf : ∀ n x, |f n x| ≤ M) :
    Integrable (boundedRealFunction U f M hf) (loebMeasure U hU) := by
  let : MeasurableSpace ((U : Filter ℕ).Product X) := loebMeasurableSpace U
  let : IsProbabilityMeasure (loebMeasure (X := X) U hU) := isProbabilityMeasure_loebMeasure U hU
  exact Integrable.of_bound (measurable_boundedRealFunction U f M hf).aestronglyMeasurable
    M (ae_of_all _ (fun x => by simpa only [Real.norm_eq_abs] using
      (boundedRealFunction_bound U f M hf x)))

theorem boundedReal_complex_convolution
    {X : ℕ → Type*} [∀ n, AddCommGroup (X n)] [∀ n, Fintype (X n)]
    (U : Ultrafilter ℕ) (hU : (U : Filter ℕ) ≤ atTop)
    (f g : ∀ n, X n → ℝ) (M N : ℝ)
    (hf : ∀ n x, |f n x| ≤ M) (hg : ∀ n x, |g n x| ≤ N)
    (hfc : ∀ n x, ‖(f n x : ℂ)‖ ≤ M) (hgc : ∀ n x, ‖(g n x : ℂ)‖ ≤ N)
    (x : (U : Filter ℕ).Product X) :
    (∫ t, boundedComplexFunction U (fun n x => (f n x : ℂ)) M hfc t *
      boundedComplexFunction U (fun n x => (g n x : ℂ)) N hgc (x - t) ∂loebMeasure U hU) =
      ((∫ t, boundedRealFunction U f M hf t *
        boundedRealFunction U g N hg (x - t) ∂loebMeasure U hU : ℝ) : ℂ) := by
  let : MeasurableSpace ((U : Filter ℕ).Product X) := loebMeasurableSpace U
  simpa only [boundedComplexFunction_ofReal U f M hf hfc,
    boundedComplexFunction_ofReal U g N hg hgc, ← Complex.ofReal_mul] using
    (integral_complex_ofReal (μ := loebMeasure U hU)
      (f := fun t => boundedRealFunction U f M hf t * boundedRealFunction U g N hg (x - t)))

end Erdos335.Loeb
