import Erdos335.LoebContinuousIntegral

/-!
# Uniformly bounded real internal functions

Embedding the values in a fixed compact interval defines their standard
part. Its Loeb integral is the ultralimit of the coordinate averages.
-/

set_option autoImplicit false

open Filter Set Topology MeasureTheory
open scoped BigOperators

namespace Erdos335.Loeb

variable {I : Type*} {X : I → Type*}

noncomputable def boundedRealFunction (U : Ultrafilter I) (f : ∀ i, X i → ℝ)
    (M : ℝ) (h : ∀ i x, |f i x| ≤ M) : (U : Filter I).Product X → ℝ :=
  fun x => (ultralimitFunction U
    (fun i y => (⟨f i y, abs_le.mp (h i y)⟩ : Set.Icc (-M) M)) x).val

theorem boundedRealFunction_bound (U : Ultrafilter I) (f : ∀ i, X i → ℝ)
    (M : ℝ) (h : ∀ i x, |f i x| ≤ M) (x : (U : Filter I).Product X) :
    |boundedRealFunction U f M h x| ≤ M := by
  apply abs_le.mpr
  exact (ultralimitFunction U (fun i y => (⟨f i y, abs_le.mp (h i y)⟩ : Set.Icc (-M) M)) x).property

theorem tendsto_boundedRealFunction (U : Ultrafilter I) (f : ∀ i, X i → ℝ)
    (M : ℝ) (h : ∀ i x, |f i x| ≤ M) (x : ∀ i, X i) :
    Tendsto (fun i => f i (x i)) (U : Filter I)
      (𝓝 (boundedRealFunction U f M h (x : (U : Filter I).Product X))) := by
  let F : ∀ i, X i → Set.Icc (-M) M := fun i y => ⟨f i y, abs_le.mp (h i y)⟩
  change Tendsto (fun i => (F i (x i)).val) (U : Filter I)
    (𝓝 (ultralimitFunction U F (x : (U : Filter I).Product X)).val)
  exact (continuous_subtype_val.tendsto _).comp (tendsto_ultralimitFunction U F x)

theorem boundedRealFunction_independent_bound (U : Ultrafilter I) (f : ∀ i, X i → ℝ)
    (M N : ℝ) (hM : ∀ i x, |f i x| ≤ M) (hN : ∀ i x, |f i x| ≤ N) :
    boundedRealFunction U f M hM = boundedRealFunction U f N hN := by
  funext x
  induction x using Quotient.inductionOn with
  | h a =>
    exact tendsto_nhds_unique (tendsto_boundedRealFunction U f M hM a)
      (tendsto_boundedRealFunction U f N hN a)

theorem measurable_boundedRealFunction
    {Y : ℕ → Type*} [∀ n, Finite (Y n)] [∀ n, Nonempty (Y n)]
    (U : Ultrafilter ℕ) (f : ∀ n, Y n → ℝ) (M : ℝ) (h : ∀ n x, |f n x| ≤ M) :
    @Measurable ((U : Filter ℕ).Product Y) ℝ (loebMeasurableSpace U) _
      (boundedRealFunction U f M h) :=
  continuous_subtype_val.measurable.comp (measurable_ultralimitFunction U _)

theorem tendsto_boundedRealFunction_averages
    {Y : ℕ → Type*} [∀ n, Fintype (Y n)] [∀ n, Nonempty (Y n)]
    (U : Ultrafilter ℕ) (hU : (U : Filter ℕ) ≤ atTop)
    (f : ∀ n, Y n → ℝ) (M : ℝ) (h : ∀ n x, |f n x| ≤ M) :
    Tendsto (fun n => (∑ x : Y n, f n x) / (Nat.card (Y n) : ℝ))
      (U : Filter ℕ) (𝓝 (∫ x, boundedRealFunction U f M h x ∂loebMeasure U hU)) :=
  tendsto_continuous_coordinate_averages U hU
    (fun n x => (⟨f n x, abs_le.mp (h n x)⟩ : Set.Icc (-M) M))
    Subtype.val continuous_subtype_val

end Erdos335.Loeb
