import Erdos335.LoebBoundedOperations

/-!
# Mean-square transfer for bounded internal functions

The normalized finite square norms and square distances converge to their
Loeb integrals. Thus finite Fourier approximation bounds pass to the Loeb
model with the same constants.
-/

set_option autoImplicit false

open Filter Set Topology MeasureTheory
open scoped BigOperators

namespace Erdos335.Loeb

theorem boundedComplexFunction_sub
    {I : Type*} {X : I → Type*} (U : Ultrafilter I) (f g : ∀ i, X i → ℂ)
    (M N P : ℝ) (hf : ∀ i x, ‖f i x‖ ≤ M) (hg : ∀ i x, ‖g i x‖ ≤ N)
    (hs : ∀ i x, ‖f i x - g i x‖ ≤ P) :
    boundedComplexFunction U (fun i x => f i x - g i x) P hs =
      fun x => boundedComplexFunction U f M hf x - boundedComplexFunction U g N hg x := by
  funext x
  induction x using Quotient.inductionOn with
  | h a =>
    exact tendsto_nhds_unique (tendsto_boundedComplexFunction U _ P hs a)
      ((tendsto_boundedComplexFunction U f M hf a).sub
        (tendsto_boundedComplexFunction U g N hg a))

theorem tendsto_boundedComplex_sqNorm_averages
    {X : ℕ → Type*} [∀ n, Fintype (X n)] [∀ n, Nonempty (X n)]
    (U : Ultrafilter ℕ) (hU : (U : Filter ℕ) ≤ atTop)
    (f : ∀ n, X n → ℂ) (M : ℝ) (hf : ∀ n x, ‖f n x‖ ≤ M) :
    Tendsto (fun n => (Nat.card (X n) : ℝ)⁻¹ * ∑ x : X n, ‖f n x‖ ^ 2)
      (U : Filter ℕ)
      (𝓝 (∫ x, ‖boundedComplexFunction U f M hf x‖ ^ 2 ∂loebMeasure U hU)) := by
  let F : ∀ n, X n → Metric.closedBall (0 : ℂ) M :=
    fun n x => ⟨f n x, by simpa only [Metric.mem_closedBall, dist_zero_right] using hf n x⟩
  have hcont : Continuous (fun z : Metric.closedBall (0 : ℂ) M => ‖z.val‖ ^ 2) :=
    continuous_subtype_val.norm.pow 2
  have hlim := tendsto_continuous_coordinate_averages U hU F _ hcont
  simpa only [F, boundedComplexFunction, div_eq_mul_inv, mul_comm] using hlim

theorem tendsto_boundedComplex_sqDistance_averages
    {X : ℕ → Type*} [∀ n, Fintype (X n)] [∀ n, Nonempty (X n)]
    (U : Ultrafilter ℕ) (hU : (U : Filter ℕ) ≤ atTop)
    (f g : ∀ n, X n → ℂ) (M N : ℝ)
    (hf : ∀ n x, ‖f n x‖ ≤ M) (hg : ∀ n x, ‖g n x‖ ≤ N) :
    Tendsto (fun n => (Nat.card (X n) : ℝ)⁻¹ * ∑ x : X n, ‖f n x - g n x‖ ^ 2)
      (U : Filter ℕ)
      (𝓝 (∫ x, ‖boundedComplexFunction U f M hf x -
        boundedComplexFunction U g N hg x‖ ^ 2 ∂loebMeasure U hU)) := by
  have hdiff : ∀ n x, ‖f n x - g n x‖ ≤ M + N := by
    intro n x
    exact (norm_sub_le _ _).trans (add_le_add (hf n x) (hg n x))
  have hlim := tendsto_boundedComplex_sqNorm_averages U hU
    (fun n x => f n x - g n x) (M + N) hdiff
  rw [boundedComplexFunction_sub U f g M N (M + N) hf hg hdiff] at hlim
  exact hlim

theorem loeb_sqDistance_le_of_eventually
    {X : ℕ → Type*} [∀ n, Fintype (X n)] [∀ n, Nonempty (X n)]
    (U : Ultrafilter ℕ) (hU : (U : Filter ℕ) ≤ atTop)
    (f g : ∀ n, X n → ℂ) (M N : ℝ)
    (hf : ∀ n x, ‖f n x‖ ≤ M) (hg : ∀ n x, ‖g n x‖ ≤ N) (r : ℝ)
    (hr : ∀ᶠ n in U, (Nat.card (X n) : ℝ)⁻¹ * ∑ x : X n, ‖f n x - g n x‖ ^ 2 ≤ r) :
    (∫ x, ‖boundedComplexFunction U f M hf x -
      boundedComplexFunction U g N hg x‖ ^ 2 ∂loebMeasure U hU) ≤ r :=
  le_of_tendsto (tendsto_boundedComplex_sqDistance_averages U hU f g M N hf hg) hr

end Erdos335.Loeb
