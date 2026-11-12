import Erdos335.LoebBoundedComplex

/-!
# Pointwise operations on bounded internal functions

Standard parts commute with addition, multiplication, and internal changes
of variables, by uniqueness of limits along the ultrafilter.
-/

set_option autoImplicit false

open Filter Set Topology

namespace Erdos335.Loeb

variable {I : Type*} {X Y : I → Type*}

theorem tendsto_boundedComplexFunction (U : Ultrafilter I) (f : ∀ i, X i → ℂ)
    (M : ℝ) (h : ∀ i x, ‖f i x‖ ≤ M) (x : ∀ i, X i) :
    Tendsto (fun i => f i (x i)) (U : Filter I)
      (𝓝 (boundedComplexFunction U f M h (x : (U : Filter I).Product X))) := by
  let F : ∀ i, X i → Metric.closedBall (0 : ℂ) M :=
    fun i y => ⟨f i y, by simpa only [Metric.mem_closedBall, dist_zero_right] using h i y⟩
  change Tendsto (fun i => (F i (x i)).val) (U : Filter I)
    (𝓝 (ultralimitFunction U F (x : (U : Filter I).Product X)).val)
  exact (continuous_subtype_val.tendsto _).comp (tendsto_ultralimitFunction U F x)

theorem boundedComplexFunction_independent_bound (U : Ultrafilter I) (f : ∀ i, X i → ℂ)
    (M N : ℝ) (hM : ∀ i x, ‖f i x‖ ≤ M) (hN : ∀ i x, ‖f i x‖ ≤ N) :
    boundedComplexFunction U f M hM = boundedComplexFunction U f N hN := by
  funext x
  induction x using Quotient.inductionOn with
  | h a =>
    exact tendsto_nhds_unique (tendsto_boundedComplexFunction U f M hM a)
      (tendsto_boundedComplexFunction U f N hN a)

theorem boundedComplexFunction_add (U : Ultrafilter I) (f g : ∀ i, X i → ℂ)
    (M N P : ℝ) (hf : ∀ i x, ‖f i x‖ ≤ M) (hg : ∀ i x, ‖g i x‖ ≤ N)
    (hs : ∀ i x, ‖f i x + g i x‖ ≤ P) :
    boundedComplexFunction U (fun i x => f i x + g i x) P hs =
      fun x => boundedComplexFunction U f M hf x + boundedComplexFunction U g N hg x := by
  funext x
  induction x using Quotient.inductionOn with
  | h a =>
    exact tendsto_nhds_unique (tendsto_boundedComplexFunction U _ P hs a)
      ((tendsto_boundedComplexFunction U f M hf a).add
        (tendsto_boundedComplexFunction U g N hg a))

theorem boundedComplexFunction_mul (U : Ultrafilter I) (f g : ∀ i, X i → ℂ)
    (M N P : ℝ) (hf : ∀ i x, ‖f i x‖ ≤ M) (hg : ∀ i x, ‖g i x‖ ≤ N)
    (hp : ∀ i x, ‖f i x * g i x‖ ≤ P) :
    boundedComplexFunction U (fun i x => f i x * g i x) P hp =
      fun x => boundedComplexFunction U f M hf x * boundedComplexFunction U g N hg x := by
  funext x
  induction x using Quotient.inductionOn with
  | h a =>
    exact tendsto_nhds_unique (tendsto_boundedComplexFunction U _ P hp a)
      ((tendsto_boundedComplexFunction U f M hf a).mul
        (tendsto_boundedComplexFunction U g N hg a))

theorem boundedComplexFunction_precompose (U : Ultrafilter I) (f : ∀ i, X i → ℂ)
    (p : ∀ i, Y i → X i) (M : ℝ) (h : ∀ i x, ‖f i x‖ ≤ M) :
    boundedComplexFunction U (fun i y => f i (p i y)) M (fun i y => h i (p i y)) =
      boundedComplexFunction U f M h ∘ productMap (U : Filter I) p := by
  funext y
  induction y using Quotient.inductionOn with
  | h a =>
    exact tendsto_nhds_unique
      (tendsto_boundedComplexFunction U _ M (fun i y => h i (p i y)) a)
      (tendsto_boundedComplexFunction U f M h (fun i => p i (a i)))

end Erdos335.Loeb
