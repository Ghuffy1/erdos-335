import Erdos335.LoebBoundedOperations

/-!
# Convolution transfer for finite-group ultraproducts

At every represented point, the normalized finite convolutions converge
to the convolution of the two bounded standard-part functions.
-/

set_option autoImplicit false

open Filter Set Topology MeasureTheory
open scoped BigOperators

namespace Erdos335.Loeb

theorem productMap_sub_left {I : Type*} {X : I → Type*} [∀ i, AddCommGroup (X i)]
    (U : Ultrafilter I) (x : ∀ i, X i) :
    productMap (U : Filter I) (fun i t => x i - t) =
      fun t => productProjection (U : Filter I) x - t := by
  funext t
  induction t using Quotient.inductionOn with
  | h a => rfl

theorem tendsto_coordinate_convolution
    {X : ℕ → Type*} [∀ n, AddCommGroup (X n)] [∀ n, Fintype (X n)]
    (U : Ultrafilter ℕ) (hU : (U : Filter ℕ) ≤ atTop)
    (f g : ∀ n, X n → ℂ) (M N : ℝ)
    (hf : ∀ n t, ‖f n t‖ ≤ M) (hg : ∀ n t, ‖g n t‖ ≤ N) (x : ∀ n, X n) :
    Tendsto (fun n => (Nat.card (X n) : ℝ)⁻¹ • ∑ t : X n, f n t * g n (x n - t))
      (U : Filter ℕ)
      (𝓝 (∫ t, boundedComplexFunction U f M hf t *
        boundedComplexFunction U g N hg (productProjection (U : Filter ℕ) x - t)
        ∂loebMeasure U hU)) := by
  let gX : ∀ n, X n → ℂ := fun n t => g n (x n - t)
  have hgX : ∀ n t, ‖gX n t‖ ≤ N := fun n t => hg n (x n - t)
  let H : ∀ n, X n → ℂ := fun n t => f n t * gX n t
  have hH : ∀ n t, ‖H n t‖ ≤ M * N := by
    intro n t
    dsimp only [H]
    rw [norm_mul]
    exact mul_le_mul (hf n t) (hgX n t) (norm_nonneg _) ((norm_nonneg _).trans (hf n t))
  have hmul := boundedComplexFunction_mul U f gX M N (M * N) hf hgX hH
  have hcomp := boundedComplexFunction_precompose U g (fun n t => x n - t) N hg
  have hEq : boundedComplexFunction U H (M * N) hH =
      fun t => boundedComplexFunction U f M hf t *
        boundedComplexFunction U g N hg (productProjection (U : Filter ℕ) x - t) := by
    funext t
    calc
      boundedComplexFunction U H (M * N) hH t =
          boundedComplexFunction U f M hf t * boundedComplexFunction U gX N hgX t :=
        congrFun hmul t
      _ = boundedComplexFunction U f M hf t *
          boundedComplexFunction U g N hg (productMap (U : Filter ℕ) (fun n t => x n - t) t) := by
        rw [congrFun hcomp t]
        rfl
      _ = _ := by rw [productMap_sub_left]
  have hlim := tendsto_boundedComplexFunction_averages U hU H (M * N) hH
  rw [hEq] at hlim
  exact hlim

end Erdos335.Loeb
