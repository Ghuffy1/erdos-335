import Erdos335.LoebL2
import Erdos335.LoebCompactHom
import Mathlib.Analysis.Complex.Circle

/-!
# Limits of bounded finite character polynomials

Coefficient limits and internal character limits give the pointwise standard
part of a polynomial with a fixed finite number of terms.
-/

set_option autoImplicit false

open Filter Set Topology
open scoped BigOperators

namespace Erdos335.Loeb

theorem exists_limit_bounded_complex {I : Type*} (U : Ultrafilter I)
    (w : I → ℂ) (C : ℝ) (hw : ∀ i, ‖w i‖ ≤ C) :
    ∃ c : ℂ, ‖c‖ ≤ C ∧ Tendsto w (U : Filter I) (𝓝 c) := by
  let W : I → Metric.closedBall (0 : ℂ) C :=
    fun i => ⟨w i, by simpa only [Metric.mem_closedBall, dist_zero_right] using hw i⟩
  let z := (U.map W).lim
  refine ⟨z.val, ?_, ?_⟩
  · simpa only [Metric.mem_closedBall, dist_zero_right] using z.property
  · exact (continuous_subtype_val.tendsto z).comp (U.map W).le_nhds_lim

theorem tendsto_character_polynomial
    {J : Type*} [Fintype J] {X : ℕ → Type*} [∀ n, AddCommGroup (X n)]
    (U : Ultrafilter ℕ) (w : ℕ → J → ℂ) (c : J → ℂ)
    (χ : ∀ n, J → AddChar (X n) Circle)
    (hw : ∀ j, Tendsto (fun n => w n j) (U : Filter ℕ) (𝓝 (c j)))
    (x : ∀ n, X n) :
    Tendsto (fun n => ∑ j : J, w n j * (χ n j (x n) : ℂ)) (U : Filter ℕ)
      (𝓝 (∑ j : J, c j *
        ((ultralimitAddHom U (fun n => (χ n j).toAddMonoidHom)
          (productProjection (U : Filter ℕ) x)).toMul : ℂ))) := by
  apply tendsto_finsetSum
  intro j _
  have hχ := tendsto_ultralimitFunction U (fun n => (χ n j).toAddMonoidHom) x
  have hcontinuous : Continuous (fun z : Additive Circle => (z.toMul : ℂ)) :=
    continuous_subtype_val
  have hvalue := (hcontinuous.tendsto _).comp hχ
  exact (hw j).mul hvalue

theorem character_polynomial_norm_le
    {J : Type*} [Fintype J] {G : Type*} [AddCommGroup G]
    (w : J → ℂ) (χ : J → AddChar G Circle) (C : ℝ) (hw : ∀ j, ‖w j‖ ≤ C) (x : G) :
    ‖∑ j : J, w j * (χ j x : ℂ)‖ ≤ Fintype.card J * C := by
  calc
    ‖∑ j : J, w j * (χ j x : ℂ)‖ ≤ ∑ j : J, ‖w j * (χ j x : ℂ)‖ := norm_sum_le _ _
    _ = ∑ j : J, ‖w j‖ := by simp only [norm_mul, Circle.norm_coe, mul_one]
    _ ≤ ∑ _j : J, C := Finset.sum_le_sum (fun j _ => hw j)
    _ = _ := by simp

theorem exists_character_polynomial_standardPart
    {J : Type*} [Fintype J] {X : ℕ → Type*} [∀ n, AddCommGroup (X n)]
    (U : Ultrafilter ℕ) (w : ℕ → J → ℂ) (χ : ∀ n, J → AddChar (X n) Circle)
    (C : ℝ) (hw : ∀ n j, ‖w n j‖ ≤ C) :
    ∃ c : J → ℂ, (∀ j, ‖c j‖ ≤ C) ∧
      boundedComplexFunction U (fun n x => ∑ j : J, w n j * (χ n j x : ℂ))
        (Fintype.card J * C) (fun n x => character_polynomial_norm_le (w n) (χ n) C (hw n) x) =
      fun x => ∑ j : J, c j *
        ((ultralimitAddHom U (fun n => (χ n j).toAddMonoidHom) x).toMul : ℂ) := by
  choose c hc hlim using fun j => exists_limit_bounded_complex U (fun n => w n j) C (fun n => hw n j)
  refine ⟨c, hc, ?_⟩
  funext x
  induction x using Quotient.inductionOn with
  | h a =>
    exact tendsto_nhds_unique
      (tendsto_boundedComplexFunction U _ _ _ a)
      (tendsto_character_polynomial U w c χ hlim a)

end Erdos335.Loeb
