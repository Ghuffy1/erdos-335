import Erdos335.FiniteConditionalRefinement

/-!
# An energy increment from a detected correlation
-/

set_option autoImplicit false

open Finset
open scoped BigOperators Classical

namespace Erdos335.IntermediateScale

theorem finite_residual_test_bound {G L : Type*} [Fintype G] [Fintype L] [DecidableEq L]
    (ρ : G → L) (f u : G → ℝ) (g : L → ℝ) (δ : ℝ)
    (hf : ∀ x, f x ∈ Set.Icc (0 : ℝ) 1)
    (happrox : ∀ x, |u x - g (ρ x)| ≤ δ) :
    |∑ x : G, (f x - finiteConditionalMean ρ f x) * u x| ≤ δ * Fintype.card G := by
  have hzero := finiteConditionalMean_orthogonal ρ f g
  have hsum : (∑ x : G, (f x - finiteConditionalMean ρ f x) * u x) =
      ∑ x : G, (f x - finiteConditionalMean ρ f x) * (u x - g (ρ x)) := by
    calc
      _ = (∑ x : G, (f x - finiteConditionalMean ρ f x) * (u x - g (ρ x))) +
          ∑ x : G, g (ρ x) * (f x - finiteConditionalMean ρ f x) := by
        rw [← sum_add_distrib]
        apply sum_congr rfl
        intro x hx
        ring
      _ = _ := by rw [hzero, add_zero]
  rw [hsum]
  calc
    _ ≤ ∑ x : G, |(f x - finiteConditionalMean ρ f x) * (u x - g (ρ x))| :=
      abs_sum_le_sum_abs _ _
    _ ≤ ∑ _x : G, δ := by
      apply sum_le_sum
      intro x hx
      have hm := finiteConditionalMean_bounds ρ f hf x
      have hr : |f x - finiteConditionalMean ρ f x| ≤ 1 := by
        apply abs_le.mpr
        constructor <;> linarith [(hf x).1, (hf x).2, hm.1, hm.2]
      rw [abs_mul]
      exact (mul_le_mul hr (happrox x) (abs_nonneg _) zero_le_one).trans_eq (one_mul _)
    _ = _ := by simp [mul_comm]

theorem finite_unit_test_cauchy {G : Type*} [Fintype G] (v u : G → ℝ)
    (hu : ∀ x, |u x| ≤ 1) :
    (∑ x : G, v x * u x) ^ 2 ≤ (∑ x : G, v x ^ 2) * Fintype.card G := by
  have hsum : (∑ x : G, u x ^ 2) ≤ Fintype.card G := by
    calc
      _ ≤ ∑ _x : G, (1 : ℝ) := by
        apply sum_le_sum
        intro x hx
        have hux := abs_le.mp (hu x)
        nlinarith
      _ = _ := by simp
  exact (sum_mul_sq_le_sq_mul_sq univ v u).trans
    (mul_le_mul_of_nonneg_left hsum (sum_nonneg fun _ _ => sq_nonneg _))

theorem finite_conditional_energy_increment
    {G K L : Type*} [Fintype G] [Nonempty G] [Fintype K] [Fintype L]
    [DecidableEq K] [DecidableEq L]
    (π : G → K) (ρ : G → L) (σ : L → K) (hπ : ∀ x, π x = σ (ρ x))
    (f u : G → ℝ) (g : L → ℝ) (ε δ : ℝ) (hεδ : δ ≤ ε)
    (hf : ∀ x, f x ∈ Set.Icc (0 : ℝ) 1) (hu : ∀ x, |u x| ≤ 1)
    (happrox : ∀ x, |u x - g (ρ x)| ≤ δ)
    (hcorr : ε * Fintype.card G ≤
      |∑ x : G, (f x - finiteConditionalMean π f x) * u x|) :
    (∑ x : G, finiteConditionalMean π f x ^ 2) + (ε - δ) ^ 2 * Fintype.card G ≤
      ∑ x : G, finiteConditionalMean ρ f x ^ 2 := by
  let v := fun x => finiteConditionalMean ρ f x - finiteConditionalMean π f x
  have hrest := finite_residual_test_bound ρ f u g δ hf happrox
  have hsplit : (∑ x : G, (f x - finiteConditionalMean π f x) * u x) =
      (∑ x : G, v x * u x) +
        ∑ x : G, (f x - finiteConditionalMean ρ f x) * u x := by
    rw [← sum_add_distrib]
    apply sum_congr rfl
    intro x hx
    dsimp [v]
    ring
  rw [hsplit] at hcorr
  have hlin : (ε - δ) * Fintype.card G ≤ |∑ x : G, v x * u x| := by
    have htriangle := abs_add_le (∑ x : G, v x * u x)
      (∑ x : G, (f x - finiteConditionalMean ρ f x) * u x)
    nlinarith
  have hleft : 0 ≤ (ε - δ) * Fintype.card G := by positivity
  have hsq := pow_le_pow_left₀ hleft hlin 2
  rw [sq_abs] at hsq
  have hcs := finite_unit_test_cauchy v u hu
  have hN : (0 : ℝ) < Fintype.card G := by exact_mod_cast Fintype.card_pos
  have hgain : (ε - δ) ^ 2 * Fintype.card G ≤ ∑ x : G, v x ^ 2 := by
    apply (mul_le_mul_iff_of_pos_right hN).mp
    calc
      _ = ((ε - δ) * Fintype.card G) ^ 2 := by ring
      _ ≤ _ := hsq.trans hcs
  rw [refinement_energy_identity π ρ σ hπ f]
  exact add_le_add le_rfl hgain

end Erdos335.IntermediateScale
