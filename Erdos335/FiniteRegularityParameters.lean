import Erdos335.FiniteTestRegularity

/-!
# Uniform parameters for finite test regularity
-/

set_option autoImplicit false

namespace Erdos335.IntermediateScale

theorem exists_finite_regularity_parameters (ε : ℝ) (hε : 0 < ε) :
    ∃ N D : ℕ, 0 < N ∧ 1 / (N : ℝ) ≤ ε / 2 ∧
      1 < (D : ℝ) * (ε - 1 / (N : ℝ)) ^ 2 := by
  obtain ⟨N, hN⟩ := exists_nat_gt (max 1 (2 / ε))
  have hN1 : (1 : ℝ) < N := (le_max_left _ _).trans_lt hN
  have hNpos : 0 < N := by exact_mod_cast (lt_trans zero_lt_one hN1)
  have hNposR : (0 : ℝ) < N := lt_trans zero_lt_one hN1
  have hbound : 1 / (N : ℝ) ≤ ε / 2 := by
    have hlarge := (le_max_right (1 : ℝ) (2 / ε)).trans_lt hN
    have hprod : 2 < (N : ℝ) * ε := (div_lt_iff₀ hε).mp hlarge
    apply (div_le_iff₀ hNposR).mpr
    nlinarith
  have hsq : 0 < (ε - 1 / (N : ℝ)) ^ 2 := by
    apply sq_pos_of_pos
    linarith
  obtain ⟨D, hD⟩ := exists_nat_gt (1 / (ε - 1 / (N : ℝ)) ^ 2)
  refine ⟨N, D, hNpos, hbound, ?_⟩
  exact (div_lt_iff₀ hsq).mp hD

theorem finite_test_regularity_with_uniform_parameters
    {G : Type*} [Fintype G] [Nonempty G]
    (ε : ℝ) (hε : 0 < ε) :
    ∃ N D : ℕ, 0 < N ∧ ∀ (f : G → ℝ) (allowed : Set (G → ℝ)),
      (∀ x, f x ∈ Set.Icc (0 : ℝ) 1) →
      (∀ u ∈ allowed, ∀ x, |u x| ≤ 1) →
      ∃ S : Finset (G → ℝ), (S : Set (G → ℝ)) ⊆ allowed ∧ S.card ≤ D ∧
        ∀ u ∈ allowed,
          |∑ x : G, (f x - finiteConditionalMean (testPartition N S) f x) * u x| ≤
            ε * Fintype.card G := by
  obtain ⟨N, D, hN, hbound, hD⟩ := exists_finite_regularity_parameters ε hε
  refine ⟨N, D, hN, fun f allowed hf hallowed => ?_⟩
  exact finite_test_regularity f hf allowed hallowed ε N D hN
    (hbound.trans (by linarith)) hD

end Erdos335.IntermediateScale
