import Erdos335.FiniteEnergySelection
import Mathlib.Data.Fintype.Pi

/-!
# Finite weak regularity for an arbitrary bounded family of tests

The selected test family has bounded size independent of the ambient finite
set. Its quantized common refinement yields a nonnegative conditional
average whose residual has small correlation with every allowed test.
-/

set_option autoImplicit false

open Finset
open scoped BigOperators Classical

namespace Erdos335.IntermediateScale

variable {G : Type*} [Fintype G]

noncomputable def testPartition (N : ℕ) (S : Finset (G → ℝ)) (x : G) : S → Fin (2 * N + 1) :=
  fun u => quantizedIndex N (u.val x)

noncomputable def testEnergy (f : G → ℝ) (N : ℕ) (S : Finset (G → ℝ)) : ℝ :=
  (∑ x : G, finiteConditionalMean (testPartition N S) f x ^ 2) / Fintype.card G

theorem testEnergy_bounds (f : G → ℝ) (hf : ∀ x, f x ∈ Set.Icc (0 : ℝ) 1)
    (N : ℕ) (S : Finset (G → ℝ)) : testEnergy f N S ∈ Set.Icc (0 : ℝ) 1 := by
  constructor
  · exact div_nonneg (sum_nonneg fun _ _ => sq_nonneg _) (Nat.cast_nonneg _)
  · have hsum : (∑ x : G, finiteConditionalMean (testPartition N S) f x ^ 2) ≤
        Fintype.card G := by
      calc
        _ ≤ ∑ _x : G, (1 : ℝ) := by
          apply sum_le_sum
          intro x hx
          have h := finiteConditionalMean_bounds (testPartition N S) f hf x
          nlinarith [h.1, h.2]
        _ = _ := by simp
    exact div_le_one_of_le₀ hsum (Nat.cast_nonneg _)

theorem testEnergy_insert_increment [Nonempty G]
    (f : G → ℝ) (hf : ∀ x, f x ∈ Set.Icc (0 : ℝ) 1)
    (N : ℕ) (hN : 0 < N) (S : Finset (G → ℝ)) (u : G → ℝ)
    (hu : ∀ x, |u x| ≤ 1) (ε : ℝ) (hε : 1 / (N : ℝ) ≤ ε)
    (hcorr : ε * Fintype.card G ≤
      |∑ x : G, (f x - finiteConditionalMean (testPartition N S) f x) * u x|) :
    testEnergy f N S + (ε - 1 / (N : ℝ)) ^ 2 ≤ testEnergy f N (insert u S) := by
  let T : Finset (G → ℝ) := insert u S
  let σ : (T → Fin (2 * N + 1)) → (S → Fin (2 * N + 1)) :=
    fun r v => r ⟨v.val, mem_insert_of_mem v.property⟩
  let g : (T → Fin (2 * N + 1)) → ℝ :=
    fun r => quantizedValue N (r ⟨u, mem_insert_self u S⟩)
  have hπ (x : G) : testPartition N S x = σ (testPartition N (insert u S) x) := rfl
  have happ (x : G) : |u x - g (testPartition N (insert u S) x)| ≤ 1 / (N : ℝ) :=
    quantizedValue_approx N hN (u x) (hu x)
  have hi := finite_conditional_energy_increment (testPartition N S)
    (testPartition N (insert u S)) σ hπ f u g ε (1 / (N : ℝ)) hε hf hu happ hcorr
  have hG : (0 : ℝ) < Fintype.card G := by exact_mod_cast Fintype.card_pos
  have hdiv := div_le_div_of_nonneg_right hi hG.le
  simpa only [testEnergy, add_div, mul_div_cancel_right₀ _ hG.ne'] using hdiv

theorem finite_test_regularity [Nonempty G]
    (f : G → ℝ) (hf : ∀ x, f x ∈ Set.Icc (0 : ℝ) 1)
    (allowed : Set (G → ℝ)) (hallowed : ∀ u ∈ allowed, ∀ x, |u x| ≤ 1)
    (ε : ℝ) (N D : ℕ) (hN : 0 < N) (hε : 1 / (N : ℝ) ≤ ε)
    (hD : 1 < (D : ℝ) * (ε - 1 / (N : ℝ)) ^ 2) :
    ∃ S : Finset (G → ℝ), (S : Set (G → ℝ)) ⊆ allowed ∧ S.card ≤ D ∧
      ∀ u ∈ allowed,
        |∑ x : G, (f x - finiteConditionalMean (testPartition N S) f x) * u x| ≤
          ε * Fintype.card G := by
  let good := fun S : Finset (G → ℝ) => ∀ u ∈ allowed,
    |∑ x : G, (f x - finiteConditionalMean (testPartition N S) f x) * u x| ≤
      ε * Fintype.card G
  apply bounded_energy_selection allowed good (testEnergy f N)
    ((ε - 1 / (N : ℝ)) ^ 2) 1 D (testEnergy_bounds f hf N ∅).1
    (fun S _ => (testEnergy_bounds f hf N S).2) hD
  intro S hS hbad
  obtain ⟨u, hnot⟩ := not_forall.mp hbad
  have huAllowed : u ∈ allowed := by by_contra h; exact hnot (fun hmem => False.elim (h hmem))
  have hcorr : ε * Fintype.card G ≤
      |∑ x : G, (f x - finiteConditionalMean (testPartition N S) f x) * u x| := by
    by_contra h
    exact hnot (fun _ => le_of_lt (lt_of_not_ge h))
  refine ⟨insert u S, ?_, card_insert_le u S, ?_⟩
  · intro v hv
    rcases mem_insert.mp hv with rfl | hv
    · exact huAllowed
    · exact hS hv
  · exact testEnergy_insert_increment f hf N hN S u (hallowed u huAllowed) ε hε hcorr

end Erdos335.IntermediateScale
