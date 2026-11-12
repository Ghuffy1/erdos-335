import Erdos335.FiniteEnergyIncrement
import Mathlib.Algebra.Order.Floor.Semiring
import Mathlib.Algebra.Order.Archimedean.Real.Basic
import Mathlib.Data.Fintype.Prod

/-!
# Refinement by a bounded real test

Quantizing a real test into `2N+1` cells approximates it within `1/N` and
turns a detected correlation into an explicit partition-energy increment.
-/

set_option autoImplicit false

open Finset
open scoped BigOperators Classical

namespace Erdos335.IntermediateScale

noncomputable def quantizedIndex (N : ℕ) (x : ℝ) : Fin (2 * N + 1) :=
  ⟨min ⌊(N : ℝ) * (x + 1)⌋₊ (2 * N), Nat.lt_succ_of_le (min_le_right _ _)⟩

noncomputable def quantizedValue (N : ℕ) (i : Fin (2 * N + 1)) : ℝ :=
  (i.val : ℝ) / N - 1

theorem quantizedValue_bounds (N : ℕ) (hN : 0 < N) (i : Fin (2 * N + 1)) :
    quantizedValue N i ∈ Set.Icc (-1 : ℝ) 1 := by
  have hNr : (0 : ℝ) < N := by exact_mod_cast hN
  have hi : (i.val : ℝ) ≤ 2 * N := by exact_mod_cast Nat.le_of_lt_succ i.isLt
  constructor
  · dsimp [quantizedValue]
    linarith [div_nonneg (Nat.cast_nonneg i.val) hNr.le]
  · have hdiv : (i.val : ℝ) / N ≤ 2 := (div_le_iff₀ hNr).mpr (by linarith)
    dsimp [quantizedValue]
    linarith

theorem quantizedValue_approx (N : ℕ) (hN : 0 < N) (x : ℝ) (hx : |x| ≤ 1) :
    |x - quantizedValue N (quantizedIndex N x)| ≤ 1 / (N : ℝ) := by
  have hNr : (0 : ℝ) < N := by exact_mod_cast hN
  have hx' := abs_le.mp hx
  have hnonneg : 0 ≤ (N : ℝ) * (x + 1) :=
    mul_nonneg hNr.le (by linarith [hx'.1])
  have hl := Nat.floor_le hnonneg
  have hu := Nat.lt_floor_add_one ((N : ℝ) * (x + 1))
  have hf : ⌊(N : ℝ) * (x + 1)⌋₊ ≤ 2 * N := by
    have hfr : (⌊(N : ℝ) * (x + 1)⌋₊ : ℝ) ≤ 2 * N := by nlinarith
    exact_mod_cast hfr
  have hi : (quantizedIndex N x).val = ⌊(N : ℝ) * (x + 1)⌋₊ := min_eq_left hf
  have hlo : (⌊(N : ℝ) * (x + 1)⌋₊ : ℝ) / N ≤ x + 1 :=
    (div_le_iff₀ hNr).mpr (by nlinarith)
  have hhi : x + 1 < ((⌊(N : ℝ) * (x + 1)⌋₊ : ℝ) + 1) / N :=
    (lt_div_iff₀ hNr).mpr (by nlinarith)
  rw [add_div] at hhi
  rw [quantizedValue, hi]
  apply abs_le.mpr
  constructor <;> linarith [div_pos zero_lt_one hNr]

theorem quantized_partition_energy_increment
    {G K : Type*} [Fintype G] [Nonempty G] [Fintype K] [DecidableEq K]
    (π : G → K) (f u : G → ℝ) (ε : ℝ) (N : ℕ) (hN : 0 < N)
    (hε : 1 / (N : ℝ) ≤ ε)
    (hf : ∀ x, f x ∈ Set.Icc (0 : ℝ) 1) (hu : ∀ x, |u x| ≤ 1)
    (hcorr : ε * Fintype.card G ≤
      |∑ x : G, (f x - finiteConditionalMean π f x) * u x|) :
    (∑ x : G, finiteConditionalMean π f x ^ 2) +
        (ε - 1 / (N : ℝ)) ^ 2 * Fintype.card G ≤
      ∑ x : G, finiteConditionalMean (fun y => (π y, quantizedIndex N (u y))) f x ^ 2 := by
  apply finite_conditional_energy_increment π (fun y => (π y, quantizedIndex N (u y)))
    Prod.fst (fun _ => rfl) f u (fun z => quantizedValue N z.2) ε (1 / (N : ℝ)) hε hf hu
  · exact fun x => quantizedValue_approx N hN (u x) (hu x)
  · exact hcorr

end Erdos335.IntermediateScale
