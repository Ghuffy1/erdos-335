import Erdos335.LoebRealBounds
import Erdos335.HilbertStructuredFamily

/-!
# Structured Hilbert limits from scale-indexed internal decompositions
-/

set_option autoImplicit false

open Filter Set Topology MeasureTheory
open scoped BigOperators InnerProductSpace

namespace Erdos335.Loeb

theorem exists_loeb_structured_family
    {X : ℕ → Type*} [∀ n, Fintype (X n)] [∀ n, Nonempty (X n)]
    {P : Type*} [Preorder P]
    (U : Ultrafilter ℕ) (hU : (U : Filter ℕ) ≤ atTop)
    (F : ∀ n, X n → ℝ) (v : P → ℕ → ∀ n, X n → ℝ)
    (hF : ∀ n x, F n x ∈ Icc (0 : ℝ) 1)
    (hv : ∀ p k n x, v p k n x ∈ Icc (0 : ℝ) 1)
    (ε : ℕ → ℝ) (hε : Tendsto ε atTop (𝓝 0))
    (hown : ∀ p k, Tendsto
      (fun n => (∑ x : X n, v p k n x * (F n x - v p k n x)) / (Nat.card (X n) : ℝ))
      (U : Filter ℕ) (𝓝 0))
    (hcross : ∀ p q, p ≤ q → ∀ k l, k ≤ l → ∀ᶠ n in (U : Filter ℕ),
      |(∑ x : X n, v q k n x * (F n x - v p l n x)) / (Nat.card (X n) : ℝ)| ≤ ε k) :
    ∃ g : P → Lp ℝ 2 (loebMeasure (X := X) U hU),
      (∀ p, Tendsto (fun k => realLoebVector U hU (v p k) (hv p k)) atTop (𝓝 (g p))) ∧
      (∀ p, ‖g p‖ ≤ 1) ∧
      (∀ p, ⟪g p, realLoebVector U hU F hF - g p⟫_ℝ = 0) ∧
      (∀ p q, p ≤ q → ⟪g q, realLoebVector U hU F hF - g p⟫_ℝ = 0) ∧
      ∀ p q, p ≤ q → ‖g q‖ ≤ ‖g p‖ := by
  let : MeasurableSpace ((U : Filter ℕ).Product X) := loebMeasurableSpace U
  apply Erdos335.IntermediateScale.exists_hilbert_structured_family
    (realLoebVector U hU F hF) (fun p k => realLoebVector U hU (v p k) (hv p k)) ε
  · exact fun p k => realLoebVector_norm_le_one U hU (v p k) (hv p k)
  · exact fun p k => realLoebVector_residual_inner_eq_zero U hU F (v p k) hF (hv p k) (hown p k)
  · exact hε
  · intro p q hpq k l hkl
    exact realLoebVector_residual_inner_bound U hU F (v q k) (v p l) hF (hv q k) (hv p l)
      (ε k) (hcross p q hpq k l hkl)

end Erdos335.Loeb
