import Erdos335.HilbertApproximationLimit
import Erdos335.HilbertCrossLimit
import Erdos335.HilbertScaleFlatness

/-!
# Nested limits of scale-indexed structured approximations
-/

set_option autoImplicit false

open Filter Topology
open scoped InnerProductSpace

namespace Erdos335.IntermediateScale

theorem exists_hilbert_structured_family
    {E P : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E] [Preorder P]
    (f : E) (v : P → ℕ → E) (ε : ℕ → ℝ)
    (hv : ∀ p k, ‖v p k‖ ≤ 1)
    (hown : ∀ p k, ⟪v p k, f - v p k⟫_ℝ = 0)
    (hε : Tendsto ε atTop (𝓝 0))
    (hcross : ∀ p q, p ≤ q → ∀ k l, k ≤ l → |⟪v q k, f - v p l⟫_ℝ| ≤ ε k) :
    ∃ g : P → E, (∀ p, Tendsto (v p) atTop (𝓝 (g p))) ∧
      (∀ p, ‖g p‖ ≤ 1) ∧ (∀ p, ⟪g p, f - g p⟫_ℝ = 0) ∧
      (∀ p q, p ≤ q → ⟪g q, f - g p⟫_ℝ = 0) ∧
      ∀ p q, p ≤ q → ‖g q‖ ≤ ‖g p‖ := by
  have hex (p : P) := exists_hilbert_approximation_limit f (v p) (hv p) (hown p) ε hε
    (hcross p p le_rfl)
  choose g hlim hnorm horth using hex
  have hmixed (p q : P) (hpq : p ≤ q) : ⟪g q, f - g p⟫_ℝ = 0 :=
    hilbert_cross_limit f (g q) (g p) (v q) (v p) ε (hlim q) (hlim p) hε (hcross p q hpq)
  refine ⟨g, hlim, hnorm, horth, hmixed, ?_⟩
  intro p q hpq
  exact nested_projection_norm_le f (g p) (g q) (horth q) (hmixed p q hpq)

end Erdos335.IntermediateScale
