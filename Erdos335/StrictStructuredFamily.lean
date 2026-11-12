import Erdos335.HilbertStructuredFamily

/-!
# Structured Hilbert limits with strictly increasing accuracy indices
-/

set_option autoImplicit false

open Filter Topology
open scoped InnerProductSpace

namespace Erdos335.IntermediateScale

theorem hilbert_cross_limit_of_lt {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (f u v : E) (a b : ℕ → E) (ε : ℕ → ℝ)
    (ha : Tendsto a atTop (𝓝 u)) (hb : Tendsto b atTop (𝓝 v))
    (hε : Tendsto ε atTop (𝓝 0))
    (hcross : ∀ k l, k < l → |⟪a k, f - b l⟫_ℝ| ≤ ε k) : ⟪u, f - v⟫_ℝ = 0 := by
  have hfixed (k : ℕ) : |⟪a k, f - v⟫_ℝ| ≤ ε k := by
    have hlim : Tendsto (fun l => |⟪a k, f - b l⟫_ℝ|) atTop (𝓝 |⟪a k, f - v⟫_ℝ|) :=
      (Filter.Tendsto.inner (𝕜 := ℝ) tendsto_const_nhds (tendsto_const_nhds.sub hb)).abs
    exact le_of_tendsto hlim ((eventually_gt_atTop k).mono fun l hl => hcross k l hl)
  have hlim : Tendsto (fun k => |⟪a k, f - v⟫_ℝ|) atTop (𝓝 |⟪u, f - v⟫_ℝ|) :=
    (Filter.Tendsto.inner (𝕜 := ℝ) ha tendsto_const_nhds).abs
  exact abs_eq_zero.mp (tendsto_nhds_unique hlim
    (squeeze_zero (fun k => abs_nonneg _) hfixed hε))

theorem exists_hilbert_strict_structured_family
    {E P : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E] [Preorder P]
    (f : E) (v : P → ℕ → E) (ε : ℕ → ℝ)
    (hv : ∀ p k, ‖v p k‖ ≤ 1)
    (hown : ∀ p k, ⟪v p k, f - v p k⟫_ℝ = 0)
    (hε0 : ∀ k, 0 ≤ ε k) (hε : Tendsto ε atTop (𝓝 0))
    (hcross : ∀ p q, p ≤ q → ∀ k l, k < l → |⟪v q k, f - v p l⟫_ℝ| ≤ ε k) :
    ∃ g : P → E, (∀ p, Tendsto (v p) atTop (𝓝 (g p))) ∧
      (∀ p, ‖g p‖ ≤ 1) ∧ (∀ p, ⟪g p, f - g p⟫_ℝ = 0) ∧
      (∀ p q, p ≤ q → ⟪g q, f - g p⟫_ℝ = 0) ∧
      ∀ p q, p ≤ q → ‖g q‖ ≤ ‖g p‖ := by
  have hself (p : P) (k l : ℕ) (hkl : k ≤ l) : |⟪v p k, f - v p l⟫_ℝ| ≤ ε k := by
    rcases hkl.eq_or_lt with heq | hlt
    · subst l
      simpa only [hown, abs_zero] using hε0 k
    · exact hcross p p le_rfl k l hlt
  have hex (p : P) := exists_hilbert_approximation_limit f (v p) (hv p) (hown p) ε hε (hself p)
  choose g hlim hnorm horth using hex
  have hmixed (p q : P) (hpq : p ≤ q) : ⟪g q, f - g p⟫_ℝ = 0 :=
    hilbert_cross_limit_of_lt f (g q) (g p) (v q) (v p) ε
      (hlim q) (hlim p) hε (hcross p q hpq)
  exact ⟨g, hlim, hnorm, horth, hmixed,
    fun p q hpq => nested_projection_norm_le f (g p) (g q) (horth q) (hmixed p q hpq)⟩

end Erdos335.IntermediateScale
