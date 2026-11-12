import Erdos335.HilbertApproximationLimit

/-!
# Mixed orthogonality of limiting structured components
-/

set_option autoImplicit false

open Filter Topology
open scoped InnerProductSpace

namespace Erdos335.IntermediateScale

theorem hilbert_cross_limit {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (f u v : E) (a b : ℕ → E) (ε : ℕ → ℝ)
    (ha : Tendsto a atTop (𝓝 u)) (hb : Tendsto b atTop (𝓝 v))
    (hε : Tendsto ε atTop (𝓝 0))
    (hcross : ∀ k l, k ≤ l → |⟪a k, f - b l⟫_ℝ| ≤ ε k) : ⟪u, f - v⟫_ℝ = 0 := by
  have hfixed (k : ℕ) : |⟪a k, f - v⟫_ℝ| ≤ ε k := by
    have hlim : Tendsto (fun l => |⟪a k, f - b l⟫_ℝ|) atTop (𝓝 |⟪a k, f - v⟫_ℝ|) :=
      (Filter.Tendsto.inner (𝕜 := ℝ) tendsto_const_nhds (tendsto_const_nhds.sub hb)).abs
    apply le_of_tendsto hlim
    exact (eventually_ge_atTop k).mono fun l hl => hcross k l hl
  have hlim : Tendsto (fun k => |⟪a k, f - v⟫_ℝ|) atTop (𝓝 |⟪u, f - v⟫_ℝ|) :=
    (Filter.Tendsto.inner (𝕜 := ℝ) ha tendsto_const_nhds).abs
  have hzero := squeeze_zero (fun k => abs_nonneg ⟪a k, f - v⟫_ℝ) hfixed hε
  exact abs_eq_zero.mp (tendsto_nhds_unique hlim hzero)

end Erdos335.IntermediateScale
