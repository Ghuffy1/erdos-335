import Erdos335.RealSetEndpointWidth

/-!
# Small endpoint differences for localized positive real sets
-/

set_option autoImplicit false

open Set Filter Topology MeasureTheory
open scoped Pointwise

namespace Erdos335.Loeb

theorem exists_localized_endpoint_sequence
    (B : ℕ → Set ℝ) (hbelow : ∀ n, BddBelow (B n)) (habove : ∀ n, BddAbove (B n))
    (hpositive : ∀ n, 0 < volume (B n))
    (hlocal : ∀ V ∈ 𝓝 (0 : ℝ), ∀ᶠ n in atTop, B n - B n ⊆ V)
    (ε : ℕ → ℝ) (hε : ∀ n, 0 < ε n) :
    ∃ x y : ℕ → ℝ,
      (∀ n, x n ∈ B n ∧ y n ∈ B n ∧ x n < y n ∧
        (volume (B n)).toReal ≤ (1 + ε n) * (y n - x n)) ∧
      Tendsto (fun n => y n - x n) atTop (𝓝 0) := by
  choose x hx y hy hxy hbound using
    fun n => exists_endpoints_cover_measure (B n) (hbelow n) (habove n) (hpositive n) (ε n) (hε n)
  refine ⟨x, y, fun n => ⟨hx n, hy n, hxy n, hbound n⟩, ?_⟩
  apply tendsto_def.mpr
  intro V hV
  filter_upwards [hlocal V hV] with n hn
  exact hn ⟨y n, hy n, x n, hx n, rfl⟩

end Erdos335.Loeb
