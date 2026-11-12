import Erdos335.HilbertScaleFlatness
import Mathlib.Topology.UnitInterval

/-!
# A flat structured fiber with unit-interval parameters
-/

set_option autoImplicit false

open Set
open scoped InnerProductSpace

namespace Erdos335.IntermediateScale

theorem exists_flat_unitInterval_structured_fiber
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (f : E) (v : unitInterval → unitInterval → E)
    (hown : ∀ x t, ⟪v x t, f - v x t⟫_ℝ = 0)
    (hfiber : ∀ x t u, t ≤ u → ⟪v x u, f - v x t⟫_ℝ = 0)
    (hcross : ∀ x y, x < y → ⟪v y 0, f - v x 1⟫_ℝ = 0) :
    ∃ x : unitInterval, (x : ℝ) ∈ Ioo (0 : ℝ) 1 ∧ ∀ t, v x t = v x 0 := by
  let w (x t : ℝ) : E :=
    if hx : x ∈ unitInterval then if ht : t ∈ unitInterval then v ⟨x, hx⟩ ⟨t, ht⟩ else 0 else 0
  have hown' (x : ℝ) (hx : x ∈ Icc (0 : ℝ) 1) (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) :
      ⟪w x t, f - w x t⟫_ℝ = 0 := by
    simpa [w, unitInterval, hx.1, hx.2, ht.1, ht.2] using hown ⟨x, hx⟩ ⟨t, ht⟩
  have hfiber' (x : ℝ) (hx : x ∈ Icc (0 : ℝ) 1) (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1)
      (u : ℝ) (hu : u ∈ Icc (0 : ℝ) 1) (htu : t ≤ u) : ⟪w x u, f - w x t⟫_ℝ = 0 := by
    simpa [w, unitInterval, hx.1, hx.2, ht.1, ht.2, hu.1, hu.2]
      using hfiber ⟨x, hx⟩ ⟨t, ht⟩ ⟨u, hu⟩ htu
  have hcross' (x : ℝ) (hx : x ∈ Icc (0 : ℝ) 1) (y : ℝ) (hy : y ∈ Icc (0 : ℝ) 1)
      (hxy : x < y) : ⟪w y 0, f - w x 1⟫_ℝ = 0 := by
    simpa [w, unitInterval, hx.1, hx.2, hy.1, hy.2] using hcross ⟨x, hx⟩ ⟨y, hy⟩ hxy
  obtain ⟨x, hx, hflat⟩ := exists_flat_structured_fiber f w hown' hfiber' hcross'
  have hx' : x ∈ unitInterval := ⟨hx.1.le, hx.2.le⟩
  let z : unitInterval := ⟨x, hx'⟩
  refine ⟨z, hx, fun t => ?_⟩
  simpa [w, z, unitInterval, hx'.1, hx'.2, t.property.1, t.property.2]
    using hflat t t.property

end Erdos335.IntermediateScale
