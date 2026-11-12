import Erdos335.IntermediateEnergyFlatness
import Mathlib.Topology.UnitInterval

/-!
# Common flat fibers for a countable family of monotone scale profiles
-/

set_option autoImplicit false

open Set

namespace Erdos335.IntermediateScale

theorem exists_common_flat_energy_fiber {J : Type*} [Countable J]
    (a : J → ℝ → ℝ → ℝ)
    (hfiber : ∀ j x, x ∈ Icc (0 : ℝ) 1 → AntitoneOn (a j x) (Icc (0 : ℝ) 1))
    (hcross : ∀ j x, x ∈ Icc (0 : ℝ) 1 → ∀ y, y ∈ Icc (0 : ℝ) 1 →
      x < y → a j y 0 ≤ a j x 1) :
    ∃ x ∈ Ioo (0 : ℝ) 1, ∀ j t, t ∈ Icc (0 : ℝ) 1 → a j x t = a j x 0 := by
  have hc : (⋃ j, {x ∈ Icc (0 : ℝ) 1 | a j x 1 < a j x 0}).Countable :=
    countable_iUnion fun j => countable_strict_energy_fibers (a j) (hcross j)
  have hex : ∃ x ∈ Ioo (0 : ℝ) 1, ∀ j, ¬ a j x 1 < a j x 0 := by
    by_contra! h
    have hcount : (Ioo (0 : ℝ) 1).Countable := hc.mono (by
      intro x hx
      obtain ⟨j, hj⟩ := h x hx
      exact mem_iUnion.mpr ⟨j, ⟨⟨hx.1.le, hx.2.le⟩, hj⟩⟩)
    have hh := Cardinal.Real.Ioo_countable_iff.mp hcount
    norm_num at hh
  obtain ⟨x, hx, heq⟩ := hex
  have hx' : x ∈ Icc (0 : ℝ) 1 := ⟨hx.1.le, hx.2.le⟩
  refine ⟨x, hx, fun j t ht => le_antisymm ?_ ?_⟩
  · exact hfiber j x hx' ⟨le_rfl, zero_le_one⟩ ht ht.1
  · exact (le_of_not_gt (heq j)).trans (hfiber j x hx' ht ⟨zero_le_one, le_rfl⟩ ht.2)

theorem exists_common_flat_unitInterval_family {J : Type*} [Countable J]
    (a : J → unitInterval → unitInterval → ℝ)
    (hfiber : ∀ j x, Antitone (a j x))
    (hcross : ∀ j x y, x < y → a j y 0 ≤ a j x 1) :
    ∃ x : unitInterval, (x : ℝ) ∈ Ioo (0 : ℝ) 1 ∧ ∀ j t, a j x t = a j x 0 := by
  let w (j : J) (x t : ℝ) :=
    if hx : x ∈ unitInterval then if ht : t ∈ unitInterval then a j ⟨x, hx⟩ ⟨t, ht⟩ else 0 else 0
  have hfiber' (j : J) (x : ℝ) (hx : x ∈ Icc (0 : ℝ) 1) : AntitoneOn (w j x) (Icc (0 : ℝ) 1) := by
    intro t ht u hu htu
    simpa [w, unitInterval, hx.1, hx.2, ht.1, ht.2, hu.1, hu.2]
      using hfiber j ⟨x, hx⟩ (a := ⟨t, ht⟩) (b := ⟨u, hu⟩) htu
  have hcross' (j : J) (x : ℝ) (hx : x ∈ Icc (0 : ℝ) 1)
      (y : ℝ) (hy : y ∈ Icc (0 : ℝ) 1) (hxy : x < y) : w j y 0 ≤ w j x 1 := by
    simpa [w, unitInterval, hx.1, hx.2, hy.1, hy.2] using hcross j ⟨x, hx⟩ ⟨y, hy⟩ hxy
  obtain ⟨x, hx, hflat⟩ := exists_common_flat_energy_fiber w hfiber' hcross'
  have hx' : x ∈ unitInterval := ⟨hx.1.le, hx.2.le⟩
  refine ⟨⟨x, hx'⟩, hx, fun j t => ?_⟩
  simpa [w, unitInterval, hx'.1, hx'.2, t.property.1, t.property.2] using hflat j t t.property

end Erdos335.IntermediateScale
