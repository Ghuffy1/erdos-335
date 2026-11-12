import Erdos335.IntermediateEnergyFlatness
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Tactic.Linarith

/-!
# Equality of nested structured components on a flat energy fiber
-/

set_option autoImplicit false

open Set
open scoped InnerProductSpace

namespace Erdos335.IntermediateScale

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

theorem nested_projection_norm_identity (f g h : E)
    (hown : ⟪h, f - h⟫_ℝ = 0) (hmixed : ⟪h, f - g⟫_ℝ = 0) :
    ‖g - h‖ ^ 2 = ‖g‖ ^ 2 - ‖h‖ ^ 2 := by
  rw [inner_sub_right, real_inner_self_eq_norm_sq] at hown
  rw [inner_sub_right] at hmixed
  rw [norm_sub_sq_real, real_inner_comm h g]
  linarith

theorem nested_projection_norm_le (f g h : E)
    (hown : ⟪h, f - h⟫_ℝ = 0) (hmixed : ⟪h, f - g⟫_ℝ = 0) : ‖h‖ ≤ ‖g‖ := by
  have hid := nested_projection_norm_identity f g h hown hmixed
  nlinarith [sq_nonneg ‖g - h‖, norm_nonneg g, norm_nonneg h]

theorem nested_projection_eq_of_norm_eq (f g h : E)
    (hown : ⟪h, f - h⟫_ℝ = 0) (hmixed : ⟪h, f - g⟫_ℝ = 0)
    (hnorm : ‖h‖ = ‖g‖) : h = g := by
  have hid := nested_projection_norm_identity f g h hown hmixed
  rw [hnorm, sub_self] at hid
  have hz : ‖g - h‖ = 0 := by nlinarith [norm_nonneg (g - h)]
  exact (sub_eq_zero.mp (norm_eq_zero.mp hz)).symm

theorem exists_flat_structured_fiber (f : E) (v : ℝ → ℝ → E)
    (hown : ∀ x ∈ Icc (0 : ℝ) 1, ∀ t ∈ Icc (0 : ℝ) 1,
      ⟪v x t, f - v x t⟫_ℝ = 0)
    (hfiber : ∀ x ∈ Icc (0 : ℝ) 1, ∀ t ∈ Icc (0 : ℝ) 1, ∀ u ∈ Icc (0 : ℝ) 1,
      t ≤ u → ⟪v x u, f - v x t⟫_ℝ = 0)
    (hcross : ∀ x ∈ Icc (0 : ℝ) 1, ∀ y ∈ Icc (0 : ℝ) 1,
      x < y → ⟪v y 0, f - v x 1⟫_ℝ = 0) :
    ∃ x ∈ Ioo (0 : ℝ) 1, ∀ t ∈ Icc (0 : ℝ) 1, v x t = v x 0 := by
  have hfiberNorm : ∀ x ∈ Icc (0 : ℝ) 1,
      AntitoneOn (fun t => ‖v x t‖) (Icc (0 : ℝ) 1) := by
    intro x hx t ht u hu htu
    exact nested_projection_norm_le f (v x t) (v x u) (hown x hx u hu) (hfiber x hx t ht u hu htu)
  have hcrossNorm : ∀ x ∈ Icc (0 : ℝ) 1, ∀ y ∈ Icc (0 : ℝ) 1,
      x < y → ‖v y 0‖ ≤ ‖v x 1‖ := by
    intro x hx y hy hxy
    exact nested_projection_norm_le f (v x 1) (v y 0)
      (hown y hy 0 ⟨le_rfl, zero_le_one⟩) (hcross x hx y hy hxy)
  obtain ⟨x, hx, hflat⟩ := exists_flat_energy_fiber (fun x t => ‖v x t‖) hfiberNorm hcrossNorm
  refine ⟨x, hx, fun t ht => ?_⟩
  have hx' : x ∈ Icc (0 : ℝ) 1 := ⟨hx.1.le, hx.2.le⟩
  exact nested_projection_eq_of_norm_eq f (v x 0) (v x t) (hown x hx' t ht)
    (hfiber x hx' 0 ⟨le_rfl, zero_le_one⟩ t ht ht.1) (hflat t ht)

end Erdos335.IntermediateScale
