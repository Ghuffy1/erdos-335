import Mathlib.Analysis.Real.Cardinality
import Mathlib.Topology.Order.Monotone

/-!
# A constant fiber for a lexicographically monotone energy

This is the selection lemma used in Ackelsberg--Richter, Lemma 8.8.
It does not require a uniform bound on the energy.
-/

set_option autoImplicit false

open Set

namespace Erdos335.IntermediateScale

theorem countable_strict_energy_fibers (a : ℝ → ℝ → ℝ)
    (hcross : ∀ x ∈ Icc (0 : ℝ) 1, ∀ y ∈ Icc (0 : ℝ) 1,
      x < y → a y 0 ≤ a x 1) :
    {x ∈ Icc (0 : ℝ) 1 | a x 1 < a x 0}.Countable := by
  classical
  let S := {x ∈ Icc (0 : ℝ) 1 | a x 1 < a x 0}
  have hrat (x : S) : ∃ q : ℚ, a x 1 < q ∧ (q : ℝ) < a x 0 :=
    exists_rat_btwn x.property.2
  choose q hq using hrat
  have hinj : Function.Injective q := by
    intro x y heq
    apply Subtype.ext
    rcases lt_trichotomy (x : ℝ) (y : ℝ) with hxy | hxy | hyx
    · have hc := hcross x x.property.1 y y.property.1 hxy
      have hx := (hq x).1
      have hy := (hq y).2
      rw [heq] at hx
      linarith
    · exact hxy
    · have hc := hcross y y.property.1 x x.property.1 hyx
      have hx := (hq x).2
      have hy := (hq y).1
      rw [heq] at hx
      linarith
  exact hinj.countable.to_set

theorem exists_flat_energy_fiber (a : ℝ → ℝ → ℝ)
    (hfiber : ∀ x ∈ Icc (0 : ℝ) 1, AntitoneOn (a x) (Icc (0 : ℝ) 1))
    (hcross : ∀ x ∈ Icc (0 : ℝ) 1, ∀ y ∈ Icc (0 : ℝ) 1,
      x < y → a y 0 ≤ a x 1) :
    ∃ x ∈ Ioo (0 : ℝ) 1, ∀ t ∈ Icc (0 : ℝ) 1, a x t = a x 0 := by
  have hc := countable_strict_energy_fibers a hcross
  have hex : ∃ x ∈ Ioo (0 : ℝ) 1, ¬a x 1 < a x 0 := by
    by_contra! h
    have hcount : (Ioo (0 : ℝ) 1).Countable := hc.mono (by
      intro x hx
      exact ⟨⟨hx.1.le, hx.2.le⟩, h x hx⟩)
    have := Cardinal.Real.Ioo_countable_iff.mp hcount
    norm_num at this
  obtain ⟨x, hx, heq⟩ := hex
  have hx' : x ∈ Icc (0 : ℝ) 1 := ⟨hx.1.le, hx.2.le⟩
  refine ⟨x, hx, fun t ht => le_antisymm ?_ ?_⟩
  · exact hfiber x hx' ⟨by norm_num, by norm_num⟩ ht ht.1
  · exact (le_of_not_gt heq).trans
      (hfiber x hx' ht ⟨by norm_num, by norm_num⟩ ht.2)

end Erdos335.IntermediateScale
