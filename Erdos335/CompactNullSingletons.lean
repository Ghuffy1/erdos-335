import Erdos335.CompactDysonTransform
import Mathlib.MeasureTheory.Measure.Regular

/-!
# Small identity neighborhoods in an infinite compact group
-/

set_option autoImplicit false

open Set MeasureTheory
open scoped Pointwise ENNReal

namespace Erdos335.Loeb

theorem singleton_measure_zero_of_infinite_invariant
    {G : Type*} [AddCommGroup G] [Infinite G]
    [MeasurableSpace G] [MeasurableSingletonClass G] [MeasurableAdd₂ G]
    (μ : Measure G) [IsFiniteMeasure μ] [μ.IsAddLeftInvariant] (x : G) : μ {x} = 0 := by
  have hpoint (y : G) : μ {y} = μ ({0} : Set G) := by
    have hset : y +ᵥ ({0} : Set G) = {y} := by simp
    rw [← hset, vadd_set_eq_neg_preimage, measure_preimage_add]
  have hzero : μ ({0} : Set G) = 0 := by
    by_contra hn
    have htop : μ (univ : Set G) = ∞ :=
      Set.infinite_univ.meas_eq_top ⟨μ ({0} : Set G), hn, fun y _ => (hpoint y).ge⟩
    exact measure_ne_top μ univ htop
  exact (hpoint x).trans hzero

theorem exists_small_open_identity_neighborhood
    {G : Type*} [AddCommGroup G] [Infinite G]
    [TopologicalSpace G] [T2Space G] [MeasurableSpace G] [BorelSpace G] [MeasurableAdd₂ G]
    (μ : Measure G) [IsFiniteMeasure μ] [μ.InnerRegularCompactLTTop] [μ.IsAddLeftInvariant]
    (ε : ℝ) (hε : 0 < ε) :
    ∃ U : Set G, IsOpen U ∧ 0 ∈ U ∧ (μ U).toReal < ε := by
  have hsmall : μ ({0} : Set G) < ENNReal.ofReal ε := by
    rw [singleton_measure_zero_of_infinite_invariant μ 0]
    exact ENNReal.ofReal_pos.mpr hε
  obtain ⟨U, hsub, hU, hmass⟩ := isCompact_singleton.exists_isOpen_lt_of_lt (μ := μ)
    (K := ({0} : Set G)) (ENNReal.ofReal ε) hsmall
  refine ⟨U, hU, hsub (by simp), ?_⟩
  have hreal := (ENNReal.toReal_lt_toReal (measure_ne_top μ U) ENNReal.ofReal_ne_top).mpr hmass
  simpa only [ENNReal.toReal_ofReal hε.le] using hreal

end Erdos335.Loeb
