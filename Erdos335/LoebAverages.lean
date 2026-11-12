import Erdos335.LoebFiniteIntegral
import Erdos335.LoebUltralimit

/-!
# Finite averages and approximation of continuous test functions
-/

set_option autoImplicit false

open Filter Set Topology MeasureTheory
open scoped ENNReal BigOperators

namespace Erdos335.Loeb

theorem countingRatio_toReal {Y : Type*} (S : Set Y) :
    (countingRatio S).toReal = (S.ncard : ℝ) / (Nat.card Y : ℝ) := by
  simp [countingRatio, ENNReal.toReal_div]

theorem finite_weighted_average {Y G : Type*} [Fintype Y] [Fintype G]
    (q : Y → G) (v : G → ℝ) :
    (∑ g, (countingRatio (q ⁻¹' {g})).toReal * v g) =
      (∑ y, v (q y)) / (Nat.card Y : ℝ) := by
  classical
  have hcard (g : G) : (q ⁻¹' {g}).ncard = (Finset.univ.filter fun y => q y = g).card := by
    have hSet : q ⁻¹' {g} = (↑(Finset.univ.filter fun y => q y = g) : Set Y) := by
      ext y
      simp
    rw [hSet, Set.ncard_coe_finset]
  have hsum : (∑ g, ((Finset.univ.filter fun y => q y = g).card : ℝ) * v g) =
      ∑ y, v (q y) := by
    simpa only [Finset.sum_const, nsmul_eq_mul] using
      (Finset.sum_fiberwise' (Finset.univ : Finset Y) q v)
  simp only [countingRatio_toReal, hcard, div_mul_eq_mul_div]
  rw [← Finset.sum_div, hsum]

theorem exists_finite_continuous_approximation
    {E : Type*} [TopologicalSpace E] [CompactSpace E]
    (g : E → ℝ) (hg : Continuous g) (ε : ℝ) (hε : 0 < ε) :
    ∃ (S : Finset ℝ) (q : E → S), ∀ x, dist (g x) (q x : ℝ) < ε := by
  classical
  obtain ⟨T, hT, hcover⟩ := Metric.totallyBounded_iff.mp (isCompact_range hg).totallyBounded ε hε
  let S := hT.toFinset
  have hex : ∀ x, ∃ y : S, dist (g x) (y : ℝ) < ε := by
    intro x
    obtain ⟨y, hy⟩ := mem_iUnion.mp (hcover (mem_range_self x))
    obtain ⟨hyT, hxy⟩ := mem_iUnion.mp hy
    exact ⟨⟨y, hT.mem_toFinset.mpr hyT⟩, hxy⟩
  choose q hq using hex
  exact ⟨S, q, hq⟩

end Erdos335.Loeb
