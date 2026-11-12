import Erdos335.NullFrameCoverage
import Erdos335.PeriodicBackgroundParts

/-!
# Singleton or sparse-transition classification of a null-active finite frame
-/

set_option autoImplicit false

open Filter Set Topology
open scoped Pointwise

namespace Erdos335.Proposed

theorem FiniteFrame.null_left_common_difference_period
    {A B : Set ℕ} (f : FiniteFrame A B)
    (hA : A ⊆ Set.Ioi 0) (hB : B ⊆ Set.Ioi 0) (a b x : ℝ)
    (hdA : HasDensity A a) (hdB : HasDensity B b) (hdC : HasDensity (A + B) (a + b))
    (hzero : HasDensity (residueSection A f.modulus f.activeA) 0)
    (hactive : HasDensity (residueSection B f.modulus f.activeB) x)
    (u v : ℕ) (hu : u ∈ residueFiber A f.activeA) (hv : v ∈ residueFiber A f.activeA)
    (huv : u < v) :
    DensityEquivalent (shift A (v - u)) A ∧ DensityEquivalent (shift B (v - u)) B := by
  have hur : (u : ZMod (f.modulus : ℕ)) = f.activeA := by
    simpa only [Finset.mem_singleton] using hu.2.2
  have hvr : (v : ZMod (f.modulus : ℕ)) = f.activeA := by
    simpa only [Finset.mem_singleton] using hv.2.2
  have hdiv : (f.modulus : ℕ) ∣ v - u := by
    apply (ZMod.natCast_eq_zero_iff (v - u) (f.modulus : ℕ)).mp
    rw [Nat.cast_sub huv.le, hur, hvr, sub_self]
  have hz : Negligible (residueFiber A f.activeA) := by
    change HasDensity (residueFiber A f.activeA) 0
    simpa only [zero_div] using hasDensity_residueFiber hA hzero
  have hAzeroPeriod : DensityEquivalent (shift (residueFiber A f.activeA) (v - u))
      (residueFiber A f.activeA) :=
    ⟨(hz.shift (v - u)).mono Set.sdiff_subset, hz.mono Set.sdiff_subset⟩
  constructor
  · exact period_from_exceptional_fiber A f.modulus f.activeA hA
      (fun r hr hri => missing_fiber_of_full_section hA (f.backgroundA r hr hri))
      (v - u) hdiv hAzeroPeriod
  · exact period_from_exceptional_fiber B f.modulus f.activeB hB
      (fun r hr hrj => missing_fiber_of_full_section hB (f.backgroundB r hr hrj))
      (v - u) hdiv (f.null_left_active_difference_period hA hB a b x hdA hdB hdC hzero hactive u v hu hv huv.le)

theorem FiniteFrame.null_left_classified
    {A B : Set ℕ} (f : FiniteFrame A B)
    (hA : A ⊆ Set.Ioi 0) (hB : B ⊆ Set.Ioi 0) (a b x : ℝ)
    (hdA : HasDensity A a) (hdB : HasDensity B b) (hdC : HasDensity (A + B) (a + b))
    (hzero : HasDensity (residueSection A f.modulus f.activeA) 0)
    (hactive : HasDensity (residueSection B f.modulus f.activeB) x)
    (hxpos : 0 < x) (hxlt : x < 1) :
    SingletonBranch A B ∨ MaskBranch A B (a + b) := by
  classical
  by_cases hsingle : ∃ k : ℕ, residueSection A f.modulus f.activeA = {k}
  · exact Or.inl ⟨f, x, hxpos, hxlt, Or.inl ⟨hsingle, hactive⟩⟩
  obtain ⟨a₀, ha₀, hares⟩ := mem_residues.mp f.activeA_mem
  have haf : a₀ ∈ residueFiber A f.activeA :=
    ⟨ha₀, hA ha₀, by simpa only [Finset.mem_singleton] using hares⟩
  rw [residueFiber_eq_image A f.modulus f.activeA] at haf
  obtain ⟨k, hk, _⟩ := haf
  have hex : ∃ l ∈ residueSection A f.modulus f.activeA, l ≠ k := by
    by_contra hn
    apply hsingle
    refine ⟨k, ?_⟩
    ext l
    constructor
    · intro hl
      have heq : l = k := by
        by_contra hne
        exact hn ⟨l, hl, hne⟩
      exact Set.mem_singleton_iff.mpr heq
    · intro hl
      simpa only [Set.mem_singleton_iff.mp hl] using hk
  obtain ⟨l, hl, hlk⟩ := hex
  let u := sectionPoint f.modulus f.activeA k
  let v := sectionPoint f.modulus f.activeA l
  have hu : u ∈ residueFiber A f.activeA := by
    rw [residueFiber_eq_image]
    exact ⟨k, hk, rfl⟩
  have hv : v ∈ residueFiber A f.activeA := by
    rw [residueFiber_eq_image]
    exact ⟨l, hl, rfl⟩
  have huv : u ≠ v := by
    intro heq
    have hmul : (f.modulus : ℕ) * (k - 1) = (f.modulus : ℕ) * (l - 1) :=
      Nat.add_right_cancel heq
    have hsub : k - 1 = l - 1 := Nat.eq_of_mul_eq_mul_left f.modulus.pos hmul
    have hkpos := hk.1
    have hlpos := hl.1
    exact hlk (by omega)
  obtain ⟨q, hAq, hBq⟩ : ∃ q : ℕ+,
      DensityEquivalent (shift A (q : ℕ)) A ∧ DensityEquivalent (shift B (q : ℕ)) B := by
    rcases lt_or_gt_of_ne huv with huv | hvu
    · exact ⟨⟨v - u, Nat.sub_pos_of_lt huv⟩,
        f.null_left_common_difference_period hA hB a b x hdA hdB hdC hzero hactive u v hu hv huv⟩
    · exact ⟨⟨u - v, Nat.sub_pos_of_lt hvu⟩,
        f.null_left_common_difference_period hA hB a b x hdA hdB hdC hzero hactive v u hv hu hvu⟩
  obtain ⟨FA, FB, hFA, hFB, hcover⟩ := f.null_left_finite_translate_coverage hA hB a b x
    hdA hdB hdC hzero hactive
  exact Or.inr ((maskBranch_iff_common_period_finite_translate_cover A B (a + b)).mpr
    ⟨hdC, q, FA, FB, hAq, hBq, hFA, hFB, hcover⟩)

end Erdos335.Proposed
