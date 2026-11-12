import Erdos335.FiniteSections

/-!
# Recovering ordinary section densities from residue-fiber densities
-/

set_option autoImplicit false

open Filter Set Topology

namespace Erdos335.Proposed

theorem hasDensity_residueSection_of_fiber
    (A : Set ℕ) (q : ℕ+) (r : ZMod (q : ℕ)) (a : ℝ)
    (hA : A ⊆ Set.Ioi 0) (hf : HasDensity (residueFiber A r) a) :
    HasDensity (residueSection A q r) (((q : ℕ) : ℝ) * a) := by
  have hprefix := (hasDensity_iff_prefixCount_multiples (residueFiber A r) q a).mp hf
  have hz : HasDensity (zeroSection A q r) (((q : ℕ) : ℝ) * a) := by
    apply (hasDensity_iff_prefixCount _ _).mpr
    have hp := hprefix.const_mul ((q : ℕ) : ℝ)
    apply hp.congr
    intro N
    rw [prefixCount_residueFiber A q r hA N, Nat.cast_mul]
    by_cases hN : N = 0
    · simp [hN]
    · have hNr : (N : ℝ) ≠ 0 := by exact_mod_cast hN
      have hqr : ((q : ℕ) : ℝ) ≠ 0 := by exact_mod_cast q.ne_zero
      field_simp
  rw [section_eq_zeroSection A q r hA]
  split_ifs
  · exact hz
  · exact hz.shift 1

end Erdos335.Proposed
