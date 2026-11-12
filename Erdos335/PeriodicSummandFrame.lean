import Erdos335.PeriodicSummandStrictFrame
import Erdos335.ResidueSectionDensity

/-!
# The strict periodic-summand reduction in the full classification's frame
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Filter Set Topology
open scoped Pointwise

namespace Erdos335.Proposed

theorem periodic_summand_strict_finite_frame
    (A B : Set ℕ) (a b : ℝ) (hA : A ⊆ Set.Ioi 0) (hB : B ⊆ Set.Ioi 0)
    (ha : 0 < a) (hb : 0 < b) (hdA : HasDensity A a) (hdB : HasDensity B b)
    (hdC : HasDensity (A + B) (a + b)) (hgap : a + b < gamma A B)
    (m : ℕ+) (P : Finset (ZMod (m : ℕ))) (hAP : DensityEquivalent A (periodicSet P))
    (hstrict : ((P + residues (m : ℕ) B).card : ℝ) / (m : ℕ) < a + b) :
    ∃ (f : FiniteFrame A B) (x : ℝ), (f.modulus : ℕ) ∣ (m : ℕ) ∧
      HasDensity (residueSection A f.modulus f.activeA) 0 ∧
      HasDensity (residueSection B f.modulus f.activeB) x ∧ 0 < x ∧ x < 1 := by
  obtain ⟨h, i, j, d, hhm, hi, hj, hcard, hAbg, hAzero, hBbg, hBactive, hdpos, hdlt, hunique⟩ :=
    Loeb.periodic_summand_strict_frame A B a b hA hB ha hb hdA hdB hdC hgap m P hAP hstrict
  have hh : (0 : ℝ) < (h : ℕ) := by exact_mod_cast h.pos
  have hunit : ((h : ℕ) : ℝ) * ((1 : ℝ) / (h : ℕ)) = 1 := by field_simp
  let f : FiniteFrame A B := {
    modulus := h
    activeA := i
    activeB := j
    activeA_mem := hi
    activeB_mem := hj
    backgroundA := by
      intro r hr hri
      have hs := hasDensity_residueSection_of_fiber A h r _ hA (hAbg r hr hri)
      simpa only [hunit] using hs
    backgroundB := by
      intro r hr hrj
      have hs := hasDensity_residueSection_of_fiber B h r _ hB (hBbg r hr hrj)
      simpa only [hunit] using hs
    uniqueExpression := hunique
    card_sum := hcard
  }
  refine ⟨f, ((h : ℕ) : ℝ) * d, hhm, ?_, ?_, mul_pos hh hdpos, ?_⟩
  · simpa only [mul_zero] using hasDensity_residueSection_of_fiber A h i 0 hA hAzero
  · exact hasDensity_residueSection_of_fiber B h j d hB hBactive
  · have hb := mul_lt_mul_of_pos_left hdlt hh
    rwa [hunit] at hb

end Erdos335.Proposed
