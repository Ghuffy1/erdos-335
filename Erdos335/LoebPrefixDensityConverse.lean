import Erdos335.LoebPeriodicPrefix

/-!
# Ordinary residue density from all prefix ultralimits
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Filter Set Topology MeasureTheory
open Erdos335.IntermediateScale
open scoped Pointwise ENNReal

noncomputable section

namespace Erdos335.Loeb

local instance prefixDensityConverseLoebSpace (U : Ultrafilter ℕ) (q : ℕ → ℕ+) :
    MeasurableSpace ((U : Filter ℕ).Product (fun n => ZMod (q n : ℕ))) := loebMeasurableSpace U

def positiveMultipleSequence (m : ℕ+) (n : ℕ) : ℕ+ := m * ⟨n + 1, Nat.succ_pos n⟩

theorem positiveMultipleSequence_tendsto (m : ℕ+) :
    Tendsto (fun n => (positiveMultipleSequence m n : ℕ)) atTop atTop := by
  exact (tendsto_mul_nat_atTop m).comp (tendsto_add_atTop_nat 1)

theorem residueFiber_density_of_all_prefix_measures
    (A : Set ℕ) (hA : A ⊆ Set.Ioi 0) (m h : ℕ+) (hhm : (h : ℕ) ∣ (m : ℕ))
    (r : ZMod (h : ℕ)) (a : ℝ)
    (hall : ∀ (U : Ultrafilter ℕ) (hU : (U : Filter ℕ) ≤ atTop),
      (loebMeasure U hU (internalSet U
        (fun n => (cyclicWindow A 0 (positiveMultipleSequence m n : ℕ) :
          Set (ZMod (positiveMultipleSequence m n : ℕ)))) ∩
            (finiteQuotient U (fun n => naturalCyclicProjection (positiveMultipleSequence m n) h)) ⁻¹' {r})).toReal = a) :
    HasDensity (residueFiber A r) a := by
  apply (hasDensity_iff_prefixCount_multiples (residueFiber A r) m a).mpr
  apply (tendsto_add_atTop_iff_nat 1).mp
  apply (tendsto_iff_ultrafilter _ _ _).mpr
  intro U hU
  have hd : ∀ᶠ n in U, (h : ℕ) ∣ (positiveMultipleSequence m n : ℕ) :=
    Eventually.of_forall fun n => dvd_mul_of_dvd_left hhm (n + 1)
  have hset : {n : ℕ | n ∈ A ∧ ((n - 0 : ℕ) : ZMod (h : ℕ)) = r} = residueFiber A r := by
    ext n
    constructor
    · rintro ⟨hn, hr⟩
      exact ⟨hn, hA hn, by simpa only [Nat.sub_zero, Finset.mem_singleton] using hr⟩
    · rintro ⟨hn, _, hr⟩
      exact ⟨hn, by simpa only [Nat.sub_zero, Finset.mem_singleton] using hr⟩
  have hp := loeb_window_residue_measure_tendsto U hU (positiveMultipleSequence m) h hd
    (fun _ => A) (fun _ => 0) r
  rw [hall U hU] at hp
  simp only [hset, cyclicWindow_card_eq_prefixCount, tailShift, add_zero, setOf_mem_eq] at hp
  exact hp

end Erdos335.Loeb

end
