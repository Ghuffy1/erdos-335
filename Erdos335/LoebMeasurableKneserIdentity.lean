import Erdos335.LoebMeasurableKneser

/-!
# The exact Kneser identity for measurable cyclic Loeb pairs

After finding one positive natural period, the two saturated summands are
internal. The internal critical identity then gives the formula for the
literal stabilizer of the original sumset.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Filter Set Topology MeasureTheory
open scoped ENNReal Pointwise

noncomputable section

namespace Erdos335.Loeb

local instance identityLoebSpace (U : Ultrafilter ℕ) (q : ℕ → ℕ+) :
    MeasurableSpace ((U : Filter ℕ).Product (fun n => ZMod (q n : ℕ))) := loebMeasurableSpace U

theorem loeb_measurable_kneser_identity
    (U : Ultrafilter ℕ) (hU : (U : Filter ℕ) ≤ atTop) (q : ℕ → ℕ+)
    (A B : Set ((U : Filter ℕ).Product (fun n => ZMod (q n : ℕ))))
    (hA : MeasurableSet A) (hB : MeasurableSet B)
    (hApos : 0 < loebMeasure U hU A) (hBpos : 0 < loebMeasure U hU B)
    (hsmall : internalInnerMeasure U hU (A + B) < loebMeasure U hU A + loebMeasure U hU B) :
    let G := (U : Filter ℕ).Product (fun n => ZMod (q n : ℕ))
    let K := AddAction.stabilizer G (A + B)
    MeasurableSet (A + B) ∧ MeasurableSet (K : Set G) ∧
      0 < loebMeasure U hU (K : Set G) ∧
      loebMeasure U hU (A + (K : Set G)) + loebMeasure U hU (B + (K : Set G)) =
        loebMeasure U hU (A + B) + loebMeasure U hU (K : Set G) := by
  let G := (U : Filter ℕ).Product (fun n => ZMod (q n : ℕ))
  let μ := loebMeasure (X := fun n => ZMod (q n : ℕ)) U hU
  letI : IsProbabilityMeasure μ := isProbabilityMeasure_loebMeasure U hU
  let K := AddAction.stabilizer G (A + B)
  obtain ⟨h, _, hHpos, hperiod⟩ := loeb_measurable_subcritical_period U hU q A B hA hB hApos hBpos hsmall
  let H := naturalCyclicKernel U q h
  have hHH : (H : Set G) + (H : Set G) = H := by
    apply subset_antisymm
    · rintro x ⟨y, hy, z, hz, rfl⟩
      exact H.add_mem hy hz
    · intro x hx
      exact ⟨x, hx, 0, H.zero_mem, add_zero x⟩
  have hAH : (A + (H : Set G)) + (H : Set G) = A + (H : Set G) := by rw [add_assoc, hHH]
  have hBH : (B + (H : Set G)) + (H : Set G) = B + (H : Set G) := by rw [add_assoc, hHH]
  obtain ⟨A', hA'⟩ := exists_internalSet_of_natural_kernel_period U q h (A + (H : Set G)) hAH
  obtain ⟨B', hB'⟩ := exists_internalSet_of_natural_kernel_period U q h (B + (H : Set G)) hBH
  have hsum : internalSet U (fun n => A' n + B' n) = A + B := by
    rw [internalSet_add, hA', hB']
    calc
      (A + (H : Set G)) + (B + (H : Set G)) = (A + B) + ((H : Set G) + (H : Set G)) := by ac_rfl
      _ = A + B := by rw [hHH]; exact hperiod
  have hCm : MeasurableSet (A + B) := by rw [← hsum]; exact measurable_internalSet U _
  have hsmall' : μ (A + B) < μ A + μ B := by
    rwa [internalInnerMeasure_eq U hU (A + B) hCm] at hsmall
  have hAA' : A ⊆ internalSet U A' := by
    rw [hA']
    intro x hx
    exact ⟨x, hx, 0, H.zero_mem, add_zero x⟩
  have hBB' : B ⊆ internalSet U B' := by
    rw [hB']
    intro x hx
    exact ⟨x, hx, 0, H.zero_mem, add_zero x⟩
  have hA'ne : (internalSet U A').Nonempty := (nonempty_of_measure_ne_zero hApos.ne').mono hAA'
  have hB'ne : (internalSet U B').Nonempty := (nonempty_of_measure_ne_zero hBpos.ne').mono hBB'
  have hcrit : μ (internalSet U (fun n => A' n + B' n)) <
      μ (internalSet U A') + μ (internalSet U B') := by
    rw [hsum]
    exact hsmall'.trans_le (add_le_add (measure_mono hAA') (measure_mono hBB'))
  have hKeq : internalAddSubgroup U (fun n => AddAction.stabilizer (ZMod (q n : ℕ)) (A' n + B' n)) = K := by
    rw [internalAddSubgroup_stabilizer, hsum]
  have hKpos : 0 < μ (K : Set G) := by
    have hp := subcritical_stabilizer_positive U hU A' B' hA'ne hB'ne hcrit
    rwa [hsum] at hp
  have hKm : MeasurableSet (K : Set G) := by
    rw [← hKeq]
    exact measurable_internalSet U _
  have hHK : H ≤ K := by
    intro k hk
    change k +ᵥ (A + B) = A + B
    apply subset_antisymm
    · rintro z ⟨c, hc, rfl⟩
      have hm : k + c ∈ (A + B) + (H : Set G) := ⟨c, hc, k, hk, add_comm _ _⟩
      rwa [hperiod] at hm
    · intro z hz
      have hm : z - k ∈ (A + B) + (H : Set G) := ⟨z, hz, -k, H.neg_mem hk, by abel⟩
      rw [hperiod] at hm
      exact ⟨z - k, hm, by simp⟩
  have hHKset : (H : Set G) + (K : Set G) = K := by
    apply subset_antisymm
    · rintro x ⟨y, hy, z, hz, rfl⟩
      exact K.add_mem (hHK hy) hz
    · intro x hx
      exact ⟨0, H.zero_mem, x, hx, zero_add x⟩
  have hid := loebMeasure_critical_identity U hU A' B' hA'ne hB'ne hcrit
  dsimp only at hid
  rw [hKeq, hA', hB', hsum, add_assoc, hHKset, add_assoc, hHKset] at hid
  exact ⟨hCm, hKm, hKpos, hid⟩

end Erdos335.Loeb

end
