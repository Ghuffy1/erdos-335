import Erdos335.LoebNullExtensionBackground

/-!
# The unique active coset under a null extension
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Filter Set Topology MeasureTheory
open scoped Pointwise ENNReal

noncomputable section

namespace Erdos335.Loeb

theorem left_coset_of_sum_right_cosets
    {G : Type*} [AddCommGroup G] (H : AddSubgroup G) (a b x y : G)
    (hsum : x + y ∈ (a + b) +ᵥ (H : Set G)) (hy : y ∈ b +ᵥ (H : Set G)) :
    x ∈ a +ᵥ (H : Set G) := by
  obtain ⟨k, hk, hkxy⟩ := hsum
  obtain ⟨l, hl, hly⟩ := hy
  refine ⟨k - l, H.sub_mem hk hl, ?_⟩
  change (a + b) + k = x + y at hkxy
  change b + l = y at hly
  change a + (k - l) = x
  calc
    _ = ((a + b) + k) - (b + l) := by abel
    _ = (x + y) - y := by rw [hkxy, hly]
    _ = x := by simp

local instance nullExtensionUniqueLoebSpace (U : Ultrafilter ℕ) (q : ℕ → ℕ+) :
    MeasurableSpace ((U : Filter ℕ).Product (fun n => ZMod (q n : ℕ))) := loebMeasurableSpace U

theorem loeb_quasiPeriodic_null_extension_unique_expression
    (U : Ultrafilter ℕ) (hU : (U : Filter ℕ) ≤ atTop) (q : ℕ → ℕ+)
    (A B A' B' : Set ((U : Filter ℕ).Product (fun n => ZMod (q n : ℕ))))
    (p : QuasiPeriodicPairData (loebMeasure U hU) (internalInnerMeasure U hU) A B)
    (hAA' : A ⊆ A') (hBB' : B ⊆ B')
    (hBactive : 0 < loebMeasure U hU p.right.active)
    (hne : MeasureNonextendible (loebMeasure U hU) (internalInnerMeasure U hU) A B)
    (hCm : MeasurableSet (A + B))
    (hnotperiod : ¬ (A + B) + (p.period : Set _) =ᵐ[loebMeasure U hU] A + B)
    (hfull : internalInnerMeasure U hU (A' + B') = loebMeasure U hU (A + B)) :
    ∀ x ∈ A', ∀ y ∈ B', x + y ∈ (p.left.anchor + p.right.anchor) +ᵥ
      (p.period : Set ((U : Filter ℕ).Product (fun n => ZMod (q n : ℕ)))) →
      x ∈ p.left.anchor +ᵥ (p.period : Set ((U : Filter ℕ).Product (fun n => ZMod (q n : ℕ)))) ∧
      y ∈ p.right.anchor +ᵥ (p.period : Set ((U : Filter ℕ).Product (fun n => ZMod (q n : ℕ)))) := by
  let G := (U : Filter ℕ).Product (fun n => ZMod (q n : ℕ))
  let μ := loebMeasure (X := fun n => ZMod (q n : ℕ)) U hU
  have hAm : MeasurableSet A := p.left.partition.symm ▸
    (p.left.background_measurable.union p.left.active_measurable)
  have hBm : MeasurableSet B := p.right.partition.symm ▸
    (p.right.background_measurable.union p.right.active_measurable)
  intro x hx y hy hxy
  have hxcoset : x ∈ p.left.anchor +ᵥ (p.period : Set G) := by
    by_contra hxout
    have hyout : y ∉ p.right.anchor +ᵥ (p.period : Set G) :=
      fun hycoset => hxout (left_coset_of_sum_right_cosets p.period _ _ x y hxy hycoset)
    have hnullx := loeb_translation_sdiff_zero_of_full_inner U hU A B A' B' hBm hCm hAA' hBB' hfull x hx
    have hnullCoset := loeb_nonextendible_quasiPeriodic_translate U hU q A B p x hxout
      hBactive hne hnotperiod hnullx
    have hmass : μ ((x +ᵥ (p.period : Set G)) ∩ A) = μ (p.period : Set G) := by
      have h := measure_inter_add_sdiff (μ := μ) (x +ᵥ (p.period : Set G)) hAm
      rw [hnullCoset, add_zero, loebMeasure_coset U hU p.period x] at h
      exact h
    have hpositive : 0 < μ ((x +ᵥ (p.period : Set G)) ∩ A) := by rw [hmass]; exact p.period_positive
    obtain ⟨a, haCoset, haA⟩ := nonempty_of_measure_ne_zero hpositive.ne'
    have hfullSwap : internalInnerMeasure U hU (B' + A') = μ (B + A) := by
      simpa only [add_comm] using hfull
    have hnully := loeb_translation_sdiff_zero_of_full_inner U hU B A B' A' hAm
      (by simpa only [add_comm] using hCm) hBB' hAA' hfullSwap y hy
    have hnotSwap : ¬ (B + A) + (p.swap.period : Set G) =ᵐ[μ] B + A := by
      simpa only [QuasiPeriodicPairData.swap, add_comm A B] using hnotperiod
    have havoid := loeb_quasiPeriodic_translate_avoids_active_coset U hU q B A
      (internalInnerMeasure U hU) p.swap y hyout hnotSwap hnully
    have havoid' : Disjoint (y +ᵥ A) ((p.left.anchor + p.right.anchor) +ᵥ (p.period : Set G)) := by
      simpa only [QuasiPeriodicPairData.swap, add_comm p.right.anchor p.left.anchor] using havoid
    have hya : y + a ∈ (p.left.anchor + p.right.anchor) +ᵥ (p.period : Set G) := by
      obtain ⟨k, hk, hkxy⟩ := hxy
      obtain ⟨l, hl, hla⟩ := haCoset
      refine ⟨k + l, p.period.add_mem hk hl, ?_⟩
      change (p.left.anchor + p.right.anchor) + k = x + y at hkxy
      change x + l = a at hla
      change (p.left.anchor + p.right.anchor) + (k + l) = y + a
      rw [← add_assoc, hkxy, ← hla]
      abel
    exact Set.disjoint_left.mp havoid' ⟨a, haA, rfl⟩ hya
  refine ⟨hxcoset, ?_⟩
  have hsumSwap : y + x ∈ (p.right.anchor + p.left.anchor) +ᵥ (p.period : Set G) := by
    simpa only [add_comm] using hxy
  exact left_coset_of_sum_right_cosets p.period _ _ y x hsumSwap hxcoset

end Erdos335.Loeb

end
