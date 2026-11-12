import Erdos335.LoebBoundedPeriods
import Erdos335.LoebInnerMeasure

/-!
# Periodicity from a strict inner-measure deficit

Finite enlargements of two fixed internal subsets have a uniformly
bounded natural period. Testing all finite subsets of the original
summands then gives an exact period of their entire sumset.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Filter Set Topology MeasureTheory
open scoped ENNReal Pointwise

noncomputable section

namespace Erdos335.Loeb

theorem exists_natural_period_of_internal_lower_bounds
    (U : Ultrafilter ℕ) (hU : (U : Filter ℕ) ≤ atTop) (q : ℕ → ℕ+)
    (A B : Set ((U : Filter ℕ).Product (fun n => ZMod (q n : ℕ))))
    (A₀ B₀ : ∀ n, Set (ZMod (q n : ℕ)))
    (hA₀ : internalSet U A₀ ⊆ A) (hB₀ : internalSet U B₀ ⊆ B)
    (hA₀ne : (internalSet U A₀).Nonempty) (hB₀ne : (internalSet U B₀).Nonempty)
    (hgap : (internalInnerMeasure U hU (A + B)).toReal <
      (loebMeasure U hU (internalSet U A₀)).toReal +
      (loebMeasure U hU (internalSet U B₀)).toReal) :
    ∃ h : ℕ+,
      MeasurableSet[loebMeasurableSpace U]
        (naturalCyclicKernel U q h : Set ((U : Filter ℕ).Product (fun n => ZMod (q n : ℕ)))) ∧
      0 < loebMeasure U hU (naturalCyclicKernel U q h :
        Set ((U : Filter ℕ).Product (fun n => ZMod (q n : ℕ)))) ∧
      A + B + (naturalCyclicKernel U q h : Set _) = A + B := by
  let G := (U : Filter ℕ).Product (fun n => ZMod (q n : ℕ))
  letI : MeasurableSpace G := loebMeasurableSpace U
  let μ := loebMeasure (X := fun n => ZMod (q n : ℕ)) U hU
  letI : IsProbabilityMeasure μ := isProbabilityMeasure_loebMeasure U hU
  let γ := (internalInnerMeasure U hU (A + B)).toReal
  let δ := (μ (internalSet U A₀)).toReal + (μ (internalSet U B₀)).toReal - γ
  have hδ : 0 < δ := sub_pos.mpr hgap
  obtain ⟨D, hD⟩ := exists_uniform_natural_period_bound U hU q δ hδ
  let K (i : Fin (D + 1)) : AddSubgroup G := naturalCyclicKernel U q ⟨i.val + 1, Nat.succ_pos _⟩
  have htest : ∀ S T : Finset G, (↑S : Set G) ⊆ A → (↑T : Set G) ⊆ B →
      ∃ i, ∀ a ∈ S, ∀ b ∈ T, ∀ k ∈ K i, a + b + k ∈ A + B := by
    intro S T hSA hTB
    obtain ⟨A', hA'eq⟩ := exists_internalSet_finite_augmentation U A₀ (S : Set G) S.finite_toSet
    obtain ⟨B', hB'eq⟩ := exists_internalSet_finite_augmentation U B₀ (T : Set G) T.finite_toSet
    have hA'sub : internalSet U A' ⊆ A := by rw [hA'eq]; exact union_subset hA₀ hSA
    have hB'sub : internalSet U B' ⊆ B := by rw [hB'eq]; exact union_subset hB₀ hTB
    have hA₀A' : internalSet U A₀ ⊆ internalSet U A' := by rw [hA'eq]; exact subset_union_left
    have hB₀B' : internalSet U B₀ ⊆ internalSet U B' := by rw [hB'eq]; exact subset_union_left
    have hsumsub : internalSet U (fun n => A' n + B' n) ⊆ A + B := by
      rw [internalSet_add]
      exact add_subset_add hA'sub hB'sub
    have hinnerfin : internalInnerMeasure U hU (A + B) ≠ ∞ :=
      ne_top_of_le_ne_top (measure_ne_top μ _) (internalInnerMeasure_le U hU (A + B))
    have hsumle : (μ (internalSet U (fun n => A' n + B' n))).toReal ≤ γ := by
      have hi := ultraCount_le_internalInnerMeasure U hU (fun n => A' n + B' n) (A + B) hsumsub
      rw [← loebMeasure_internal U hU] at hi
      exact ENNReal.toReal_mono hinnerfin hi
    have hAle := ENNReal.toReal_mono (measure_ne_top μ _) (measure_mono hA₀A')
    have hBle := ENNReal.toReal_mono (measure_ne_top μ _) (measure_mono hB₀B')
    have haugGap : δ ≤ (μ (internalSet U A')).toReal + (μ (internalSet U B')).toReal -
        (μ (internalSet U (fun n => A' n + B' n))).toReal := by
      dsimp only [δ]
      linarith
    obtain ⟨h, hDh, hperiod⟩ := hD A' B' (hA₀ne.mono hA₀A') (hB₀ne.mono hB₀B') haugGap
    let i : Fin (D + 1) := ⟨(h : ℕ) - 1, by have := h.pos; omega⟩
    have hi : (⟨i.val + 1, Nat.succ_pos _⟩ : ℕ+) = h := by
      apply Subtype.ext
      change (h : ℕ) - 1 + 1 = (h : ℕ)
      exact Nat.sub_add_cancel (Nat.succ_le_of_lt h.pos)
    refine ⟨i, ?_⟩
    intro a ha b hb k hk
    change k ∈ naturalCyclicKernel U q ⟨i.val + 1, Nat.succ_pos _⟩ at hk
    rw [hi] at hk
    apply hsumsub
    apply hperiod (a + b) _ k hk
    rw [internalSet_add]
    refine ⟨a, ?_, b, ?_, rfl⟩
    · rw [hA'eq]; exact Or.inr ha
    · rw [hB'eq]; exact Or.inr hb
  obtain ⟨i, hi⟩ := exists_common_period_of_finite_tests A B K htest
  exact ⟨⟨i.val + 1, Nat.succ_pos _⟩, measurable_naturalCyclicKernel U q _,
    naturalCyclicKernel_measure_pos U hU q _, hi⟩

end Erdos335.Loeb

end
