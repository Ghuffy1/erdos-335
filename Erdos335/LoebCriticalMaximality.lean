import Erdos335.LoebCriticalSolidity
import Erdos335.LoebSolidAbsorption

/-!
# Maximality of strict critical pairs

For a strict critical pair, a translate of one input lies almost
everywhere in the sum exactly when the translation parameter lies in
the saturation of the other input. The forward implication below is
the maximality assertion of Griesmer's Lemma 9.6.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Filter Set Topology MeasureTheory
open scoped ENNReal Pointwise

noncomputable section

namespace Erdos335.Loeb

local instance maximalityLoebSpace (U : Ultrafilter ℕ) (q : ℕ → ℕ+) :
    MeasurableSpace ((U : Filter ℕ).Product (fun n => ZMod (q n : ℕ))) := loebMeasurableSpace U

theorem loeb_critical_translate_maximal
    (U : Ultrafilter ℕ) (hU : (U : Filter ℕ) ≤ atTop) (q : ℕ → ℕ+)
    (A B : Set ((U : Filter ℕ).Product (fun n => ZMod (q n : ℕ))))
    (hA : MeasurableSet A) (hB : MeasurableSet B)
    (hApos : 0 < loebMeasure U hU A) (hBpos : 0 < loebMeasure U hU B)
    (hsmall : internalInnerMeasure U hU (A + B) < loebMeasure U hU A + loebMeasure U hU B)
    (g : (U : Filter ℕ).Product (fun n => ZMod (q n : ℕ)))
    (hnull : loebMeasure U hU ((g +ᵥ B) \ (A + B)) = 0) :
    g ∈ A + (AddAction.stabilizer ((U : Filter ℕ).Product (fun n => ZMod (q n : ℕ)))
      (A + B) : Set _) := by
  let G := (U : Filter ℕ).Product (fun n => ZMod (q n : ℕ))
  let μ := loebMeasure (X := fun n => ZMod (q n : ℕ)) U hU
  letI : IsProbabilityMeasure μ := isProbabilityMeasure_loebMeasure U hU
  let H := AddAction.stabilizer G (A + B)
  obtain ⟨hCm, hHm, hHpos, hid⟩ := loeb_measurable_kneser_identity U hU q A B hA hB hApos hBpos hsmall
  have hperiod : (A + B) + (H : Set G) = A + B := by
    apply subset_antisymm
    · rintro x ⟨c, hc, k, hk, rfl⟩
      have hfix : k +ᵥ (A + B) = A + B := hk
      rw [← hfix]
      exact ⟨c, hc, add_comm k c⟩
    · intro x hx
      exact ⟨x, hx, 0, H.zero_mem, add_zero x⟩
  have hsolid := (loeb_critical_coset_masses_positive U hU q A B hA hB hApos hBpos hsmall).2
  have habsorb := loeb_solid_translate_absorption U hU H B (A + B) g hperiod hsolid hnull
  by_contra hg
  let A' := A ∪ (g +ᵥ (H : Set G))
  have hAA' : A ⊆ A' := subset_union_left
  have hA'm : MeasurableSet A' := hA.union (measurable_loeb_coset U hU H hHm g)
  have hA'pos : 0 < μ A' := hApos.trans_le (measure_mono hAA')
  have hC' : A' + B = A + B := by
    apply subset_antisymm
    · rintro x ⟨a, ha, b, hb, rfl⟩
      rcases ha with ha | ha
      · exact ⟨a, ha, b, hb, rfl⟩
      · obtain ⟨k, hk, rfl⟩ := ha
        apply habsorb
        exact ⟨b + k, ⟨b, hb, k, hk, rfl⟩, by simp [vadd_eq_add]; abel⟩
    · exact add_subset_add hAA' (show B ⊆ B from Subset.rfl)
  have hsmall' : internalInnerMeasure U hU (A' + B) < μ A' + μ B := by
    rw [hC']
    exact hsmall.trans_le (add_le_add (measure_mono hAA') le_rfl)
  have hid' := (loeb_measurable_kneser_identity U hU q A' B hA'm hB hA'pos hBpos hsmall').2.2.2
  rw [hC'] at hid'
  change μ (A' + (H : Set G)) + μ (B + (H : Set G)) = μ (A + B) + μ (H : Set G) at hid'
  have hsaturation : A' + (H : Set G) = (A + (H : Set G)) ∪ (g +ᵥ (H : Set G)) := by
    apply subset_antisymm
    · rintro x ⟨a, ha, k, hk, rfl⟩
      rcases ha with ha | ha
      · exact Or.inl ⟨a, ha, k, hk, rfl⟩
      · obtain ⟨l, hl, rfl⟩ := ha
        exact Or.inr ⟨l + k, H.add_mem hl hk, by simp [vadd_eq_add, add_assoc]⟩
    · rintro x (hx | hx)
      · exact add_subset_add hAA' (show (H : Set G) ⊆ H from Subset.rfl) hx
      · exact ⟨x, Or.inr hx, 0, H.zero_mem, add_zero x⟩
  have hdisjoint : Disjoint (A + (H : Set G)) (g +ᵥ (H : Set G)) := by
    apply Set.disjoint_left.mpr
    rintro x ⟨a, ha, k, hk, heqa⟩ ⟨l, hl, heqg⟩
    apply hg
    refine ⟨a, ha, k - l, H.sub_mem hk hl, ?_⟩
    change a + k = x at heqa
    change g + l = x at heqg
    calc
      a + (k - l) = (a + k) - l := by abel
      _ = x - l := by rw [heqa]
      _ = g := by rw [← heqg]; simp
  have hmass : μ (A' + (H : Set G)) = μ (A + (H : Set G)) + μ (H : Set G) := by
    rw [hsaturation, measure_union hdisjoint (measurable_loeb_coset U hU H hHm g), loebMeasure_coset]
  have hdup : μ (H : Set G) + (μ (A + (H : Set G)) + μ (B + (H : Set G))) =
      0 + (μ (A + (H : Set G)) + μ (B + (H : Set G))) := by
    calc
      _ = (μ (A + (H : Set G)) + μ (H : Set G)) + μ (B + (H : Set G)) := by ac_rfl
      _ = μ (A' + (H : Set G)) + μ (B + (H : Set G)) := by rw [hmass]
      _ = μ (A + B) + μ (H : Set G) := hid'
      _ = 0 + (μ (A + (H : Set G)) + μ (B + (H : Set G))) := by rw [zero_add, hid]
  have hz : μ (H : Set G) ≤ 0 :=
    (ENNReal.add_le_add_iff_right (by finiteness)).mp hdup.le
  exact (not_le_of_gt hHpos) hz

end Erdos335.Loeb

end
