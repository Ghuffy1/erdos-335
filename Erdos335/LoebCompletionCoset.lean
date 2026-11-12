import Erdos335.LoebCriticalMaximality

/-!
# Completion of a pair with a positive stabilizer

For a pair whose sum has measure at most the total input measure, its
completion adds at most one coset of the positive stabilizer. The proof
is the cyclic Loeb version of Griesmer's Lemma 10.11.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Filter Set Topology MeasureTheory
open scoped ENNReal Pointwise

noncomputable section

namespace Erdos335.Loeb

local instance completionCosetLoebSpace (U : Ultrafilter ℕ) (q : ℕ → ℕ+) :
    MeasurableSpace ((U : Filter ℕ).Product (fun n => ZMod (q n : ℕ))) := loebMeasurableSpace U

theorem loeb_completion_at_most_one_coset
    (U : Ultrafilter ℕ) (hU : (U : Filter ℕ) ≤ atTop) (q : ℕ → ℕ+)
    (A B : Set ((U : Filter ℕ).Product (fun n => ZMod (q n : ℕ))))
    (hAm : MeasurableSet A) (hBm : MeasurableSet B) (hCm : MeasurableSet (A + B))
    (hApos : 0 < loebMeasure U hU A) (hBpos : 0 < loebMeasure U hU B)
    (hle : loebMeasure U hU (A + B) ≤ loebMeasure U hU A + loebMeasure U hU B) :
    let G := (U : Filter ℕ).Product (fun n => ZMod (q n : ℕ))
    let H := AddAction.stabilizer G (A + B)
    MeasurableSet (H : Set G) → 0 < loebMeasure U hU (H : Set G) →
      {x | x +ᵥ B ⊆ A + B} = A + (H : Set G) ∨
      ∃ g ∉ A + (H : Set G),
        {x | x +ᵥ B ⊆ A + B} = (A + (H : Set G)) ∪ (g +ᵥ (H : Set G)) := by
  dsimp only
  intro hHm hHpos
  let G := (U : Filter ℕ).Product (fun n => ZMod (q n : ℕ))
  let μ := loebMeasure (X := fun n => ZMod (q n : ℕ)) U hU
  letI : IsProbabilityMeasure μ := isProbabilityMeasure_loebMeasure U hU
  let H := AddAction.stabilizer G (A + B)
  let E : Set G := {x | x +ᵥ B ⊆ A + B}
  have hperiod : (A + B) + (H : Set G) = A + B := by
    apply subset_antisymm
    · rintro x ⟨c, hc, k, hk, rfl⟩
      have hfix : k +ᵥ (A + B) = A + B := hk
      rw [← hfix]
      exact ⟨c, hc, add_comm k c⟩
    · intro x hx
      exact ⟨x, hx, 0, H.zero_mem, add_zero x⟩
  have hinside : A + (H : Set G) ⊆ E := by
    rintro x ⟨a, ha, k, hk, rfl⟩ z ⟨b, hb, rfl⟩
    rw [← hperiod]
    exact ⟨a + b, add_mem_add ha hb, k, hk, by simp only [vadd_eq_add]; abel⟩
  by_cases hE : E ⊆ A + (H : Set G)
  · exact Or.inl (subset_antisymm hE hinside)
  · obtain ⟨g, hg, hgout⟩ := Set.not_subset.mp hE
    right
    refine ⟨g, hgout, ?_⟩
    let A' := A ∪ (g +ᵥ (H : Set G))
    have hAA' : A ⊆ A' := subset_union_left
    have hA'm : MeasurableSet A' := hAm.union (measurable_loeb_coset U hU H hHm g)
    have hAsat : A' + (H : Set G) = (A + (H : Set G)) ∪ (g +ᵥ (H : Set G)) := by
      apply subset_antisymm
      · rintro x ⟨y, hy, k, hk, rfl⟩
        rcases hy with hy | hy
        · exact Or.inl ⟨y, hy, k, hk, rfl⟩
        · obtain ⟨l, hl, rfl⟩ := hy
          exact Or.inr ⟨l + k, H.add_mem hl hk, by simp [vadd_eq_add, add_assoc]⟩
      · rintro x (hx | hx)
        · exact add_subset_add hAA' (show (H : Set G) ⊆ H from Subset.rfl) hx
        · exact ⟨x, Or.inr hx, 0, H.zero_mem, add_zero x⟩
    have hginside : g +ᵥ (H : Set G) ⊆ E := by
      rintro x ⟨k, hk, rfl⟩ z ⟨b, hb, rfl⟩
      rw [← hperiod]
      have hgb : g + b ∈ A + B := hg ⟨b, hb, rfl⟩
      exact ⟨g + b, hgb, k, hk, by simp only [vadd_eq_add]; abel⟩
    have hC' : A' + B = A + B := by
      apply subset_antisymm
      · rintro z ⟨x, hx, b, hb, rfl⟩
        rcases hx with hx | hx
        · exact add_mem_add hx hb
        · exact hginside hx ⟨b, hb, rfl⟩
      · exact add_subset_add hAA' (show B ⊆ B from Subset.rfl)
    have hdisj : Disjoint A (g +ᵥ (H : Set G)) := by
      apply Set.disjoint_left.mpr
      rintro x hx ⟨k, hk, hkx⟩
      apply hgout
      refine ⟨x, hx, -k, H.neg_mem hk, ?_⟩
      change g + k = x at hkx
      rw [← hkx]
      simp
    have hmass : μ A' = μ A + μ (H : Set G) := by
      rw [show A' = A ∪ (g +ᵥ (H : Set G)) from rfl,
        measure_union hdisj (measurable_loeb_coset U hU H hHm g), loebMeasure_coset]
    have hinc : μ A + μ B < μ A' + μ B := by
      rw [hmass]
      calc
        μ A + μ B < (μ A + μ B) + μ (H : Set G) :=
          ENNReal.lt_add_right (by finiteness) hHpos.ne'
        _ = (μ A + μ (H : Set G)) + μ B := by ac_rfl
    have hsmall : internalInnerMeasure U hU (A' + B) < μ A' + μ B := by
      rw [hC', internalInnerMeasure_eq U hU (A + B) hCm]
      exact hle.trans_lt hinc
    have hA'pos : 0 < μ A' := hApos.trans_le (measure_mono hAA')
    apply subset_antisymm
    · intro x hx
      have hzero : μ ((x +ᵥ B) \ (A' + B)) = 0 := by
        rw [hC', sdiff_eq_empty.mpr hx, measure_empty]
      have hmem := loeb_critical_translate_maximal U hU q A' B hA'm hBm hA'pos hBpos hsmall x hzero
      rw [hC'] at hmem
      change x ∈ A' + (H : Set G) at hmem
      rwa [hAsat] at hmem
    · exact union_subset hinside hginside

end Erdos335.Loeb

end
