import Erdos335.LoebOneCosetReduction
import Erdos335.LoebQuasiPeriodicInput

/-!
# Recovering a pair that exceeds one containing coset

If the first input occupies one coset and the sum has measure greater
than that coset, the second input's quasi-periodic background has
positive measure. Pair recovery then applies with the inputs exchanged.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Filter Set MeasureTheory
open scoped Pointwise ENNReal

noncomputable section

namespace Erdos335.Loeb

local instance oneCosetPairLoebSpace (U : Ultrafilter ℕ) (q : ℕ → ℕ+) :
    MeasurableSpace ((U : Filter ℕ).Product (fun n => ZMod (q n : ℕ))) := loebMeasurableSpace U

theorem loeb_quasiPeriodic_pair_of_one_coset_and_large_sum
    (U : Ultrafilter ℕ) (hU : (U : Filter ℕ) ≤ atTop) (q : ℕ → ℕ+)
    (A B : Set ((U : Filter ℕ).Product (fun n => ZMod (q n : ℕ))))
    (H : AddSubgroup ((U : Filter ℕ).Product (fun n => ZMod (q n : ℕ))))
    (hHm : MeasurableSet (H : Set ((U : Filter ℕ).Product (fun n => ZMod (q n : ℕ)))))
    (a : (U : Filter ℕ).Product (fun n => ZMod (q n : ℕ)))
    (hAcoset : A ⊆ a +ᵥ (H : Set _))
    (hAm : MeasurableSet A) (hBm : MeasurableSet B) (hSm : MeasurableSet (A + B))
    (hApos : 0 < loebMeasure U hU A) (hBpos : 0 < loebMeasure U hU B)
    (hlarge : loebMeasure U hU
      (H : Set ((U : Filter ℕ).Product (fun n => ZMod (q n : ℕ)))) < loebMeasure U hU (A + B))
    (hfull : loebMeasure U hU (A + B) = loebMeasure U hU A + loebMeasure U hU B)
    (hirr : MeasureIrreducible (loebMeasure U hU) (internalInnerMeasure U hU) A B)
    (hne : MeasureNonextendible (loebMeasure U hU) (internalInnerMeasure U hU) A B)
    (hnotperiod : ¬ ∃ L : AddSubgroup ((U : Filter ℕ).Product (fun n => ZMod (q n : ℕ))),
      MeasurableSet (L : Set ((U : Filter ℕ).Product (fun n => ZMod (q n : ℕ)))) ∧
      0 < loebMeasure (X := fun n => ZMod (q n : ℕ)) U hU (L : Set _) ∧
      (A + B) + (L : Set _) =ᵐ[loebMeasure U hU] A + B) :
    Nonempty (QuasiPeriodicPairData (loebMeasure U hU) (internalInnerMeasure U hU) A B) := by
  let G := (U : Filter ℕ).Product (fun n => ZMod (q n : ℕ))
  let μ := loebMeasure (X := fun n => ZMod (q n : ℕ)) U hU
  have hnotexact : ¬ ∃ L : AddSubgroup G, MeasurableSet (L : Set G) ∧
      0 < μ (L : Set G) ∧ (A + B) + (L : Set G) = A + B := by
    rintro ⟨L, hLm, hLpos, hperiod⟩
    apply hnotperiod
    refine ⟨L, hLm, hLpos, ?_⟩
    rw [hperiod]
  obtain ⟨K, hKm, hKpos, hKH, ⟨p⟩⟩ := loeb_one_coset_input_reduction U hU q A B H a
    hAcoset hAm hBm hSm hApos hfull hnotexact
  have hBgpos : 0 < μ p.background := by
    by_contra hn
    have hBgzero : μ p.background = 0 := le_antisymm (not_lt.mp hn) bot_le
    have hparts : Disjoint p.background p.active := by
      apply Set.disjoint_left.mpr
      intro x hx hy
      exact Set.disjoint_left.mp p.separated ⟨x, hy, 0, K.zero_mem, add_zero x⟩ hx
    have hBmass : μ p.active = μ B := by
      have h := (congrArg μ p.partition).trans (measure_union hparts p.active_measurable)
      rw [hBgzero, zero_add] at h
      exact h.symm
    have hActsub : p.active ⊆ B := subset_union_right.trans p.partition.ge
    have hsub : A + p.active ⊆ (a + p.anchor) +ᵥ (H : Set G) := by
      rintro z ⟨x, hx, y, hy, rfl⟩
      obtain ⟨h, hh, hhx⟩ := hAcoset hx
      obtain ⟨k, hk, hky⟩ := p.active_subset_coset hy
      refine ⟨h + k, H.add_mem hh (hKH hk), ?_⟩
      change a + h = x at hhx
      change p.anchor + k = y at hky
      change (a + p.anchor) + (h + k) = x + y
      rw [← hhx, ← hky]
      ac_rfl
    have hinner : internalInnerMeasure U hU (A + p.active) = μ (A + B) :=
      (hirr A p.active hAm p.active_measurable Subset.rfl hActsub rfl hBmass).trans
        (internalInnerMeasure_eq U hU _ hSm)
    have hbound : μ (A + B) ≤ μ (H : Set G) := by
      rw [← hinner, ← loebMeasure_coset U hU H (a + p.anchor),
        ← internalInnerMeasure_eq U hU _ (measurable_loeb_coset U hU H hHm _)]
      exact internalInnerMeasure_mono U hU hsub
    exact (not_lt_of_ge hbound) hlarge
  have hnotperiodSwap : ¬ ∃ L : AddSubgroup G, MeasurableSet (L : Set G) ∧
      0 < μ (L : Set G) ∧ (B + A) + (L : Set G) =ᵐ[μ] B + A := by
    simpa only [add_comm B A] using hnotperiod
  obtain ⟨r⟩ := loeb_quasiPeriodic_pair_of_nonnull_background U hU q B A K hKm hKpos p
    hAm (by simpa only [add_comm B A] using hSm) hBgpos hBpos hApos
    (by simpa only [add_comm] using hfull) hirr.swap hne.swap hnotperiodSwap
  exact ⟨r.swap⟩

end Erdos335.Loeb

end
