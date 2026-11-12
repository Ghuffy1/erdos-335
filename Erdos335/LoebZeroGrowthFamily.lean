import Erdos335.LoebZeroGrowth

/-!
# The zero-growth components of a critical finite partition
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Filter Set MeasureTheory
open scoped Pointwise ENNReal BigOperators

noncomputable section

namespace Erdos335.Loeb

theorem finite_growth_concentrates
    {I : Type*} [Fintype I] (f g : I → ℝ) (a : ℝ)
    (hmono : ∀ i, g i ≤ f i) (hsum : ∑ i, f i = a + ∑ i, g i)
    (i : I) (hi : a + g i ≤ f i) :
    ∀ j, j ≠ i → f j = g j := by
  classical
  let d (k : I) := f k - g k
  have hnonneg (k : I) : 0 ≤ d k := sub_nonneg.mpr (hmono k)
  have hdsum : ∑ k, d k = a := by
    simp only [d, Finset.sum_sub_distrib]
    linarith
  intro j hji
  have hpair : d i + d j ≤ ∑ k, d k := by
    calc
      d i + d j = ∑ k ∈ ({i, j} : Finset I), d k := by simp [Ne.symm hji]
      _ ≤ ∑ k ∈ (Finset.univ : Finset I), d k :=
        Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _) (fun k _ _ => hnonneg k)
      _ = ∑ k, d k := by simp
  rw [hdsum] at hpair
  have hj := hnonneg j
  dsimp only [d] at hpair hj
  linarith

local instance zeroGrowthFamilyLoebSpace (U : Ultrafilter ℕ) (q : ℕ → ℕ+) :
    MeasurableSpace ((U : Filter ℕ).Product (fun n => ZMod (q n : ℕ))) := loebMeasurableSpace U

theorem loeb_zero_growth_family_periodic
    (U : Ultrafilter ℕ) (hU : (U : Filter ℕ) ≤ atTop) (q : ℕ → ℕ+)
    {I : Type*} [Fintype I]
    (A : Set ((U : Filter ℕ).Product (fun n => ZMod (q n : ℕ))))
    (B : I → Set ((U : Filter ℕ).Product (fun n => ZMod (q n : ℕ))))
    (hAm : MeasurableSet A) (hBm : ∀ i, MeasurableSet (B i))
    (hSm : ∀ i, MeasurableSet (A + B i))
    (hApos : 0 < loebMeasure U hU A) (hzero : 0 ∈ A) (hBne : ∀ i, (B i).Nonempty)
    (hcount : ∑ i, loebMeasure U hU (A + B i) = loebMeasure U hU A + ∑ i, loebMeasure U hU (B i))
    (i : I) (hi : loebMeasure U hU A + loebMeasure U hU (B i) ≤ loebMeasure U hU (A + B i)) :
    ∀ j, j ≠ i → loebMeasure U hU ((B j + (AddSubgroup.closure A : Set _)) \ B j) = 0 := by
  classical
  let μ := loebMeasure (X := fun n => ZMod (q n : ℕ)) U hU
  have : IsProbabilityMeasure μ := isProbabilityMeasure_loebMeasure U hU
  have hsub (j : I) : B j ⊆ A + B j := fun x hx => ⟨0, hzero, x, hx, zero_add x⟩
  have hmono (j : I) : (μ (B j)).toReal ≤ (μ (A + B j)).toReal :=
    ENNReal.toReal_mono (measure_ne_top μ _) (measure_mono (hsub j))
  have hcountR := congrArg ENNReal.toReal hcount
  rw [ENNReal.toReal_sum (fun j _ => measure_ne_top μ _),
    ENNReal.toReal_add (measure_ne_top μ _) (ENNReal.sum_ne_top.mpr (fun j _ => measure_ne_top μ _)),
    ENNReal.toReal_sum (fun j _ => measure_ne_top μ _)] at hcountR
  have hiR := ENNReal.toReal_mono (measure_ne_top μ _) hi
  rw [ENNReal.toReal_add (measure_ne_top μ _) (measure_ne_top μ _)] at hiR
  have hconcentrate := finite_growth_concentrates (fun j => (μ (A + B j)).toReal)
    (fun j => (μ (B j)).toReal) (μ A).toReal hmono hcountR i hiR
  intro j hji
  have hmass : μ (A + B j) = μ (B j) := by
    apply le_antisymm
    · exact (ENNReal.toReal_le_toReal (measure_ne_top μ _) (measure_ne_top μ _)).mp (hconcentrate j hji).le
    · exact measure_mono (hsub j)
  have hinner : internalInnerMeasure U hU (A + B j) = μ (B j) :=
    (internalInnerMeasure_eq U hU _ (hSm j)).trans hmass
  exact (loeb_zero_growth_generated_period U hU q A (B j) hAm (hBm j) hApos (hBne j) hzero hinner).2.2

end Erdos335.Loeb

end
