import Erdos335.LoebEqualityPeriod

/-!
# Sums of essentially periodic inputs

If both inputs fill their occupied cosets up to null sets, their literal
sum equals the sum of the saturated inputs. Positive coset measure and
the coset pigeonhole theorem give the literal equality.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Filter Set Topology MeasureTheory
open scoped ENNReal Pointwise

noncomputable section

namespace Erdos335.Loeb

variable {X : ℕ → Type*} [∀ n, AddCommGroup (X n)] [∀ n, Fintype (X n)]

local instance fullSaturationsLoebSpace (U : Ultrafilter ℕ) :
    MeasurableSpace ((U : Filter ℕ).Product X) := loebMeasurableSpace U

theorem loeb_measure_saturation_eq_of_essential_period
    (U : Ultrafilter ℕ) (hU : (U : Filter ℕ) ≤ atTop)
    (H : AddSubgroup ((U : Filter ℕ).Product X))
    (A : Set ((U : Filter ℕ).Product X)) (hAm : MeasurableSet A)
    (hperiod : loebMeasure U hU ((A + (H : Set ((U : Filter ℕ).Product X))) \ A) = 0) :
    loebMeasure U hU (A + (H : Set ((U : Filter ℕ).Product X))) = loebMeasure U hU A := by
  have hsub : A ⊆ A + (H : Set ((U : Filter ℕ).Product X)) := by
    intro a ha
    exact ⟨a, ha, 0, H.zero_mem, add_zero a⟩
  have hsplit := measure_inter_add_sdiff (μ := loebMeasure U hU)
    (A + (H : Set ((U : Filter ℕ).Product X))) hAm
  rw [inter_eq_right.mpr hsub, hperiod, add_zero] at hsplit
  exact hsplit.symm

theorem loeb_add_eq_add_saturations_of_essential_periods
    (U : Ultrafilter ℕ) (hU : (U : Filter ℕ) ≤ atTop)
    (H : AddSubgroup ((U : Filter ℕ).Product X))
    (A B : Set ((U : Filter ℕ).Product X))
    (hHm : MeasurableSet (H : Set ((U : Filter ℕ).Product X)))
    (hHpos : 0 < loebMeasure U hU (H : Set ((U : Filter ℕ).Product X)))
    (hAm : MeasurableSet A) (hBm : MeasurableSet B)
    (hAperiod : loebMeasure U hU ((A + (H : Set ((U : Filter ℕ).Product X))) \ A) = 0)
    (hBperiod : loebMeasure U hU ((B + (H : Set ((U : Filter ℕ).Product X))) \ B) = 0) :
    A + B = (A + (H : Set ((U : Filter ℕ).Product X))) +
      (B + (H : Set ((U : Filter ℕ).Product X))) := by
  let G := (U : Filter ℕ).Product X
  let μ := loebMeasure (X := X) U hU
  letI : IsProbabilityMeasure μ := isProbabilityMeasure_loebMeasure U hU
  have hAmass := loeb_measure_saturation_eq_of_essential_period U hU H A hAm hAperiod
  have hBmass := loeb_measure_saturation_eq_of_essential_period U hU H B hBm hBperiod
  have hdeficit : μ (A + (H : Set G)) + μ (B + (H : Set G)) <
      μ A + μ B + μ (H : Set G) := by
    rw [hAmass, hBmass]
    exact ENNReal.lt_add_right (by finiteness) hHpos.ne'
  have hperiod := loeb_add_periodic_of_saturated_deficit U hU H hHm A B hBm hdeficit
  apply subset_antisymm
  · rintro x ⟨a, ha, b, hb, rfl⟩
    exact ⟨a, ⟨a, ha, 0, H.zero_mem, add_zero a⟩,
      b, ⟨b, hb, 0, H.zero_mem, add_zero b⟩, rfl⟩
  · rintro x ⟨a', ⟨a, ha, k, hk, hka⟩, b', ⟨b, hb, l, hl, hlb⟩, rfl⟩
    rw [← hperiod]
    refine ⟨a + b, add_mem_add ha hb, k + l, H.add_mem hk hl, ?_⟩
    change a + k = a' at hka
    change b + l = b' at hlb
    rw [← hka, ← hlb]
    abel

end Erdos335.Loeb

end
