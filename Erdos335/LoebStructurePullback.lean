import Erdos335.QuasiPeriodicPullback

/-!
# Compact structure under the Loeb quotient map

Measurable active sums give exact inner measures after pullback. Essential
sumset periods pull back along the same surjective homomorphism.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Filter Set MeasureTheory
open scoped Pointwise ENNReal

noncomputable section

namespace Erdos335.Loeb

variable {X : ℕ → Type*} [∀ n, AddCommGroup (X n)] [∀ n, Fintype (X n)]

local instance structurePullbackLoebSpace (U : Ultrafilter ℕ) :
    MeasurableSpace ((U : Filter ℕ).Product X) := loebMeasurableSpace U

theorem loeb_quasiPeriodic_comap
    (U : Ultrafilter ℕ) (hU : (U : Filter ℕ) ≤ atTop)
    {K : Type*} [AddCommGroup K] [MeasurableSpace K]
    (φ : (U : Filter ℕ).Product X →+ K) (hφ : Measurable φ)
    (hsurj : Function.Surjective φ) (C D : Set K)
    (p : QuasiPeriodicPairData (Measure.map φ (loebMeasure U hU))
      (Measure.map φ (loebMeasure U hU)) C D)
    (hactive : MeasurableSet (p.left.active + p.right.active)) :
    ∃ r : QuasiPeriodicPairData (loebMeasure U hU) (internalInnerMeasure U hU)
        (φ ⁻¹' C) (φ ⁻¹' D),
      r.period = p.period.comap φ ∧
      r.left.active = φ ⁻¹' p.left.active ∧
      r.right.active = φ ⁻¹' p.right.active := by
  apply exists_quasiPeriodicPairData_comap φ hφ hsurj (internalInnerMeasure U hU) p
  rw [internalInnerMeasure_eq U hU _ (hactive.preimage hφ),
    Measure.map_apply hφ hactive]

theorem essential_sum_period_comap
    {G K : Type*} [AddCommGroup G] [AddCommGroup K]
    [MeasurableSpace G] [MeasurableSpace K]
    (μ : Measure G) (φ : G →+ K) (hφ : Measurable φ)
    (hsurj : Function.Surjective φ) (C D : Set K) (H : AddSubgroup K)
    (hperiod : (C + D) + (H : Set K) =ᵐ[Measure.map φ μ] C + D) :
    ((φ ⁻¹' C) + (φ ⁻¹' D)) + (H.comap φ : Set G) =ᵐ[μ]
      (φ ⁻¹' C) + (φ ⁻¹' D) := by
  have h := ae_of_ae_map hφ.aemeasurable hperiod
  change (φ ⁻¹' ((C + D) + (H : Set K))) =ᵐ[μ] φ ⁻¹' (C + D) at h
  rw [preimage_add_of_surjective_addHom φ hsurj,
    preimage_add_of_surjective_addHom φ hsurj C D] at h
  exact h

end Erdos335.Loeb

end
