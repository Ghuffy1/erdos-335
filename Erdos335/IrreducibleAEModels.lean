import Erdos335.LoebIrreducibleCore

/-!
# Transferring irreducibility through almost-everywhere input models
-/

set_option autoImplicit false

open Filter Set MeasureTheory
open scoped Pointwise ENNReal

namespace Erdos335.Loeb

theorem MeasureIrreducible.of_ae_pair
    {G : Type*} [AddCommGroup G] [MeasurableSpace G]
    {μ : Measure G} {inner : Set G → ℝ≥0∞} (hmono : Monotone inner)
    {A B P Q : Set G} (hirr : MeasureIrreducible μ inner A B)
    (hAm : MeasurableSet A) (hBm : MeasurableSet B)
    (hAP : A =ᵐ[μ] P) (hBQ : B =ᵐ[μ] Q)
    (hinner : inner (P + Q) = inner (A + B)) :
    MeasureIrreducible μ inner P Q := by
  intro R S hRm hSm hRP hSQ hRmass hSmass
  have hRA : A ∩ R =ᵐ[μ] R := by
    filter_upwards [hAP] with x hx
    apply propext
    constructor
    · exact fun h => h.2
    · intro hr
      exact ⟨hx.mpr (hRP hr), hr⟩
  have hSB : B ∩ S =ᵐ[μ] S := by
    filter_upwards [hBQ] with x hx
    apply propext
    constructor
    · exact fun h => h.2
    · intro hs
      exact ⟨hx.mpr (hSQ hs), hs⟩
  have hRAmass : μ (A ∩ R) = μ A :=
    (measure_congr hRA).trans (hRmass.trans (measure_congr hAP).symm)
  have hSBmass : μ (B ∩ S) = μ B :=
    (measure_congr hSB).trans (hSmass.trans (measure_congr hBQ).symm)
  have hcore := hirr (A ∩ R) (B ∩ S) (hAm.inter hRm) (hBm.inter hSm)
    inter_subset_left inter_subset_left hRAmass hSBmass
  apply le_antisymm (hmono (add_subset_add hRP hSQ))
  rw [hinner, ← hcore]
  exact hmono (add_subset_add inter_subset_right inter_subset_right)

end Erdos335.Loeb
