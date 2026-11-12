import Erdos335.LoebCompactQuotientPair
import Erdos335.LoebAEModelStructure
import Erdos335.LoebCompactConnectedCosets

/-!
# Reduction of an aperiodic compact quotient to connected cosets
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Filter Set MeasureTheory
open scoped Pointwise ENNReal

noncomputable section

namespace Erdos335.Loeb

local instance quotientConnectedReductionLoebSpace (U : Ultrafilter ℕ) (q : ℕ → ℕ+) :
    MeasurableSpace ((U : Filter ℕ).Product (fun n => ZMod (q n : ℕ))) := loebMeasurableSpace U

theorem loeb_quotient_quasiPeriodic_or_connected_cosets
    (U : Ultrafilter ℕ) (hU : (U : Filter ℕ) ≤ atTop) (q : ℕ → ℕ+)
    {K L : Type*} [AddCommGroup K] [AddCommGroup L]
    [TopologicalSpace K] [TopologicalSpace L] [IsTopologicalAddGroup K]
    [IsTopologicalAddGroup L] [CompactSpace K] [CompactSpace L]
    [T2Space K] [T2Space L] [PolishSpace K] [PolishSpace L]
    [MeasurableSpace K] [MeasurableSpace L] [BorelSpace K] [BorelSpace L]
    [MeasurableAdd₂ K] [MeasurableNeg K] [MeasurableAdd₂ L] [MeasurableNeg L]
    (φ : (U : Filter ℕ).Product (fun n => ZMod (q n : ℕ)) →+ K)
    (hφ : Measurable φ) (hsurj : Function.Surjective φ)
    (ψ : K →+ L) (hψ : Continuous ψ) (hψsurj : Function.Surjective ψ)
    (C D : Set K) (hCsc : IsSigmaCompact C) (hDsc : IsSigmaCompact D)
    (hCpos : 0 < Measure.map φ (loebMeasure U hU) C)
    (hDpos : 0 < Measure.map φ (loebMeasure U hU) D)
    (hcomp : 0 < loebMeasure U hU ((φ ⁻¹' C) + (φ ⁻¹' D))ᶜ)
    (hfull : loebMeasure U hU ((φ ⁻¹' C) + (φ ⁻¹' D)) =
      loebMeasure U hU (φ ⁻¹' C) + loebMeasure U hU (φ ⁻¹' D))
    (hirr : MeasureIrreducible (loebMeasure U hU) (internalInnerMeasure U hU)
      (φ ⁻¹' C) (φ ⁻¹' D))
    (hne : MeasureNonextendible (loebMeasure U hU) (internalInnerMeasure U hU)
      (φ ⁻¹' C) (φ ⁻¹' D))
    (hnoAE : ∀ H : AddSubgroup ((U : Filter ℕ).Product (fun n => ZMod (q n : ℕ))),
      MeasurableSet (H : Set ((U : Filter ℕ).Product (fun n => ZMod (q n : ℕ)))) →
      0 < loebMeasure (X := fun n => ZMod (q n : ℕ)) U hU (H : Set _) →
      ¬ ∀ t ∈ H, t +ᵥ ((φ ⁻¹' C) + (φ ⁻¹' D)) =ᵐ[loebMeasure U hU]
        (φ ⁻¹' C) + (φ ⁻¹' D))
    (hker : ∀ t : K, t ∈ ψ.ker ↔
      t +ᵥ (C + D) =ᵐ[Measure.map φ (loebMeasure U hU)] C + D) :
    Nonempty (QuasiPeriodicPairData (loebMeasure U hU) (internalInnerMeasure U hU)
      (φ ⁻¹' C) (φ ⁻¹' D)) ∨
      ∃ P Q : Set L, IsSigmaCompact P ∧ IsSigmaCompact Q ∧
        (ψ.comp φ) ⁻¹' P =ᵐ[loebMeasure U hU] φ ⁻¹' C ∧
        (ψ.comp φ) ⁻¹' Q =ᵐ[loebMeasure U hU] φ ⁻¹' D ∧
        (ψ.comp φ) ⁻¹' (P + Q) =ᵐ[loebMeasure U hU] φ ⁻¹' (C + D) ∧
        (∀ t : L, t +ᵥ (P + Q) =ᵐ[Measure.map (ψ.comp φ) (loebMeasure U hU)] P + Q → t = 0) ∧
        ∃ H : OpenAddSubgroup L, ConnectedSpace H ∧
          ∃ a b : L, P ⊆ a +ᵥ (H : Set L) ∧ Q ⊆ b +ᵥ (H : Set L) := by
  let μ := loebMeasure (X := fun n => ZMod (q n : ℕ)) U hU
  let θ := ψ.comp φ
  have hθ : Measurable θ := hψ.measurable.comp hφ
  have hθsurj : Function.Surjective θ := hψsurj.comp hsurj
  have hCm : MeasurableSet C := measurableSet_of_sigmaCompact C hCsc
  have hDm : MeasurableSet D := measurableSet_of_sigmaCompact D hDsc
  have hCDm : MeasurableSet (C + D) :=
    measurableSet_of_sigmaCompact _ (isSigmaCompact_add_sets C D hCsc hDsc)
  have hAm : MeasurableSet (φ ⁻¹' C) := hCm.preimage hφ
  have hBm : MeasurableSet (φ ⁻¹' D) := hDm.preimage hφ
  have hSm : MeasurableSet ((φ ⁻¹' C) + (φ ⁻¹' D)) := by
    rw [← preimage_add_of_surjective_addHom φ hsurj]
    exact hCDm.preimage hφ
  have hApos : 0 < μ (φ ⁻¹' C) := by
    rwa [Measure.map_apply hφ hCm] at hCpos
  have hBpos : 0 < μ (φ ⁻¹' D) := by
    rwa [Measure.map_apply hφ hDm] at hDpos
  obtain ⟨P, Q, hPsc, hQsc, hPm, hQm, hPQm, hPA, hQB, hPQ, hperiod⟩ :=
    loeb_compact_aperiodic_quotient_pair U hU q φ hφ hsurj ψ hψ hψsurj C D hCm hDm hCDm
      hirr hne hker
  have hPpullM : MeasurableSet (θ ⁻¹' P) := hPm.preimage hθ
  have hQpullM : MeasurableSet (θ ⁻¹' Q) := hQm.preimage hθ
  have hPQpullM : MeasurableSet ((θ ⁻¹' P) + (θ ⁻¹' Q)) := by
    rw [← preimage_add_of_surjective_addHom θ hθsurj]
    exact hPQm.preimage hθ
  have hPQae : (θ ⁻¹' P) + (θ ⁻¹' Q) =ᵐ[μ] (φ ⁻¹' C) + (φ ⁻¹' D) := by
    rw [← preimage_add_of_surjective_addHom θ hθsurj,
      ← preimage_add_of_surjective_addHom φ hsurj]
    exact hPQ
  obtain ⟨hPpos, hQpos, hPQfull, hPQirr, hPQne, hPQnoAE⟩ := loeb_ae_pair_model_structure
    U hU q (φ ⁻¹' C) (φ ⁻¹' D) (θ ⁻¹' P) (θ ⁻¹' Q) hAm hBm hPpullM hQpullM hPQpullM
      hApos hBpos hfull hirr hnoAE hPA hQB hPQae
  have hPQcomp : 0 < μ ((θ ⁻¹' P) + (θ ⁻¹' Q))ᶜ := by
    have hcomplement : ((θ ⁻¹' P) + (θ ⁻¹' Q))ᶜ =ᵐ[μ] ((φ ⁻¹' C) + (φ ⁻¹' D))ᶜ := by
      filter_upwards [hPQae] with x hx
      exact congrArg Not hx
    rwa [measure_congr hcomplement]
  have hPcompactPos : 0 < Measure.map θ μ P := by
    rwa [Measure.map_apply hθ hPm]
  have hQcompactPos : 0 < Measure.map θ μ Q := by
    rwa [Measure.map_apply hθ hQm]
  rcases loeb_compact_quasiPeriodic_or_connected_cosets U hU q θ hθ hθsurj P Q hPsc hQsc
    hPcompactPos hQcompactPos hPQcomp hPQfull hPQirr hPQne hPQnoAE hperiod with hp | hc
  · left
    obtain ⟨p⟩ := hp
    exact loeb_quasiPeriodic_pair_of_equal_sum_model U hU q (φ ⁻¹' C) (φ ⁻¹' D)
      (θ ⁻¹' P) (θ ⁻¹' Q) p hPQpullM hPQae hAm hBm hSm hApos hBpos hcomp hfull hirr hne hnoAE
  · exact Or.inr ⟨P, Q, hPsc, hQsc, hPA, hQB, hPQ, hperiod, hc⟩

end Erdos335.Loeb

end
