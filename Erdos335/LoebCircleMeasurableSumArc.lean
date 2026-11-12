import Erdos335.LoebCircleSumArc
import Erdos335.LoebAEModelStructure
import Erdos335.CompactSigmaRepresentatives

/-!
# Circle sumset arcs for measurable compact-factor inputs
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter Topology MeasureTheory
open scoped Pointwise ENNReal

noncomputable section

namespace Erdos335.Loeb

local instance circleMeasurableArcLoebSpace (U : Ultrafilter ℕ) (q : ℕ → ℕ+) :
    MeasurableSpace ((U : Filter ℕ).Product (fun n => ZMod (q n : ℕ))) := loebMeasurableSpace U

theorem loeb_unitCircle_measurable_sum_ae_arc_or_quasiPeriodic
    (U : Ultrafilter ℕ) (hU : (U : Filter ℕ) ≤ atTop) (q : ℕ → ℕ+)
    (φ : (U : Filter ℕ).Product (fun n => ZMod (q n : ℕ)) →+ AddCircle (1 : ℝ))
    (hφ : Measurable φ) (hsurj : Function.Surjective φ)
    (C D : Set (AddCircle (1 : ℝ)))
    (hC : MeasurableSet C) (hD : MeasurableSet D) (hS : MeasurableSet (C + D))
    (hCpos : 0 < volume C) (hDpos : 0 < volume D)
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
    (hperiod : ∀ z : AddCircle (1 : ℝ), z +ᵥ (C + D) =ᵐ[volume] C + D → z = 0) :
    Nonempty (QuasiPeriodicPairData (loebMeasure U hU) (internalInnerMeasure U hU)
      (φ ⁻¹' C) (φ ⁻¹' D)) ∨
    ∃ c a b : ℝ, 0 ≤ a ∧ a < b ∧ b ≤ 1 ∧ b - a < 1 ∧
      (-(c : AddCircle (1 : ℝ)) +ᵥ (C + D)) =ᵐ[volume]
        (((↑) : ℝ → AddCircle (1 : ℝ)) '' Ioo a b) := by
  have : Fact (0 < (1 : ℝ)) := ⟨zero_lt_one⟩
  let μ := loebMeasure (X := fun n => ZMod (q n : ℕ)) U hU
  have : IsProbabilityMeasure μ := isProbabilityMeasure_loebMeasure U hU
  have : IsProbabilityMeasure (volume : Measure (AddCircle (1 : ℝ))) :=
    ⟨by simpa using AddCircle.measure_univ (1 : ℝ)⟩
  have : IsProbabilityMeasure (Measure.map φ μ) := ⟨by
    rw [Measure.map_apply hφ MeasurableSet.univ]
    simp⟩
  have : Measure.IsAddHaarMeasure (Measure.map φ μ) :=
    loebMeasure_map_hom_isAddHaarMeasure U hU φ hφ hsurj
  have hvolume : Measure.map φ μ = volume :=
    Measure.isAddHaarMeasure_eq_of_isProbabilityMeasure _ _
  have mass (T : Set (AddCircle (1 : ℝ))) (hT : MeasurableSet T) :
      μ (φ ⁻¹' T) = volume T := by
    rw [← Measure.map_apply hφ hT, hvolume]
  obtain ⟨C₀, hC₀C, hC₀sc, hC₀m, hC₀mass⟩ := exists_full_measure_sigmaCompact_subset volume C hC
  obtain ⟨D₀, hD₀D, hD₀sc, hD₀m, hD₀mass⟩ := exists_full_measure_sigmaCompact_subset volume D hD
  have hS₀m : MeasurableSet (C₀ + D₀) :=
    measurableSet_of_sigmaCompact _ (isSigmaCompact_add_sets C₀ D₀ hC₀sc hD₀sc)
  let A := φ ⁻¹' C
  let B := φ ⁻¹' D
  let P := φ ⁻¹' C₀
  let Q := φ ⁻¹' D₀
  have hAm : MeasurableSet A := hC.preimage hφ
  have hBm : MeasurableSet B := hD.preimage hφ
  have hPm : MeasurableSet P := hC₀m.preimage hφ
  have hQm : MeasurableSet Q := hD₀m.preimage hφ
  have hSm : MeasurableSet (A + B) := by
    rw [← preimage_add_of_surjective_addHom φ hsurj C D]
    exact hS.preimage hφ
  have hPQm : MeasurableSet (P + Q) := by
    rw [← preimage_add_of_surjective_addHom φ hsurj C₀ D₀]
    exact hS₀m.preimage hφ
  have hPA : P ⊆ A := preimage_mono hC₀C
  have hQB : Q ⊆ B := preimage_mono hD₀D
  have hPmass : μ P = μ A := by rw [mass C₀ hC₀m, mass C hC, hC₀mass]
  have hQmass : μ Q = μ B := by rw [mass D₀ hD₀m, mass D hD, hD₀mass]
  have hPae : P =ᵐ[μ] A :=
    ae_eq_of_subset_of_measure_ge hPA hPmass.ge hPm.nullMeasurableSet (measure_ne_top μ _)
  have hQae : Q =ᵐ[μ] B :=
    ae_eq_of_subset_of_measure_ge hQB hQmass.ge hQm.nullMeasurableSet (measure_ne_top μ _)
  have hsumMass : μ (P + Q) = μ (A + B) := by
    rw [← internalInnerMeasure_eq U hU _ hPQm, ← internalInnerMeasure_eq U hU _ hSm]
    exact hirr P Q hPm hQm hPA hQB hPmass hQmass
  have hsumAE : P + Q =ᵐ[μ] A + B :=
    ae_eq_of_subset_of_measure_ge (add_subset_add hPA hQB) hsumMass.ge
      hPQm.nullMeasurableSet (measure_ne_top μ _)
  have hCpositive : 0 < μ A := by rw [mass C hC]; exact hCpos
  have hDpositive : 0 < μ B := by rw [mass D hD]; exact hDpos
  obtain ⟨_, _, hPQfull, hPQirr, hPQne, hPQnoAE⟩ := loeb_ae_pair_model_structure U hU q
    A B P Q hAm hBm hPm hQm hPQm hCpositive hDpositive hfull hirr hnoAE hPae hQae hsumAE
  have hcompactAE : C₀ + D₀ =ᵐ[volume] C + D := by
    have hpre := hsumAE
    rw [← preimage_add_of_surjective_addHom φ hsurj C₀ D₀,
      ← preimage_add_of_surjective_addHom φ hsurj C D] at hpre
    have h := ae_map_set_eq_of_preimage μ φ hφ _ _ hS₀m hS hpre
    rwa [hvolume] at h
  have hPQcomp : 0 < μ (P + Q)ᶜ := by
    have hc : (P + Q)ᶜ =ᵐ[μ] (A + B)ᶜ := by
      filter_upwards [hsumAE] with x hx
      exact congrArg Not hx
    rwa [measure_congr hc]
  have hperiod₀ (t : AddCircle (1 : ℝ)) (ht : t +ᵥ (C₀ + D₀) =ᵐ[volume] C₀ + D₀) : t = 0 :=
    hperiod t (((vadd_set_ae_eq t).2 hcompactAE).symm.trans (ht.trans hcompactAE))
  rcases loeb_unitCircle_sum_ae_arc_or_quasiPeriodic U hU q φ hφ hsurj C₀ D₀ hC₀sc hD₀sc
    (by rwa [hC₀mass]) (by rwa [hD₀mass]) hPQcomp hPQfull hPQirr hPQne hPQnoAE hperiod₀
    with hQP | harc
  · obtain ⟨p⟩ := hQP
    exact Or.inl (loeb_quasiPeriodic_pair_of_equal_sum_model U hU q A B P Q p hPQm hsumAE
      hAm hBm hSm hCpositive hDpositive hcomp hfull hirr hne hnoAE)
  · obtain ⟨c, a, b, ha, hab, hb, hlength, harc⟩ := harc
    exact Or.inr ⟨c, a, b, ha, hab, hb, hlength,
      ((vadd_set_ae_eq (-(c : AddCircle (1 : ℝ)))).2 hcompactAE).symm.trans harc⟩

end Erdos335.Loeb

end
