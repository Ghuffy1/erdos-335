import Erdos335.LoebDysonStep
import Erdos335.LoebEqualSumStructure
import Erdos335.CompactDysonSigma
import Erdos335.DysonMassDecay

/-!
# A shrinking sequence in a fixed compact factor

The construction stops with a quasi-periodic original pair or continues
through equality transforms whose right measures tend to zero.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Filter Set Topology MeasureTheory
open scoped Pointwise ENNReal

noncomputable section

namespace Erdos335.Loeb

local instance compactDysonSequenceLoebSpace (U : Ultrafilter ℕ) (q : ℕ → ℕ+) :
    MeasurableSpace ((U : Filter ℕ).Product (fun n => ZMod (q n : ℕ))) := loebMeasurableSpace U

theorem loeb_compact_dyson_sequence_or_quasiPeriodic
    (U : Ultrafilter ℕ) (hU : (U : Filter ℕ) ≤ atTop) (q : ℕ → ℕ+)
    {K : Type*} [AddCommGroup K] [TopologicalSpace K] [IsTopologicalAddGroup K]
    [CompactSpace K] [T2Space K] [PolishSpace K]
    [MeasurableSpace K] [BorelSpace K] [MeasurableAdd₂ K] [MeasurableNeg K]
    (φ : (U : Filter ℕ).Product (fun n => ZMod (q n : ℕ)) →+ K)
    (hφ : Measurable φ) (hsurj : Function.Surjective φ)
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
        (φ ⁻¹' C) + (φ ⁻¹' D)) :
    Nonempty (QuasiPeriodicPairData (loebMeasure U hU) (internalInnerMeasure U hU)
      (φ ⁻¹' C) (φ ⁻¹' D)) ∨
    ∃ Cn Dn : ℕ → Set K, ∃ en : ℕ → K,
      Cn 0 = C ∧ Dn 0 = D ∧
      (∀ n, IsSigmaCompact (Cn n) ∧ IsSigmaCompact (Dn n) ∧
        0 < Measure.map φ (loebMeasure U hU) (Cn n) ∧
        0 < Measure.map φ (loebMeasure U hU) (Dn n) ∧
        (φ ⁻¹' Cn n) + (φ ⁻¹' Dn n) =ᵐ[loebMeasure U hU] (φ ⁻¹' C) + (φ ⁻¹' D)) ∧
      (∀ n, Cn (n + 1) = dysonGroupLeft (Cn n) (Dn n) (en n) ∧
        Dn (n + 1) = dysonGroupRight (Cn n) (Dn n) (en n) ∧
        (Measure.map φ (loebMeasure U hU) (Dn (n + 1))).toReal ≤
          (1 - (Measure.map φ (loebMeasure U hU) (Dn n)).toReal) *
            (Measure.map φ (loebMeasure U hU) (Dn n)).toReal) ∧
      Tendsto (fun n => (Measure.map φ (loebMeasure U hU) (Dn n)).toReal) atTop (𝓝 0) ∧
      Tendsto (fun n => (Measure.map φ (loebMeasure U hU) (Cn n)).toReal) atTop
        (𝓝 (Measure.map φ (loebMeasure U hU) (C + D)).toReal) := by
  classical
  by_cases hQP : Nonempty (QuasiPeriodicPairData (loebMeasure U hU) (internalInnerMeasure U hU)
      (φ ⁻¹' C) (φ ⁻¹' D))
  · exact Or.inl hQP
  right
  let μ := loebMeasure (X := fun n => ZMod (q n : ℕ)) U hU
  let ν := Measure.map φ μ
  let A := φ ⁻¹' C
  let B := φ ⁻¹' D
  have : IsProbabilityMeasure μ := isProbabilityMeasure_loebMeasure U hU
  have : IsProbabilityMeasure ν := ⟨by
    change Measure.map φ μ univ = 1
    rw [Measure.map_apply hφ MeasurableSet.univ]
    simp⟩
  have hCm := measurableSet_of_sigmaCompact C hCsc
  have hDm := measurableSet_of_sigmaCompact D hDsc
  have hCDm := measurableSet_of_sigmaCompact (C + D) (isSigmaCompact_add_sets C D hCsc hDsc)
  have hAm : MeasurableSet A := hCm.preimage hφ
  have hBm : MeasurableSet B := hDm.preimage hφ
  have hSm : MeasurableSet (A + B) := by
    rw [← preimage_add_of_surjective_addHom φ hsurj C D]
    exact hCDm.preimage hφ
  have mass (S : Set K) (hS : MeasurableSet S) : μ (φ ⁻¹' S) = ν S :=
    (Measure.map_apply hφ hS).symm
  have hApos : 0 < μ A := (mass C hCm).symm ▸ hCpos
  have hBpos : 0 < μ B := (mass D hDm).symm ▸ hDpos
  let Good (X : Set K × Set K) : Prop :=
    IsSigmaCompact X.1 ∧ IsSigmaCompact X.2 ∧ 0 < ν X.1 ∧ 0 < ν X.2 ∧
    ((φ ⁻¹' X.1) + (φ ⁻¹' X.2) =ᵐ[μ] A + B) ∧
    μ ((φ ⁻¹' X.1) + (φ ⁻¹' X.2)) = μ (φ ⁻¹' X.1) + μ (φ ⁻¹' X.2)
  let State := {X : Set K × Set K // Good X}
  let initial : State := ⟨(C, D), hCsc, hDsc, hCpos, hDpos, Filter.EventuallyEq.rfl, hfull⟩
  have next_exists (X : State) : ∃ e : K, ∃ Y : State,
      Y.val.1 = dysonGroupLeft X.val.1 X.val.2 e ∧
      Y.val.2 = dysonGroupRight X.val.1 X.val.2 e ∧
      (ν Y.val.2).toReal ≤ (1 - (ν X.val.2).toReal) * (ν X.val.2).toReal := by
    obtain ⟨hLsc, hRsc, hLpos, hRpos, hsumAE, hsumFull⟩ := X.property
    have hLm := measurableSet_of_sigmaCompact X.val.1 hLsc
    have hRm := measurableSet_of_sigmaCompact X.val.2 hRsc
    have hLRm := measurableSet_of_sigmaCompact (X.val.1 + X.val.2)
      (isSigmaCompact_add_sets X.val.1 X.val.2 hLsc hRsc)
    let P := φ ⁻¹' X.val.1
    let Q := φ ⁻¹' X.val.2
    have hPm : MeasurableSet P := hLm.preimage hφ
    have hQm : MeasurableSet Q := hRm.preimage hφ
    have hPQm : MeasurableSet (P + Q) := by
      rw [← preimage_add_of_surjective_addHom φ hsurj X.val.1 X.val.2]
      exact hLRm.preimage hφ
    have hPpos : 0 < μ P := (mass X.val.1 hLm).symm ▸ hLpos
    have hQpos : 0 < μ Q := (mass X.val.2 hRm).symm ▸ hRpos
    obtain ⟨hPQirr, hPQne, hPQnoAE⟩ :=
      (loeb_equal_sum_model_structure U hU q A B P Q hAm hBm hSm hApos hBpos hcomp hfull
        hirr hne hnoAE hPm hQm hPQm hPpos hQpos hsumFull hsumAE).resolve_left hQP
    have hPQcomp : 0 < μ (P + Q)ᶜ := by
      have hc : (P + Q)ᶜ =ᵐ[μ] (A + B)ᶜ := by
        filter_upwards [hsumAE] with x hx
        exact congrArg Not hx
      rw [measure_congr hc]
      exact hcomp
    rcases loeb_compact_dyson_step_or_quasiPeriodic U hU q φ hφ hsurj X.val.1 X.val.2
      hLm hRm hLRm hLpos hRpos hPQcomp hsumFull hPQirr hPQne hPQnoAE with hQPX | hstep
    · obtain ⟨p⟩ := hQPX
      exact False.elim (hQP (loeb_quasiPeriodic_pair_of_equal_sum_model U hU q A B P Q p
        hPQm hsumAE hAm hBm hSm hApos hBpos hcomp hfull hirr hne hnoAE))
    · obtain ⟨e, hepos, hebound, _, _, _, heAE, heFull, _⟩ := hstep
      let L := dysonGroupLeft X.val.1 X.val.2 (φ e)
      let R := dysonGroupRight X.val.1 X.val.2 (φ e)
      obtain ⟨hLsc', hRsc'⟩ := isSigmaCompact_dysonGroup X.val.1 X.val.2 hLsc hRsc (φ e)
      have hRm' : MeasurableSet R := measurableSet_of_sigmaCompact R hRsc'
      have hLpos' : 0 < ν L := hLpos.trans_le (measure_mono subset_union_left)
      have hRpos' : 0 < ν R := by
        rw [← mass R hRm', preimage_dysonGroupRight]
        exact hepos
      have heAE' : (φ ⁻¹' L) + (φ ⁻¹' R) =ᵐ[μ] A + B := by
        rw [preimage_dysonGroupLeft, preimage_dysonGroupRight]
        exact heAE.trans hsumAE
      have heFull' : μ ((φ ⁻¹' L) + (φ ⁻¹' R)) = μ (φ ⁻¹' L) + μ (φ ⁻¹' R) := by
        rw [preimage_dysonGroupLeft, preimage_dysonGroupRight]
        exact heFull
      let Y : State := ⟨(L, R), hLsc', hRsc', hLpos', hRpos', heAE', heFull'⟩
      refine ⟨φ e, Y, rfl, rfl, ?_⟩
      rw [← mass R hRm', ← mass X.val.2 hRm, preimage_dysonGroupRight]
      exact hebound
  choose stepParameter step hstepLeft hstepRight hstepBound using next_exists
  let states (n : ℕ) : State := step^[n] initial
  let Cn (n : ℕ) : Set K := (states n).val.1
  let Dn (n : ℕ) : Set K := (states n).val.2
  let en (n : ℕ) : K := stepParameter (states n)
  have hstates (n : ℕ) : states (n + 1) = step (states n) :=
    Function.iterate_succ_apply' step n initial
  have hgood (n : ℕ) : Good (Cn n, Dn n) := (states n).property
  have hstep (n : ℕ) : Cn (n + 1) = dysonGroupLeft (Cn n) (Dn n) (en n) ∧
      Dn (n + 1) = dysonGroupRight (Cn n) (Dn n) (en n) ∧
      (ν (Dn (n + 1))).toReal ≤ (1 - (ν (Dn n)).toReal) * (ν (Dn n)).toReal := by
    change (states (n + 1)).val.1 = _ ∧ (states (n + 1)).val.2 = _ ∧
      (ν (states (n + 1)).val.2).toReal ≤
        (1 - (ν (states n).val.2).toReal) * (ν (states n).val.2).toReal
    rw [hstates]
    exact ⟨hstepLeft (states n), hstepRight (states n), hstepBound (states n)⟩
  have hdecay : Tendsto (fun n => (ν (Dn n)).toReal) atTop (𝓝 0) :=
    dyson_mass_tendsto_zero _ (fun _ => ENNReal.toReal_nonneg) (fun n => (hstep n).2.2)
  have htotal (n : ℕ) : (ν (Cn n)).toReal + (ν (Dn n)).toReal = (ν (C + D)).toReal := by
    obtain ⟨hCn, hDn, _, _, hAE, hFull⟩ := hgood n
    rw [← ENNReal.toReal_add (measure_ne_top ν _) (measure_ne_top ν _)]
    congr 1
    rw [← mass (Cn n) (measurableSet_of_sigmaCompact _ hCn),
      ← mass (Dn n) (measurableSet_of_sigmaCompact _ hDn), ← hFull, measure_congr hAE,
      ← preimage_add_of_surjective_addHom φ hsurj C D, mass (C + D) hCDm]
  have hleftDecay : Tendsto (fun n => (ν (Cn n)).toReal) atTop (𝓝 (ν (C + D)).toReal) := by
    have heq : (fun n => (ν (Cn n)).toReal) =
        (fun n => (ν (C + D)).toReal - (ν (Dn n)).toReal) := by
      funext n
      have h := htotal n
      linarith
    rw [heq]
    simpa using tendsto_const_nhds.sub hdecay
  refine ⟨Cn, Dn, en, rfl, rfl, ?_, hstep, hdecay, hleftDecay⟩
  intro n
  exact ⟨(hgood n).1, (hgood n).2.1, (hgood n).2.2.1, (hgood n).2.2.2.1,
    (hgood n).2.2.2.2.1⟩

end Erdos335.Loeb

end
