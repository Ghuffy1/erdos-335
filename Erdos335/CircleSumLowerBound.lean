import Erdos335.LoebMeasurableKneser
import Erdos335.LoebCircleSubgroupMeasure
import Erdos335.LoebCompactEqualityReduction

/-!
# A sum-measure lower bound in a proper circle sumset

Private proof development. Verification status is recorded separately.
A strict deficit would give a positive Loeb period subgroup. Its image under
a surjective circle homomorphism fills the circle and forces the sumset full.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Filter Set Topology MeasureTheory
open scoped Pointwise ENNReal

noncomputable section

namespace Erdos335.Loeb

local instance circleSumLowerBoundLoebSpace (U : Ultrafilter ℕ) (q : ℕ → ℕ+) :
    MeasurableSpace ((U : Filter ℕ).Product (fun n => ZMod (q n : ℕ))) :=
  loebMeasurableSpace U

theorem unitCircle_sum_measure_lower_bound
    (U : Ultrafilter ℕ) (hU : (U : Filter ℕ) ≤ atTop) (q : ℕ → ℕ+)
    (φ : (U : Filter ℕ).Product (fun n => ZMod (q n : ℕ)) →+ AddCircle (1 : ℝ))
    (hφ : Measurable φ) (hsurj : Function.Surjective φ)
    (C D : Set (AddCircle (1 : ℝ)))
    (hC : MeasurableSet C) (hD : MeasurableSet D) (hCD : MeasurableSet (C + D))
    (hCpos : 0 < volume C) (hDpos : 0 < volume D)
    (hproper : volume (C + D) < 1) :
    volume C + volume D ≤ volume (C + D) := by
  classical
  let G := (U : Filter ℕ).Product (fun n => ZMod (q n : ℕ))
  let μ := loebMeasure (X := fun n => ZMod (q n : ℕ)) U hU
  let P : Set G := φ ⁻¹' C
  let Q : Set G := φ ⁻¹' D
  letI : Fact (0 < (1 : ℝ)) := ⟨zero_lt_one⟩
  letI : IsProbabilityMeasure μ := isProbabilityMeasure_loebMeasure U hU
  letI : IsProbabilityMeasure (volume : Measure (AddCircle (1 : ℝ))) :=
    ⟨by simpa using AddCircle.measure_univ (1 : ℝ)⟩
  letI : IsProbabilityMeasure (Measure.map φ μ) := ⟨by
    rw [Measure.map_apply hφ MeasurableSet.univ]
    simp⟩
  letI : Measure.IsAddHaarMeasure (Measure.map φ μ) :=
    loebMeasure_map_hom_isAddHaarMeasure U hU φ hφ hsurj
  have hvolume : Measure.map φ μ = volume :=
    Measure.isAddHaarMeasure_eq_of_isProbabilityMeasure _ _
  have mass (T : Set (AddCircle (1 : ℝ))) (hT : MeasurableSet T) :
      μ (φ ⁻¹' T) = volume T := by
    rw [← Measure.map_apply hφ hT, hvolume]
  have hPm : MeasurableSet P := hC.preimage hφ
  have hQm : MeasurableSet Q := hD.preimage hφ
  have hPQ : P + Q = φ ⁻¹' (C + D) :=
    (preimage_add_of_surjective_addHom φ hsurj C D).symm
  have hPQm : MeasurableSet (P + Q) := by
    rw [hPQ]
    exact hCD.preimage hφ
  have hPmass : μ P = volume C := mass C hC
  have hQmass : μ Q = volume D := mass D hD
  have hPQmass : μ (P + Q) = volume (C + D) := by
    rw [hPQ, mass (C + D) hCD]
  have hPpos : 0 < μ P := by rwa [hPmass]
  have hQpos : 0 < μ Q := by rwa [hQmass]
  by_contra hbound
  have hstrict : volume (C + D) < volume C + volume D := lt_of_not_ge hbound
  have hsmall : internalInnerMeasure U hU (P + Q) < μ P + μ Q := by
    rw [internalInnerMeasure_eq U hU (P + Q) hPQm]
    change μ (P + Q) < μ P + μ Q
    rw [hPQmass, hPmass, hQmass]
    exact hstrict
  obtain ⟨h, hHm, hHpos, hperiod⟩ :=
    loeb_measurable_subcritical_period U hU q P Q hPm hQm hPpos hQpos hsmall
  let H : AddSubgroup G := naturalCyclicKernel U q h
  have hHsurj : Function.Surjective (φ.comp H.subtype) :=
    surjective_circle_restriction_of_positive_loeb_subgroup U hU q φ hsurj
      H hHm hHpos
  obtain ⟨p, hp⟩ := nonempty_of_measure_ne_zero hPpos.ne'
  obtain ⟨r, hr⟩ := nonempty_of_measure_ne_zero hQpos.ne'
  have hbase : p + r ∈ P + Q := ⟨p, hp, r, hr, rfl⟩
  have hfull : C + D = univ := by
    apply Set.eq_univ_of_forall
    intro z
    obtain ⟨t, ht⟩ := hHsurj (z - φ (p + r))
    change φ (t : G) = z - φ (p + r) at ht
    have hstep : p + r + (t : G) ∈ P + Q := by
      rw [← hperiod]
      exact ⟨p + r, hbase, (t : G), t.property, rfl⟩
    have himage : φ (p + r + (t : G)) ∈ C + D := by
      change p + r + (t : G) ∈ φ ⁻¹' (C + D)
      rw [← hPQ]
      exact hstep
    have heq : φ (p + r + (t : G)) = z := by
      rw [map_add, ht]
      abel
    simpa only [heq] using himage
  rw [hfull, measure_univ] at hproper
  exact (lt_irrefl (1 : ℝ≥0∞)) hproper

theorem unitCircle_sum_measure_toReal_lower_bound
    (U : Ultrafilter ℕ) (hU : (U : Filter ℕ) ≤ atTop) (q : ℕ → ℕ+)
    (φ : (U : Filter ℕ).Product (fun n => ZMod (q n : ℕ)) →+ AddCircle (1 : ℝ))
    (hφ : Measurable φ) (hsurj : Function.Surjective φ)
    (C D : Set (AddCircle (1 : ℝ)))
    (hC : MeasurableSet C) (hD : MeasurableSet D) (hCD : MeasurableSet (C + D))
    (hCpos : 0 < volume C) (hDpos : 0 < volume D)
    (hproper : (volume (C + D)).toReal < 1) :
    (volume C).toReal + (volume D).toReal ≤ (volume (C + D)).toReal := by
  letI : Fact (0 < (1 : ℝ)) := ⟨zero_lt_one⟩
  letI : IsProbabilityMeasure (volume : Measure (AddCircle (1 : ℝ))) :=
    ⟨by simpa using AddCircle.measure_univ (1 : ℝ)⟩
  have hproper' : volume (C + D) < 1 :=
    (ENNReal.toReal_lt_toReal (measure_ne_top volume _) (by simp)).mp
      (by simpa using hproper)
  have hbound := unitCircle_sum_measure_lower_bound U hU q φ hφ hsurj
    C D hC hD hCD hCpos hDpos hproper'
  have hreal := ENNReal.toReal_mono (measure_ne_top volume (C + D)) hbound
  rw [ENNReal.toReal_add (measure_ne_top volume C) (measure_ne_top volume D)] at hreal
  exact hreal

end Erdos335.Loeb

end
