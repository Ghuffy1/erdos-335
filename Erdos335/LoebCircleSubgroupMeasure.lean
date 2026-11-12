import Erdos335.LoebCircleSubgroupImage
import Erdos335.LoebHaar
import Erdos335.CompactDysonTransform
import Mathlib.MeasureTheory.Measure.Haar.Unique
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Periodic

/-!
# Circle distribution on positive Loeb subgroup cosets
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter MeasureTheory
open scoped Pointwise ENNReal

noncomputable section

namespace Erdos335.Loeb

theorem map_restrict_subgroup_unitCircle
    {G : Type*} [AddCommGroup G] [MeasurableSpace G] [MeasurableAdd G]
    (μ : Measure G) [IsFiniteMeasure μ] [μ.IsAddLeftInvariant]
    (φ : G →+ AddCircle (1 : ℝ)) (hφ : Measurable φ)
    (H : AddSubgroup G) (hH : MeasurableSet (H : Set G)) (hHpos : 0 < μ (H : Set G))
    (hsurj : Function.Surjective (φ.comp H.subtype)) :
    Measure.map φ (μ.restrict (H : Set G)) = μ (H : Set G) • (volume : Measure (AddCircle (1 : ℝ))) := by
  have : Fact (0 < (1 : ℝ)) := ⟨zero_lt_one⟩
  let ν := Measure.map φ (μ.restrict (H : Set G))
  have hmapH (x : H) : Measure.map (fun y => (x : G) + y) (μ.restrict (H : Set G)) =
      μ.restrict (H : Set G) := by
    have hpreH : (fun y => (x : G) + y) ⁻¹' (H : Set G) = H := by
      ext y
      constructor
      · intro hy
        have h := H.sub_mem hy x.property
        change y ∈ H
        simpa only [add_sub_cancel_left] using h
      · exact fun hy => H.add_mem x.property hy
    apply Measure.ext
    intro T hT
    rw [Measure.map_apply (measurable_const_add (x : G)) hT,
      Measure.restrict_apply (hT.preimage (measurable_const_add (x : G))),
      Measure.restrict_apply hT]
    calc
      μ ((fun y => (x : G) + y) ⁻¹' T ∩ (H : Set G)) =
          μ ((fun y => (x : G) + y) ⁻¹' (T ∩ (H : Set G))) := by
        rw [preimage_inter, hpreH]
      _ = μ (T ∩ (H : Set G)) := measure_preimage_add _ _ _
  have : ν.IsAddLeftInvariant := by
    constructor
    intro t
    obtain ⟨x, hx⟩ := hsurj t
    change φ (x : G) = t at hx
    have hcomp : (fun y => t + y) ∘ φ = φ ∘ (fun y => (x : G) + y) := by
      funext y
      simp only [Function.comp_apply, map_add, hx]
    change Measure.map (fun y => t + y) (Measure.map φ (μ.restrict (H : Set G))) = ν
    rw [Measure.map_map (measurable_const_add t) hφ, hcomp,
      ← Measure.map_map hφ (measurable_const_add (x : G)), hmapH]
  have hνmass : ν univ = μ (H : Set G) := by
    dsimp [ν]
    rw [Measure.map_apply hφ MeasurableSet.univ]
    simp
  let θ : Measure (AddCircle (1 : ℝ)) := (μ (H : Set G))⁻¹ • ν
  have : IsProbabilityMeasure θ := by
    constructor
    change ((μ (H : Set G))⁻¹ • ν) univ = 1
    rw [Measure.smul_apply, smul_eq_mul, hνmass,
      ENNReal.inv_mul_cancel hHpos.ne' (measure_ne_top μ _)]
  have : θ.IsAddLeftInvariant := inferInstance
  have : θ.IsAddHaarMeasure :=
    Measure.isAddHaarMeasure_of_isCompact_nonempty_interior θ univ isCompact_univ
      (by simp) (by simp) (by simp)
  have : IsProbabilityMeasure (volume : Measure (AddCircle (1 : ℝ))) :=
    ⟨by simpa using AddCircle.measure_univ (1 : ℝ)⟩
  have hθ : θ = volume := Measure.isAddHaarMeasure_eq_of_isProbabilityMeasure _ _
  change ν = μ (H : Set G) • volume
  calc
    ν = μ (H : Set G) • θ := by
      dsimp [θ]
      rw [smul_smul, ENNReal.mul_inv_cancel hHpos.ne' (measure_ne_top μ _), one_smul]
    _ = _ := by rw [hθ]

local instance circleSubgroupMeasureLoebSpace (U : Ultrafilter ℕ) (q : ℕ → ℕ+) :
    MeasurableSpace ((U : Filter ℕ).Product (fun n => ZMod (q n : ℕ))) := loebMeasurableSpace U

theorem loeb_circle_subgroup_intersection_measure
    (U : Ultrafilter ℕ) (hU : (U : Filter ℕ) ≤ atTop) (q : ℕ → ℕ+)
    (φ : (U : Filter ℕ).Product (fun n => ZMod (q n : ℕ)) →+ AddCircle (1 : ℝ))
    (hφ : Measurable φ) (hsurj : Function.Surjective φ)
    (H : AddSubgroup ((U : Filter ℕ).Product (fun n => ZMod (q n : ℕ))))
    (hH : MeasurableSet (H : Set ((U : Filter ℕ).Product (fun n => ZMod (q n : ℕ)))))
    (hHpos : 0 < loebMeasure U hU (H : Set ((U : Filter ℕ).Product (fun n => ZMod (q n : ℕ)))))
    (S : Set (AddCircle (1 : ℝ))) (hS : MeasurableSet S) :
    loebMeasure U hU (φ ⁻¹' S ∩ (H : Set _)) =
      loebMeasure (X := fun n => ZMod (q n : ℕ)) U hU (H : Set _) * volume S := by
  let G := (U : Filter ℕ).Product (fun n => ZMod (q n : ℕ))
  let μ := loebMeasure (X := fun n => ZMod (q n : ℕ)) U hU
  have : IsProbabilityMeasure μ := isProbabilityMeasure_loebMeasure U hU
  have : MeasurableAdd G := {
    measurable_const_add := measurable_add_left U hU
    measurable_add_const := fun c => by
      simpa only [add_comm] using measurable_add_left U hU c }
  have : μ.IsAddLeftInvariant := ⟨fun e => loebMeasure_map_add_left U hU e⟩
  have hmap := map_restrict_subgroup_unitCircle μ φ hφ H hH hHpos
    (surjective_circle_restriction_of_positive_loeb_subgroup U hU q φ hsurj H hH hHpos)
  have h := congrArg (fun ν : Measure (AddCircle (1 : ℝ)) => ν S) hmap
  rw [Measure.map_apply hφ hS, Measure.restrict_apply (hS.preimage hφ),
    Measure.smul_apply, smul_eq_mul] at h
  exact h

theorem loeb_circle_coset_intersection_measure
    (U : Ultrafilter ℕ) (hU : (U : Filter ℕ) ≤ atTop) (q : ℕ → ℕ+)
    (φ : (U : Filter ℕ).Product (fun n => ZMod (q n : ℕ)) →+ AddCircle (1 : ℝ))
    (hφ : Measurable φ) (hsurj : Function.Surjective φ)
    (H : AddSubgroup ((U : Filter ℕ).Product (fun n => ZMod (q n : ℕ))))
    (hH : MeasurableSet (H : Set ((U : Filter ℕ).Product (fun n => ZMod (q n : ℕ)))))
    (hHpos : 0 < loebMeasure U hU (H : Set ((U : Filter ℕ).Product (fun n => ZMod (q n : ℕ)))))
    (S : Set (AddCircle (1 : ℝ))) (hS : MeasurableSet S)
    (a : (U : Filter ℕ).Product (fun n => ZMod (q n : ℕ))) :
    loebMeasure U hU (φ ⁻¹' S ∩ (a +ᵥ (H : Set _))) =
      loebMeasure (X := fun n => ZMod (q n : ℕ)) U hU (H : Set _) * volume S := by
  have : Fact (0 < (1 : ℝ)) := ⟨zero_lt_one⟩
  have hshift : MeasurableSet (-(φ a) +ᵥ S) := by
    rw [vadd_set_eq_neg_preimage]
    exact hS.preimage (measurable_const_add (- -(φ a)))
  have hset : (fun x => a + x) ⁻¹' (φ ⁻¹' S ∩ (a +ᵥ (H : Set _))) =
      φ ⁻¹' (-(φ a) +ᵥ S) ∩ (H : Set _) := by
    ext x
    simp [vadd_set_eq_neg_preimage, map_add]
  have hmass : volume (-(φ a) +ᵥ S) = volume S := by
    rw [vadd_set_eq_neg_preimage, measure_preimage_add]
  have h := loebMeasure_preimage_add_left U hU a (φ ⁻¹' S ∩ (a +ᵥ (H : Set _)))
  rw [hset, loeb_circle_subgroup_intersection_measure U hU q φ hφ hsurj H hH hHpos
    (-(φ a) +ᵥ S) hshift, hmass] at h
  exact h.symm

end Erdos335.Loeb

end
