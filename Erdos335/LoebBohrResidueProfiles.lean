import Erdos335.NaturalQuotientRefinement
import Erdos335.LoebFiniteResidueProfiles
import Erdos335.LoebInternalBohrPair
import Erdos335.LoebCircleSubgroupMeasure

/-!
# Circle distribution on every refinement of a natural residue class
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Filter Set MeasureTheory
open scoped Pointwise ENNReal

noncomputable section

namespace Erdos335.Loeb

local instance bohrResidueProfilesLoebSpace (U : Ultrafilter ℕ) (q : ℕ → ℕ+) :
    MeasurableSpace ((U : Filter ℕ).Product (fun n => ZMod (q n : ℕ))) := loebMeasurableSpace U

theorem loeb_nested_finite_circle_fiber_measure
    (U : Ultrafilter ℕ) (hU : (U : Filter ℕ) ≤ atTop) (q : ℕ → ℕ+) (m h : ℕ+)
    (hd : ∀ᶠ n in U, (h : ℕ) ∣ (q n : ℕ)) (hmh : (m : ℕ) ∣ (h : ℕ))
    (φ : (U : Filter ℕ).Product (fun n => ZMod (q n : ℕ)) →+ AddCircle (1 : ℝ))
    (hφ : Measurable φ) (hsurj : Function.Surjective φ)
    (S : Set (AddCircle (1 : ℝ))) (hS : MeasurableSet S)
    (c : ZMod (m : ℕ)) (r : ZMod (h : ℕ)) :
    loebMeasure U hU (((finiteQuotient U (fun n => naturalCyclicProjection (q n) m)) ⁻¹' {c} ∩
      φ ⁻¹' S) ∩ (finiteQuotient U (fun n => naturalCyclicProjection (q n) h)) ⁻¹' {r}) =
      if naturalCyclicProjection h m r = c then (1 : ℝ≥0∞) / (h : ℕ) * volume S else 0 := by
  classical
  let G := (U : Filter ℕ).Product (fun n => ZMod (q n : ℕ))
  let μ : Measure G := loebMeasure (X := fun n => ZMod (q n : ℕ)) U hU
  let f := finiteQuotient U (fun n => naturalCyclicProjection (q n) m)
  let g := finiteQuotient U (fun n => naturalCyclicProjection (q n) h)
  have hcomp (x : G) : naturalCyclicProjection h m (g x) = f x :=
    congrArg (fun k => k x) (finiteQuotient_natural_refinement U q h m hd hmh)
  by_cases hr : naturalCyclicProjection h m r = c
  · rw [if_pos hr]
    have heq : (f ⁻¹' {c} ∩ φ ⁻¹' S) ∩ g ⁻¹' {r} = φ ⁻¹' S ∩ g ⁻¹' {r} := by
      ext x
      constructor
      · exact fun hx => ⟨hx.1.2, hx.2⟩
      · intro hx
        refine ⟨⟨?_, hx.1⟩, hx.2⟩
        change f x = c
        rw [← hcomp x, show g x = r from hx.2, hr]
    change μ ((f ⁻¹' {c} ∩ φ ⁻¹' S) ∩ g ⁻¹' {r}) = _
    rw [heq]
    have hgm : MeasurableSet (g.ker : Set G) := by
      change MeasurableSet ((finiteQuotient U (fun n => naturalCyclicProjection (q n) h)).ker : Set G)
      rw [finiteQuotient_ker]
      exact measurable_internalSet U _
    have hgMass : μ (g.ker : Set G) = (1 : ℝ≥0∞) / (h : ℕ) := by
      change loebMeasure U hU ((finiteQuotient U (fun n => naturalCyclicProjection (q n) h)).ker : Set G) = _
      rw [finiteQuotient_ker, loebMeasure_internalSubgroup_of_eventually_quotients U hU
        (fun n => naturalCyclicProjection (q n) h)
          (hd.mono fun n hn => naturalCyclicProjection_surjective (q n) h hn)]
      simp
    have hgpos : 0 < μ (g.ker : Set G) := by
      rw [hgMass]
      exact ENNReal.div_pos (by norm_num) (by simp)
    obtain ⟨a, ha⟩ := finiteQuotient_surjective_of_eventually U
      (fun n => naturalCyclicProjection (q n) h)
        (hd.mono fun n hn => naturalCyclicProjection_surjective (q n) h hn) r
    change g a = r at ha
    rw [← ha, addHom_fiber_eq_coset]
    exact (loeb_circle_coset_intersection_measure U hU q φ hφ hsurj g.ker hgm hgpos S hS a).trans
      (congrArg (fun t => t * volume S) hgMass)
  · rw [if_neg hr]
    have heq : (f ⁻¹' {c} ∩ φ ⁻¹' S) ∩ g ⁻¹' {r} = ∅ := by
      apply subset_antisymm
      · intro x hx
        exfalso
        apply hr
        calc
          naturalCyclicProjection h m r = naturalCyclicProjection h m (g x) :=
            congrArg (naturalCyclicProjection h m) (show g x = r from hx.2).symm
          _ = f x := hcomp x
          _ = c := hx.1.1
      · exact empty_subset _
    change μ ((f ⁻¹' {c} ∩ φ ⁻¹' S) ∩ g ⁻¹' {r}) = 0
    rw [heq, measure_empty]

theorem loeb_natural_bohr_residue_profile
    (U : Ultrafilter ℕ) (hU : (U : Filter ℕ) ≤ atTop) (q : ℕ → ℕ+) (m h : ℕ+)
    (hd : ∀ᶠ n in U, (h : ℕ) ∣ (q n : ℕ)) (hmh : (m : ℕ) ∣ (h : ℕ))
    (χ : ∀ n, ZMod (q n : ℕ) →+ AddCircle (1 : ℝ))
    (hsurj : Function.Surjective (ultralimitAddHom U χ))
    (a : (U : Filter ℕ).Product (fun n => ZMod (q n : ℕ)))
    (x : AddCircle (1 : ℝ)) (length : ℝ) (h0 : 0 ≤ length) (h1 : length ≤ 1)
    (r : ZMod (h : ℕ)) :
    loebResidueProfile U hU q h
      (internalBohrCoset U q m (fun n => naturalCyclicProjection (q n) m) χ a x length) r =
      if naturalCyclicProjection h m r = finiteQuotient U (fun n => naturalCyclicProjection (q n) m) a
        then length else 0 := by
  classical
  let S := x +ᵥ (((↑) : ℝ → AddCircle (1 : ℝ)) '' Icc 0 length)
  have hS : MeasurableSet S := by
    dsimp only [S]
    rw [vadd_set_eq_neg_preimage]
    exact (isCompact_Icc.image (AddCircle.continuous_mk' 1)).isClosed.measurableSet.preimage
      (measurable_const_add _)
  have hmass := loeb_nested_finite_circle_fiber_measure U hU q m h hd hmh
    (ultralimitAddHom U χ) (measurable_ultralimitAddHom U χ) hsurj S hS
    (finiteQuotient U (fun n => naturalCyclicProjection (q n) m) a) r
  unfold loebResidueProfile internalBohrCoset
  rw [← addHom_fiber_eq_coset, hmass]
  rw [show volume S = ENNReal.ofReal length from volume_unitCircle_normalized_closedArc x length h1]
  split_ifs
  · rw [ENNReal.toReal_mul, ENNReal.toReal_div, ENNReal.toReal_one,
      ENNReal.toReal_natCast, ENNReal.toReal_ofReal h0]
    have hh : ((h : ℕ) : ℝ) ≠ 0 := by exact_mod_cast h.ne_zero
    field_simp
  · simp

end Erdos335.Loeb

end
