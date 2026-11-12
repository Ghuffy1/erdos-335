import Erdos335.LoebFiniteAugmentation
import Erdos335.LoebPositiveSubgroups

/-!
# Canonical natural residue kernels

For each possible finite modulus, the coordinatewise natural residue
condition determines at most one quotient map of a cyclic ultraproduct.
This gives a fixed finite family when the modulus is bounded.
The whole group is the default when that modulus has no natural quotient.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Filter Set Topology MeasureTheory
open scoped ENNReal

noncomputable section

namespace Erdos335.Loeb

def naturalCyclicKernel {I : Type*} (U : Ultrafilter I) (q : I → ℕ+) (h : ℕ+) :
    AddSubgroup ((U : Filter I).Product (fun i => ZMod (q i : ℕ))) := by
  classical
  exact if hp : ∃ p : ∀ i, ZMod (q i : ℕ) →+ ZMod (h : ℕ),
      ∀ᶠ i in U, ∀ n : ℕ, p i (n : ZMod (q i : ℕ)) = (n : ZMod (h : ℕ))
    then (finiteQuotient U hp.choose).ker
    else ⊤

theorem naturalCyclicKernel_eq
    {I : Type*} (U : Ultrafilter I) (q : I → ℕ+) (h : ℕ+)
    (p : ∀ i, ZMod (q i : ℕ) →+ ZMod (h : ℕ))
    (hp : ∀ᶠ i in U, ∀ n : ℕ, p i (n : ZMod (q i : ℕ)) = (n : ZMod (h : ℕ))) :
    naturalCyclicKernel U q h = (finiteQuotient U p).ker := by
  have hex : ∃ p : ∀ i, ZMod (q i : ℕ) →+ ZMod (h : ℕ),
      ∀ᶠ i in U, ∀ n : ℕ, p i (n : ZMod (q i : ℕ)) = (n : ZMod (h : ℕ)) := ⟨p, hp⟩
  rw [naturalCyclicKernel, dite_eq_left hex,
    finiteQuotient_eq_of_eventually_natural U q h hex.choose p hex.choose_spec hp]

theorem positive_measurable_subgroup_eq_natural_kernel
    (U : Ultrafilter ℕ) (hU : (U : Filter ℕ) ≤ atTop) (q : ℕ → ℕ+)
    (H : AddSubgroup ((U : Filter ℕ).Product (fun n => ZMod (q n : ℕ))))
    (hH : MeasurableSet[loebMeasurableSpace U]
      (H : Set ((U : Filter ℕ).Product (fun n => ZMod (q n : ℕ)))))
    (hpos : 0 < loebMeasure U hU
      (H : Set ((U : Filter ℕ).Product (fun n => ZMod (q n : ℕ))))) :
    ∃ h : ℕ+, H = naturalCyclicKernel U q h ∧
      loebMeasure U hU (H : Set ((U : Filter ℕ).Product (fun n => ZMod (q n : ℕ)))) =
        1 / ((h : ℕ) : ℝ≥0∞) := by
  obtain ⟨h, p, hp, hker, hmass⟩ :=
    positive_measurable_subgroup_is_natural_finite_kernel U hU q H hH hpos
  refine ⟨h, ?_, hmass⟩
  exact hker.symm.trans (naturalCyclicKernel_eq U q h p (hp.mono (fun _ hi => hi.2))).symm

theorem measurable_naturalCyclicKernel
    (U : Ultrafilter ℕ) (q : ℕ → ℕ+) (h : ℕ+) :
    MeasurableSet[loebMeasurableSpace U]
      (naturalCyclicKernel U q h : Set ((U : Filter ℕ).Product (fun n => ZMod (q n : ℕ)))) := by
  classical
  by_cases hp : ∃ p : ∀ n, ZMod (q n : ℕ) →+ ZMod (h : ℕ),
      ∀ᶠ i in U, ∀ n : ℕ, p i (n : ZMod (q i : ℕ)) = (n : ZMod (h : ℕ))
  · rw [naturalCyclicKernel_eq U q h hp.choose hp.choose_spec, finiteQuotient_ker]
    exact measurable_internalSet U _
  · simp only [naturalCyclicKernel, dite_eq_right hp, AddSubgroup.coe_top]
    exact MeasurableSet.univ

theorem naturalCyclicKernel_measure_pos
    (U : Ultrafilter ℕ) (hU : (U : Filter ℕ) ≤ atTop) (q : ℕ → ℕ+) (h : ℕ+) :
    0 < loebMeasure U hU
      (naturalCyclicKernel U q h : Set ((U : Filter ℕ).Product (fun n => ZMod (q n : ℕ)))) := by
  classical
  by_cases hp : ∃ p : ∀ n, ZMod (q n : ℕ) →+ ZMod (h : ℕ),
      ∀ᶠ i in U, ∀ n : ℕ, p i (n : ZMod (q i : ℕ)) = (n : ZMod (h : ℕ))
  · let p := hp.choose
    have hsurj : ∀ᶠ i in U, Function.Surjective (p i) := by
      apply hp.choose_spec.mono
      intro i hi x
      refine ⟨(x.val : ZMod (q i : ℕ)), ?_⟩
      rw [hi]
      exact ZMod.natCast_zmod_val x
    rw [naturalCyclicKernel_eq U q h p hp.choose_spec, finiteQuotient_ker,
      loebMeasure_internalSubgroup_of_eventually_quotients U hU p hsurj]
    exact ENNReal.div_pos (by norm_num) (by simp)
  · simp only [naturalCyclicKernel, dite_eq_right hp, AddSubgroup.coe_top]
    rw [loebMeasure_univ]
    norm_num

end Erdos335.Loeb

end
