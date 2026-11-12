import Erdos335.LoebSaturationGap

/-!
# The measurable aperiodic inverse with quantitative termination

The active sum inherits the absence of positive essential periods even
when the original pair is reducible. Refinement stops at a null active
input or a Bohr active pair if an input has a positive saturation gap.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter MeasureTheory
open scoped ENNReal Pointwise

noncomputable section

namespace Erdos335.Loeb

local instance generalInverseIterationLoebSpace (U : Ultrafilter ℕ) (q : ℕ → ℕ+) :
    MeasurableSpace ((U : Filter ℕ).Product (fun n => ZMod (q n : ℕ))) := loebMeasurableSpace U

theorem loeb_quasiPeriodic_active_aperiodic
    (U : Ultrafilter ℕ) (hU : (U : Filter ℕ) ≤ atTop) (q : ℕ → ℕ+)
    (A B : Set ((U : Filter ℕ).Product (fun n => ZMod (q n : ℕ))))
    (p : QuasiPeriodicPairData (loebMeasure U hU) (internalInnerMeasure U hU) A B)
    (hSm : MeasurableSet (A + B))
    (hnoAE : ∀ H : AddSubgroup ((U : Filter ℕ).Product (fun n => ZMod (q n : ℕ))),
      MeasurableSet (H : Set ((U : Filter ℕ).Product (fun n => ZMod (q n : ℕ)))) →
      0 < loebMeasure U hU (H : Set ((U : Filter ℕ).Product (fun n => ZMod (q n : ℕ)))) →
      ¬ ∀ t ∈ H, t +ᵥ (A + B) =ᵐ[loebMeasure U hU] A + B) :
    MeasurableSet (p.left.active + p.right.active) ∧
      ∀ H : AddSubgroup ((U : Filter ℕ).Product (fun n => ZMod (q n : ℕ))),
        MeasurableSet (H : Set ((U : Filter ℕ).Product (fun n => ZMod (q n : ℕ)))) →
        0 < loebMeasure U hU (H : Set ((U : Filter ℕ).Product (fun n => ZMod (q n : ℕ)))) →
        ¬ ∀ t ∈ H, t +ᵥ (p.left.active + p.right.active) =ᵐ[loebMeasure U hU]
          p.left.active + p.right.active := by
  let G := (U : Filter ℕ).Product (fun n => ZMod (q n : ℕ))
  let μ := loebMeasure (X := fun n => ZMod (q n : ℕ)) U hU
  let T := (p.left.background + B) ∪ (A + p.right.background)
  let R := p.left.active + p.right.active
  have hsplit : A + B = T ∪ R := p.sum_partition
  obtain ⟨hTm, hTp⟩ := loeb_quasiPeriodic_background U hU q A B (internalInnerMeasure U hU) p
  constructor
  · rw [p.active_sum_eq_inter]
    exact hSm.inter (measurable_loeb_translate U hU _ p.period_measurable _)
  · intro H hHm hHpos hp
    obtain ⟨hJm, hJpos⟩ := loeb_positive_subgroup_intersection U hU q p.period H
      p.period_measurable hHm p.period_positive hHpos
    apply hnoAE (p.period ⊓ H) hJm hJpos
    intro t ht
    have hleft := loeb_translate_ae_of_essential_period U hU q T hTm p.period
      (ae_le_set.mp hTp.le) t ht.1
    have hright := hp t ht.2
    rw [hsplit, vadd_set_union]
    filter_upwards [hleft, hright] with x hx hy
    change (x ∈ t +ᵥ T ∨ x ∈ t +ᵥ R) = (x ∈ T ∨ x ∈ R)
    rw [hx, hy]

theorem loeb_aperiodic_inverse_iteration_alternative
    (U : Ultrafilter ℕ) (hU : (U : Filter ℕ) ≤ atTop) (q : ℕ → ℕ+)
    (A B : Set ((U : Filter ℕ).Product (fun n => ZMod (q n : ℕ))))
    (hAm : MeasurableSet A) (hBm : MeasurableSet B) (hSm : MeasurableSet (A + B))
    (hApos : 0 < loebMeasure U hU A) (hBpos : 0 < loebMeasure U hU B)
    (hfull : loebMeasure U hU (A + B) = loebMeasure U hU A + loebMeasure U hU B)
    (hnoAE : ∀ H : AddSubgroup ((U : Filter ℕ).Product (fun n => ZMod (q n : ℕ))),
      MeasurableSet (H : Set ((U : Filter ℕ).Product (fun n => ZMod (q n : ℕ)))) →
      0 < loebMeasure U hU (H : Set ((U : Filter ℕ).Product (fun n => ZMod (q n : ℕ)))) →
      ¬ ∀ t ∈ H, t +ᵥ (A + B) =ᵐ[loebMeasure U hU] A + B) :
    Nonempty (InternalBohrPairData U hU q A B) ∨
      (∃ p : QuasiPeriodicPairData (loebMeasure U hU) (internalInnerMeasure U hU) A B,
        loebMeasure U hU p.left.active = 0 ∨ loebMeasure U hU p.right.active = 0 ∨
          Nonempty (InternalBohrPairData U hU q p.left.active p.right.active)) ∨
      ∀ ε : ℝ, 0 < ε →
        ∃ p : QuasiPeriodicPairData (loebMeasure U hU) (internalInnerMeasure U hU) A B,
          (loebMeasure (X := fun n => ZMod (q n : ℕ)) U hU (p.period : Set _)).toReal < ε := by
  classical
  rcases loeb_aperiodic_equality_quasiPeriodic_or_internalBohr U hU q A B
    hAm hBm hSm hApos hBpos hfull hnoAE with hqp | hbohr
  · obtain ⟨p⟩ := hqp
    right
    by_cases hterminal : ∃ r : QuasiPeriodicPairData (loebMeasure U hU)
        (internalInnerMeasure U hU) A B,
        loebMeasure U hU r.left.active = 0 ∨ loebMeasure U hU r.right.active = 0 ∨
          Nonempty (InternalBohrPairData U hU q r.left.active r.right.active)
    · exact Or.inl hterminal
    · right
      apply loeb_quasiPeriodic_arbitrarily_small_of_refinable U hU q A B p
      intro r
      have hleft : 0 < loebMeasure U hU r.left.active := by
        apply pos_iff_ne_zero.mpr
        intro hz
        exact hterminal ⟨r, Or.inl hz⟩
      have hright : 0 < loebMeasure U hU r.right.active := by
        apply pos_iff_ne_zero.mpr
        intro hz
        exact hterminal ⟨r, Or.inr (Or.inl hz)⟩
      obtain ⟨hactive, hperiods⟩ := loeb_quasiPeriodic_active_aperiodic U hU q A B r hSm hnoAE
      have hactivefull : loebMeasure U hU (r.left.active + r.right.active) =
          loebMeasure U hU r.left.active + loebMeasure U hU r.right.active := by
        rw [← internalInnerMeasure_eq U hU _ hactive]
        exact r.active_identity
      rcases loeb_aperiodic_equality_quasiPeriodic_or_internalBohr U hU q
        r.left.active r.right.active r.left.active_measurable r.right.active_measurable
        hactive hleft hright hactivefull hperiods with hrefine | hbohr
      · exact hrefine
      · exact False.elim (hterminal ⟨r, Or.inr (Or.inr hbohr)⟩)
  · exact Or.inl hbohr

theorem loeb_aperiodic_inverse_of_saturation_gap
    (U : Ultrafilter ℕ) (hU : (U : Filter ℕ) ≤ atTop) (q : ℕ → ℕ+)
    (A B : Set ((U : Filter ℕ).Product (fun n => ZMod (q n : ℕ))))
    (hAm : MeasurableSet A) (hBm : MeasurableSet B) (hSm : MeasurableSet (A + B))
    (hApos : 0 < loebMeasure U hU A) (hBpos : 0 < loebMeasure U hU B)
    (hfull : loebMeasure U hU (A + B) = loebMeasure U hU A + loebMeasure U hU B)
    (hnoAE : ∀ H : AddSubgroup ((U : Filter ℕ).Product (fun n => ZMod (q n : ℕ))),
      MeasurableSet (H : Set ((U : Filter ℕ).Product (fun n => ZMod (q n : ℕ)))) →
      0 < loebMeasure U hU (H : Set ((U : Filter ℕ).Product (fun n => ZMod (q n : ℕ)))) →
      ¬ ∀ t ∈ H, t +ᵥ (A + B) =ᵐ[loebMeasure U hU] A + B)
    (δ : ℝ) (hδ : 0 < δ)
    (hgap : ∀ H : AddSubgroup ((U : Filter ℕ).Product (fun n => ZMod (q n : ℕ))),
      MeasurableSet (H : Set ((U : Filter ℕ).Product (fun n => ZMod (q n : ℕ)))) →
      0 < loebMeasure U hU (H : Set ((U : Filter ℕ).Product (fun n => ZMod (q n : ℕ)))) →
      δ ≤ (loebMeasure U hU (A + (H : Set _))).toReal - (loebMeasure U hU A).toReal) :
    Nonempty (InternalBohrPairData U hU q A B) ∨
      ∃ p : QuasiPeriodicPairData (loebMeasure U hU) (internalInnerMeasure U hU) A B,
        loebMeasure U hU p.left.active = 0 ∨ loebMeasure U hU p.right.active = 0 ∨
          Nonempty (InternalBohrPairData U hU q p.left.active p.right.active) := by
  rcases loeb_aperiodic_inverse_iteration_alternative U hU q A B hAm hBm hSm
    hApos hBpos hfull hnoAE with hdirect | hterminal | hsmall
  · exact Or.inl hdirect
  · exact Or.inr hterminal
  · obtain ⟨p, hp⟩ := hsmall δ hδ
    have hbound := loeb_quasiPeriodic_period_bound_of_saturation_gap U hU q A p.period
      p.left δ (hgap p.period p.period_measurable p.period_positive)
    exact False.elim (not_lt_of_ge hbound hp)

end Erdos335.Loeb

end
