import Erdos335.LoebLiteralResidues

/-!
# Termination from a literal integer residue gap

Literal exhaustion supplies the lower bound on every finite-quotient
saturation. The quasi-periodic iteration theorem then gives a terminal
null active input or an internal Bohr pair.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter MeasureTheory
open scoped ENNReal Pointwise

noncomputable section

namespace Erdos335.Loeb

local instance literalGapTerminationLoebSpace (U : Ultrafilter ℕ) (q : ℕ → ℕ+) :
    MeasurableSpace ((U : Filter ℕ).Product (fun n => ZMod (q n : ℕ))) := loebMeasurableSpace U

theorem loeb_literal_exhaustion_saturation_gap
    (U : Ultrafilter ℕ) (hU : (U : Filter ℕ) ≤ atTop) (q : ℕ → ℕ+)
    (A : Set ℕ) (E : ℕ → Set ℕ)
    (hEA : ∀ᶠ n in U, E n ⊆ A)
    (hexhaust : ∀ a ∈ A, ∀ᶠ n in U, a ∈ E n)
    (α δ : ℝ)
    (hmass : (loebMeasure U hU
      (internalSet U (fun n => ((↑) : ℕ → ZMod (q n : ℕ)) '' E n))).toReal = α)
    (hcapacity : ∀ h : ℕ+, α + δ ≤ ((residues (h : ℕ) A).card : ℝ) / (h : ℕ))
    (H : AddSubgroup ((U : Filter ℕ).Product (fun n => ZMod (q n : ℕ))))
    (hHm : MeasurableSet (H : Set ((U : Filter ℕ).Product (fun n => ZMod (q n : ℕ)))))
    (hHpos : 0 < loebMeasure U hU (H : Set ((U : Filter ℕ).Product (fun n => ZMod (q n : ℕ))))) :
    δ ≤ (loebMeasure U hU
      ((internalSet U (fun n => ((↑) : ℕ → ZMod (q n : ℕ)) '' E n)) + (H : Set _))).toReal -
      (loebMeasure U hU (internalSet U (fun n => ((↑) : ℕ → ZMod (q n : ℕ)) '' E n))).toReal := by
  obtain ⟨h, p, hp, hker, _⟩ :=
    positive_measurable_subgroup_is_natural_finite_kernel U hU q H hHm hHpos
  have hsat := loeb_literal_exhaustion_saturation_measure U hU q A E hEA hexhaust h p hp
  rw [hker] at hsat
  rw [hsat, ENNReal.toReal_div, ENNReal.toReal_natCast, ENNReal.toReal_natCast, hmass]
  linarith [hcapacity h]

theorem loeb_literal_exhaustion_inverse
    (U : Ultrafilter ℕ) (hU : (U : Filter ℕ) ≤ atTop) (q : ℕ → ℕ+)
    (A : Set ℕ) (E : ℕ → Set ℕ)
    (hEA : ∀ᶠ n in U, E n ⊆ A)
    (hexhaust : ∀ a ∈ A, ∀ᶠ n in U, a ∈ E n)
    (B : Set ((U : Filter ℕ).Product (fun n => ZMod (q n : ℕ))))
    (α δ : ℝ) (hα : 0 < α) (hδ : 0 < δ)
    (hmass : (loebMeasure U hU
      (internalSet U (fun n => ((↑) : ℕ → ZMod (q n : ℕ)) '' E n))).toReal = α)
    (hcapacity : ∀ h : ℕ+, α + δ ≤ ((residues (h : ℕ) A).card : ℝ) / (h : ℕ))
    (hBm : MeasurableSet B) (hBpos : 0 < loebMeasure U hU B)
    (hSm : MeasurableSet ((internalSet U (fun n => ((↑) : ℕ → ZMod (q n : ℕ)) '' E n)) + B))
    (hfull : loebMeasure U hU
      ((internalSet U (fun n => ((↑) : ℕ → ZMod (q n : ℕ)) '' E n)) + B) =
        loebMeasure U hU (internalSet U (fun n => ((↑) : ℕ → ZMod (q n : ℕ)) '' E n)) +
          loebMeasure U hU B)
    (hnoAE : ∀ H : AddSubgroup ((U : Filter ℕ).Product (fun n => ZMod (q n : ℕ))),
      MeasurableSet (H : Set ((U : Filter ℕ).Product (fun n => ZMod (q n : ℕ)))) →
      0 < loebMeasure U hU (H : Set ((U : Filter ℕ).Product (fun n => ZMod (q n : ℕ)))) →
      ¬ ∀ t ∈ H, t +ᵥ ((internalSet U (fun n => ((↑) : ℕ → ZMod (q n : ℕ)) '' E n)) + B)
        =ᵐ[loebMeasure U hU] (internalSet U (fun n => ((↑) : ℕ → ZMod (q n : ℕ)) '' E n)) + B) :
    Nonempty (InternalBohrPairData U hU q
      (internalSet U (fun n => ((↑) : ℕ → ZMod (q n : ℕ)) '' E n)) B) ∨
      ∃ p : QuasiPeriodicPairData (loebMeasure U hU) (internalInnerMeasure U hU)
        (internalSet U (fun n => ((↑) : ℕ → ZMod (q n : ℕ)) '' E n)) B,
        loebMeasure U hU p.left.active = 0 ∨ loebMeasure U hU p.right.active = 0 ∨
          Nonempty (InternalBohrPairData U hU q p.left.active p.right.active) := by
  let C := internalSet U (fun n => ((↑) : ℕ → ZMod (q n : ℕ)) '' E n)
  have hCm : MeasurableSet C := measurable_internalSet U _
  have hCpos : 0 < loebMeasure U hU C := by
    apply pos_iff_ne_zero.mpr
    intro hz
    change (loebMeasure U hU C).toReal = α at hmass
    rw [hz, ENNReal.toReal_zero] at hmass
    linarith
  apply loeb_aperiodic_inverse_of_saturation_gap U hU q C B hCm hBm hSm hCpos hBpos hfull hnoAE δ hδ
  exact loeb_literal_exhaustion_saturation_gap U hU q A E hEA hexhaust α δ hmass hcapacity

end Erdos335.Loeb

end
