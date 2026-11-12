import Erdos335.LoebLiteralGapTermination

/-!
# The inverse alternative for a literal prefix model
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Filter Set MeasureTheory
open scoped Pointwise ENNReal

noncomputable section

namespace Erdos335.Loeb

local instance literalModelInverseLoebSpace (U : Ultrafilter ℕ) (q : ℕ → ℕ+) :
    MeasurableSpace ((U : Filter ℕ).Product (fun n => ZMod (q n : ℕ))) := loebMeasurableSpace U

theorem loeb_literal_model_inverse
    (U : Ultrafilter ℕ) (hU : (U : Filter ℕ) ≤ atTop) (q : ℕ → ℕ+)
    (A : Set ℕ) (E : ℕ → Set ℕ) (W : ∀ n, Set (ZMod (q n : ℕ)))
    (hEA : ∀ᶠ n in U, E n ⊆ A)
    (hexhaust : ∀ a ∈ A, ∀ᶠ n in U, a ∈ E n)
    (a b δ : ℝ) (ha : 0 < a) (hb : 0 < b) (hδ : 0 < δ)
    (hE : (loebMeasure U hU
      (internalSet U (fun n => ((↑) : ℕ → ZMod (q n : ℕ)) '' E n))).toReal = a)
    (hW : (loebMeasure U hU (internalSet U W)).toReal = b)
    (hcapacity : ∀ h : ℕ+, a + δ ≤ ((residues (h : ℕ) A).card : ℝ) / (h : ℕ))
    (hsum : (loebMeasure U hU
      (internalSet U (fun n => ((↑) : ℕ → ZMod (q n : ℕ)) '' E n) + internalSet U W)).toReal ≤ a + b) :
    let C := internalSet U (fun n => ((↑) : ℕ → ZMod (q n : ℕ)) '' E n)
    let D := internalSet U W
    (∃ H : AddSubgroup ((U : Filter ℕ).Product (fun n => ZMod (q n : ℕ))),
      MeasurableSet (H : Set ((U : Filter ℕ).Product (fun n => ZMod (q n : ℕ)))) ∧
      0 < loebMeasure U hU (H : Set ((U : Filter ℕ).Product (fun n => ZMod (q n : ℕ)))) ∧
      ∀ t ∈ H, t +ᵥ (C + D) =ᵐ[loebMeasure U hU] C + D) ∨
    Nonempty (InternalBohrPairData U hU q C D) ∨
    ∃ p : QuasiPeriodicPairData (loebMeasure U hU) (internalInnerMeasure U hU) C D,
      loebMeasure U hU p.left.active = 0 ∨ loebMeasure U hU p.right.active = 0 ∨
        Nonempty (InternalBohrPairData U hU q p.left.active p.right.active) := by
  dsimp only
  let C := internalSet U (fun n => ((↑) : ℕ → ZMod (q n : ℕ)) '' E n)
  let D := internalSet U W
  let μ := loebMeasure (X := fun n => ZMod (q n : ℕ)) U hU
  letI : IsProbabilityMeasure μ := isProbabilityMeasure_loebMeasure U hU
  have hCm : MeasurableSet C := measurable_internalSet U _
  have hDm : MeasurableSet D := measurable_internalSet U _
  have hSm : MeasurableSet (C + D) := by
    rw [show C + D = internalSet U
      (fun n => (((↑) : ℕ → ZMod (q n : ℕ)) '' E n) + W n) from (internalSet_add U _ _).symm]
    exact measurable_internalSet U _
  have hCpos : 0 < μ C := by
    apply pos_iff_ne_zero.mpr
    intro hz
    change (μ C).toReal = a at hE
    rw [hz, ENNReal.toReal_zero] at hE
    linarith
  have hDpos : 0 < μ D := by
    apply pos_iff_ne_zero.mpr
    intro hz
    change (μ D).toReal = b at hW
    rw [hz, ENNReal.toReal_zero] at hW
    linarith
  by_cases hperiod : ∃ H : AddSubgroup ((U : Filter ℕ).Product (fun n => ZMod (q n : ℕ))),
      MeasurableSet (H : Set ((U : Filter ℕ).Product (fun n => ZMod (q n : ℕ)))) ∧
      0 < μ (H : Set ((U : Filter ℕ).Product (fun n => ZMod (q n : ℕ)))) ∧
      ∀ t ∈ H, t +ᵥ (C + D) =ᵐ[μ] C + D
  · exact Or.inl hperiod
  have hnoAE : ∀ H : AddSubgroup ((U : Filter ℕ).Product (fun n => ZMod (q n : ℕ))),
      MeasurableSet (H : Set ((U : Filter ℕ).Product (fun n => ZMod (q n : ℕ)))) →
      0 < μ (H : Set ((U : Filter ℕ).Product (fun n => ZMod (q n : ℕ)))) →
      ¬ ∀ t ∈ H, t +ᵥ (C + D) =ᵐ[μ] C + D := by
    intro H hHm hHpos hp
    exact hperiod ⟨H, hHm, hHpos, hp⟩
  have hfullReal : (μ (C + D)).toReal = a + b := by
    apply le_antisymm hsum
    by_contra hn
    have hsmall : μ (C + D) < μ C + μ D := by
      apply (ENNReal.toReal_lt_toReal (measure_ne_top μ _) (by finiteness)).mp
      rw [ENNReal.toReal_add (measure_ne_top μ _) (measure_ne_top μ _), hE, hW]
      exact lt_of_not_ge hn
    let H := AddAction.stabilizer ((U : Filter ℕ).Product (fun n => ZMod (q n : ℕ))) (C + D)
    have hHpos : 0 < μ (H : Set _) := by
      have hp := subcritical_stabilizer_positive U hU
        (fun n => ((↑) : ℕ → ZMod (q n : ℕ)) '' E n) W
        (nonempty_of_measure_ne_zero hCpos.ne') (nonempty_of_measure_ne_zero hDpos.ne')
      rw [internalSet_add] at hp
      exact hp hsmall
    have hHm : MeasurableSet
        (H : Set ((U : Filter ℕ).Product (fun n => ZMod (q n : ℕ)))) := by
      change MeasurableSet
        (AddAction.stabilizer ((U : Filter ℕ).Product (fun n => ZMod (q n : ℕ)))
          (C + D) : Set ((U : Filter ℕ).Product (fun n => ZMod (q n : ℕ))))
      rw [show C + D = internalSet U
        (fun n => (((↑) : ℕ → ZMod (q n : ℕ)) '' E n) + W n) from (internalSet_add U _ _).symm,
        ← internalAddSubgroup_stabilizer]
      exact measurable_internalSet U _
    exact hnoAE H hHm hHpos (fun t ht => Filter.EventuallyEq.of_eq ht)
  have hfull : μ (C + D) = μ C + μ D := by
    apply (ENNReal.toReal_eq_toReal_iff' (measure_ne_top μ _) (by finiteness)).mp
    rw [ENNReal.toReal_add (measure_ne_top μ _) (measure_ne_top μ _), hE, hW]
    exact hfullReal
  exact Or.inr (loeb_literal_exhaustion_inverse U hU q A E hEA hexhaust D a δ ha hδ hE
    hcapacity hDm hDpos hSm hfull hnoAE)

end Erdos335.Loeb

end
