import Erdos335.LoebBohrPeriodContainment

/-!
# Absorbing the terminal Bohr modulus into a quasi-periodic pair
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter MeasureTheory
open scoped ENNReal Pointwise

noncomputable section

namespace Erdos335.Loeb

local instance bohrPeriodAlignmentLoebSpace (U : Ultrafilter ℕ) (q : ℕ → ℕ+) :
    MeasurableSpace ((U : Filter ℕ).Product (fun n => ZMod (q n : ℕ))) := loebMeasurableSpace U

theorem loeb_quasiPeriodic_internalBohr_period_alignment
    (U : Ultrafilter ℕ) (hU : (U : Filter ℕ) ≤ atTop) (q : ℕ → ℕ+)
    (A B : Set ((U : Filter ℕ).Product (fun n => ZMod (q n : ℕ))))
    (p : QuasiPeriodicPairData (loebMeasure U hU) (internalInnerMeasure U hU) A B)
    (b : InternalBohrPairData U hU q p.left.active p.right.active) :
    ∃ r : QuasiPeriodicPairData (loebMeasure U hU) (internalInnerMeasure U hU) A B,
      r.period = (finiteQuotient U b.residue).ker ∧
      r.left.active = p.left.active ∧ r.right.active = p.right.active ∧
      r.left.anchor = b.left_anchor ∧ r.right.anchor = b.right_anchor := by
  let G := (U : Filter ℕ).Product (fun n => ZMod (q n : ℕ))
  let μ := loebMeasure (X := fun n => ZMod (q n : ℕ)) U hU
  let K := (finiteQuotient U b.residue).ker
  let φ := ultralimitAddHom U b.character
  let S := b.left_start +ᵥ (((↑) : ℝ → AddCircle (1 : ℝ)) '' Icc 0 b.left_length)
  have hKm : MeasurableSet (K : Set G) := by
    rw [show (K : Set G) = internalSet U (fun n => ((b.residue n).ker : Set (ZMod (q n : ℕ)))) from
      congrArg (fun J : AddSubgroup G => (J : Set G)) (finiteQuotient_ker U b.residue)]
    exact measurable_internalSet U _
  have hKpos : 0 < μ (K : Set G) := by
    rw [show (K : Set G) = internalSet U (fun n => ((b.residue n).ker : Set (ZMod (q n : ℕ)))) from
      congrArg (fun J : AddSubgroup G => (J : Set G)) (finiteQuotient_ker U b.residue)]
    change 0 < loebMeasure U hU (internalAddSubgroup U (fun n => (b.residue n).ker) : Set G)
    rw [loebMeasure_internalSubgroup_of_eventually_quotients U hU b.residue
      (b.natural_residue.mono fun _ hn => hn.1)]
    exact ENNReal.div_pos (by norm_num) (by simp)
  have hSm : MeasurableSet S := by
    dsimp only [S]
    rw [vadd_set_eq_neg_preimage]
    exact (isCompact_Icc.image (AddCircle.continuous_mk' 1)).isClosed.measurableSet.preimage
      (measurable_const_add _)
  have hSpos : 0 < volume S := by
    rw [show S = b.left_start +ᵥ (((↑) : ℝ → AddCircle (1 : ℝ)) '' Icc 0 b.left_length) from rfl,
      volume_unitCircle_normalized_closedArc b.left_start b.left_length
        (by linarith [b.length_sum_lt_one, b.right_positive])]
    exact ENNReal.ofReal_pos.mpr b.left_positive
  have hcontain : (b.left_anchor +ᵥ (K : Set G)) ∩ φ ⁻¹' S ≤ᵐ[μ]
      p.left.anchor +ᵥ (p.period : Set G) := by
    have hmodel : p.left.active =ᵐ[μ] (b.left_anchor +ᵥ (K : Set G)) ∩ φ ⁻¹' S := b.left_model
    exact hmodel.symm.le.trans p.left.active_subset_coset.eventuallySubset
  have hKH : K ≤ p.period := loeb_circle_coset_period_le_of_ae_containment U hU q φ
    (measurable_ultralimitAddHom U b.character) b.character_surjective p.period K
    p.period_measurable hKm p.period_positive hKpos S hSm hSpos
    p.left.anchor b.left_anchor hcontain
  have hleft : p.left.active ⊆ b.left_anchor +ᵥ (K : Set G) :=
    b.left_containment.trans inter_subset_left
  have hright : p.right.active ⊆ b.right_anchor +ᵥ (K : Set G) :=
    b.right_containment.trans inter_subset_left
  let r := p.restrictPeriod K hKm hKpos hKH b.left_anchor b.right_anchor hleft hright
  exact ⟨r, rfl, rfl, rfl, rfl, rfl⟩

end Erdos335.Loeb

end
