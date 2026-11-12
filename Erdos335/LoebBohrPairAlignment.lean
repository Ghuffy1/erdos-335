import Erdos335.LoebBohrPeriodAlignment

/-!
# Keeping the Bohr data when its containing finite period is aligned
-/

set_option autoImplicit false

open Filter Set MeasureTheory

noncomputable section

namespace Erdos335.Loeb

def InternalBohrPairData.congr
    {U : Ultrafilter ℕ} {hU : (U : Filter ℕ) ≤ atTop} {q : ℕ → ℕ+}
    {A B A' B' : Set ((U : Filter ℕ).Product (fun n => ZMod (q n : ℕ)))}
    (b : InternalBohrPairData U hU q A B) (hA : A' = A) (hB : B' = B) :
    InternalBohrPairData U hU q A' B' where
  modulus := b.modulus
  residue := b.residue
  natural_residue := b.natural_residue
  character := b.character
  character_surjective := b.character_surjective
  left_anchor := b.left_anchor
  right_anchor := b.right_anchor
  left_start := b.left_start
  right_start := b.right_start
  left_length := b.left_length
  right_length := b.right_length
  left_positive := b.left_positive
  right_positive := b.right_positive
  length_sum_lt_one := b.length_sum_lt_one
  left_containment := by simpa only [hA] using b.left_containment
  right_containment := by simpa only [hB] using b.right_containment
  left_model := by simpa only [hA] using b.left_model
  right_model := by simpa only [hB] using b.right_model

local instance bohrPairAlignmentLoebSpace (U : Ultrafilter ℕ) (q : ℕ → ℕ+) :
    MeasurableSpace ((U : Filter ℕ).Product (fun n => ZMod (q n : ℕ))) := loebMeasurableSpace U

theorem exists_aligned_quasiPeriodicBohrPair
    (U : Ultrafilter ℕ) (hU : (U : Filter ℕ) ≤ atTop) (q : ℕ → ℕ+)
    (A B : Set ((U : Filter ℕ).Product (fun n => ZMod (q n : ℕ))))
    (p : QuasiPeriodicPairData (loebMeasure U hU) (internalInnerMeasure U hU) A B)
    (b : InternalBohrPairData U hU q p.left.active p.right.active) :
    ∃ (r : QuasiPeriodicPairData (loebMeasure U hU) (internalInnerMeasure U hU) A B)
      (d : InternalBohrPairData U hU q r.left.active r.right.active),
      r.period = (finiteQuotient U d.residue).ker := by
  obtain ⟨r, hperiod, hleft, hright, _, _⟩ := loeb_quasiPeriodic_internalBohr_period_alignment U hU q A B p b
  exact ⟨r, b.congr hleft hright, hperiod⟩

end Erdos335.Loeb

end
