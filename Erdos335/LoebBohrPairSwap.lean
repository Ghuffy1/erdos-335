import Erdos335.LoebInternalBohrPair

/-!
# Exchanging the two inputs of an internal Bohr model
-/

set_option autoImplicit false

open Filter Set MeasureTheory

noncomputable section

namespace Erdos335.Loeb

def InternalBohrPairData.swap
    {U : Ultrafilter ℕ} {hU : (U : Filter ℕ) ≤ atTop} {q : ℕ → ℕ+}
    {A B : Set ((U : Filter ℕ).Product (fun n => ZMod (q n : ℕ)))}
    (b : InternalBohrPairData U hU q A B) : InternalBohrPairData U hU q B A where
  modulus := b.modulus
  residue := b.residue
  natural_residue := b.natural_residue
  character := b.character
  character_surjective := b.character_surjective
  left_anchor := b.right_anchor
  right_anchor := b.left_anchor
  left_start := b.right_start
  right_start := b.left_start
  left_length := b.right_length
  right_length := b.left_length
  left_positive := b.right_positive
  right_positive := b.left_positive
  length_sum_lt_one := by linarith [b.length_sum_lt_one]
  left_containment := b.right_containment
  right_containment := b.left_containment
  left_model := b.right_model
  right_model := b.left_model

end Erdos335.Loeb

end
