import Erdos335.LoebInternalBohrCosets

/-!
# Internal Bohr pair data for the Loeb inverse theorem
-/

set_option autoImplicit false

open Set Filter MeasureTheory
open scoped ENNReal Pointwise

noncomputable section

namespace Erdos335.Loeb

def internalBohrCoset (U : Ultrafilter ℕ) (q : ℕ → ℕ+)
    (m : ℕ+) (p : ∀ n, ZMod (q n : ℕ) →+ ZMod (m : ℕ))
    (χ : ∀ n, ZMod (q n : ℕ) →+ AddCircle (1 : ℝ))
    (a : (U : Filter ℕ).Product (fun n => ZMod (q n : ℕ)))
    (x : AddCircle (1 : ℝ)) (r : ℝ) :
    Set ((U : Filter ℕ).Product (fun n => ZMod (q n : ℕ))) :=
  (a +ᵥ ((finiteQuotient U p).ker : Set ((U : Filter ℕ).Product (fun n => ZMod (q n : ℕ))))) ∩
    (ultralimitAddHom U χ) ⁻¹' (x +ᵥ (((↑) : ℝ → AddCircle (1 : ℝ)) '' Icc 0 r))

local instance internalBohrPairLoebSpace (U : Ultrafilter ℕ) (q : ℕ → ℕ+) :
    MeasurableSpace ((U : Filter ℕ).Product (fun n => ZMod (q n : ℕ))) := loebMeasurableSpace U

structure InternalBohrPairData
    (U : Ultrafilter ℕ) (hU : (U : Filter ℕ) ≤ atTop) (q : ℕ → ℕ+)
    (A B : Set ((U : Filter ℕ).Product (fun n => ZMod (q n : ℕ)))) where
  modulus : ℕ+
  residue : ∀ n, ZMod (q n : ℕ) →+ ZMod (modulus : ℕ)
  natural_residue : ∀ᶠ n in U, Function.Surjective (residue n) ∧
    ∀ k : ℕ, residue n (k : ZMod (q n : ℕ)) = (k : ZMod (modulus : ℕ))
  character : ∀ n, ZMod (q n : ℕ) →+ AddCircle (1 : ℝ)
  character_surjective : Function.Surjective (ultralimitAddHom U character)
  left_anchor : (U : Filter ℕ).Product (fun n => ZMod (q n : ℕ))
  right_anchor : (U : Filter ℕ).Product (fun n => ZMod (q n : ℕ))
  left_start : AddCircle (1 : ℝ)
  right_start : AddCircle (1 : ℝ)
  left_length : ℝ
  right_length : ℝ
  left_positive : 0 < left_length
  right_positive : 0 < right_length
  length_sum_lt_one : left_length + right_length < 1
  left_containment : A ⊆ internalBohrCoset U q modulus residue character left_anchor left_start left_length
  right_containment : B ⊆ internalBohrCoset U q modulus residue character right_anchor right_start right_length
  left_model : A =ᵐ[loebMeasure U hU]
    internalBohrCoset U q modulus residue character left_anchor left_start left_length
  right_model : B =ᵐ[loebMeasure U hU]
    internalBohrCoset U q modulus residue character right_anchor right_start right_length

end Erdos335.Loeb

end
