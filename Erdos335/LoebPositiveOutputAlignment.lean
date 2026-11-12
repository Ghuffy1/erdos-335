import Erdos335.LoebPhysicalBohrOutput
import Erdos335.PartialResidueProfileAlignment

/-!
# Matching positive terminal moduli across common actual output windows
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Filter Set MeasureTheory
open Erdos335.IntermediateScale
open scoped Pointwise ENNReal

noncomputable section

namespace Erdos335.Loeb

local instance positiveOutputAlignmentLoebSpace (U : Ultrafilter ℕ) (q : ℕ → ℕ+) :
    MeasurableSpace ((U : Filter ℕ).Product (fun n => ZMod (q n : ℕ))) := loebMeasurableSpace U

theorem positive_terminal_output_moduli_agree
    (U : Ultrafilter ℕ) (hU : (U : Filter ℕ) ≤ atTop) (q : Bool → ℕ → ℕ+)
    (hdiv : ∀ i, ∀ h : ℕ+, ∀ᶠ n in U, (h : ℕ) ∣ (q i n : ℕ))
    (A B : ∀ i, Set ((U : Filter ℕ).Product (fun n => ZMod (q i n : ℕ))))
    (p : ∀ i, QuasiPeriodicPairData (loebMeasure U hU) (internalInnerMeasure U hU) (A i) (B i))
    (hSm : ∀ i, MeasurableSet (A i + B i))
    (b : ∀ i, InternalBohrPairData U hU (q i) (p i).left.active (p i).right.active)
    (hperiod : ∀ i, (p i).period = (finiteQuotient U (b i).residue).ker)
    (C : Set ℕ) (start : ℕ → ℕ)
    (hmodel : ∀ i, A i + B i =ᵐ[loebMeasure U hU] internalSet U
      (fun n => (cyclicWindow C (start n) (q i n : ℕ) : Set (ZMod (q i n : ℕ)))))
    (hagree : ∀ h : ℕ+, ∀ r : ZMod (h : ℕ),
      actualWindowProfile U hU (q false) h C start r = actualWindowProfile U hU (q true) h C start r) :
    (b false).modulus = (b true).modulus ∧
      (b false).left_length + (b false).right_length = (b true).left_length + (b true).right_length := by
  classical
  let m := (b false).modulus
  let k := (b true).modulus
  let N := m * k
  have hmN : (m : ℕ) ∣ (N : ℕ) := ⟨k, rfl⟩
  have hkN : (k : ℕ) ∣ (N : ℕ) := ⟨m, Nat.mul_comm _ _⟩
  let R (i : Bool) := ((finiteQuotient U (b i).residue) '' (A i + B i)).toFinite.toFinset
  have hR (i : Bool) : (finiteQuotient U (b i).residue) '' (A i + B i) = (R i : Set _) := by
    ext r
    simp [R]
  let z (i : Bool) := finiteValue U (fun n => (start n : ZMod ((b i).modulus : ℕ)))
  let s := finiteQuotient U (b false).residue ((b false).left_anchor + (b false).right_anchor) + z false
  let t := finiteQuotient U (b true).residue ((b true).left_anchor + (b true).right_anchor) + z true
  let S := (R false).image (fun r => r + z false)
  let T := (R true).image (fun r => r + z true)
  have hfalse (r : ZMod (N : ℕ)) : actualWindowProfile U hU (q false) N C start r =
      if naturalCyclicProjection N m r = s then (b false).left_length + (b false).right_length
      else if naturalCyclicProjection N m r ∈ S then 1 else 0 :=
    loeb_physical_bohr_output_profile U hU (q false) (A false) (B false) (p false) (hSm false)
      (b false) (hperiod false) C start (hmodel false) (R false) (hR false) N (hdiv false N) hmN r
  have htrue (r : ZMod (N : ℕ)) : actualWindowProfile U hU (q false) N C start r =
      if naturalCyclicProjection N k r = t then (b true).left_length + (b true).right_length
      else if naturalCyclicProjection N k r ∈ T then 1 else 0 :=
    (hagree N r).trans (loeb_physical_bohr_output_profile U hU (q true) (A true) (B true) (p true) (hSm true)
      (b true) (hperiod true) C start (hmodel true) (R true) (hR true) N (hdiv true N) hkN r)
  obtain ⟨hmk, hlength, _⟩ := partial_residue_profile_alignment N m k hmN hkN s t S T
    ((b false).left_length + (b false).right_length) ((b true).left_length + (b true).right_length)
    (add_pos (b false).left_positive (b false).right_positive) (b false).length_sum_lt_one
    (add_pos (b true).left_positive (b true).right_positive) (b true).length_sum_lt_one
    (actualWindowProfile U hU (q false) N C start) hfalse htrue
  exact ⟨hmk, hlength⟩

end Erdos335.Loeb

end
