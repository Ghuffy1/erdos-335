import Erdos335.ApproximateCoverEquality
import Erdos335.LoebWindowMaskBounds
import Erdos335.LoebLiteralResidues

/-!
# Prefix and physical window models agree for a residue-regular input
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Filter Set MeasureTheory
open Erdos335.IntermediateScale
open scoped Pointwise ENNReal

noncomputable section

namespace Erdos335.Loeb

local instance regularPrefixWindowLoebSpace (U : Ultrafilter ℕ) (q : ℕ → ℕ+) :
    MeasurableSpace ((U : Filter ℕ).Product (fun n => ZMod (q n : ℕ))) := loebMeasurableSpace U

theorem loeb_regular_prefix_window_agreement
    (U : Ultrafilter ℕ) (hU : (U : Filter ℕ) ≤ atTop) (q : ℕ → ℕ+)
    (hdiv : ∀ h : ℕ+, ∀ᶠ n in U, (h : ℕ) ∣ (q n : ℕ))
    (A : Set ℕ) (E : ℕ → Set ℕ) (start : ℕ → ℕ)
    (hEA : ∀ᶠ n in U, E n ⊆ A) (hexhaust : ∀ a ∈ A, ∀ᶠ n in U, a ∈ E n)
    (a : ℝ)
    (hmE : (loebMeasure U hU (internalSet U
      (fun n => ((↑) : ℕ → ZMod (q n : ℕ)) '' E n))).toReal = a)
    (hmW : (loebMeasure U hU (internalSet U
      (fun n => (cyclicWindow A (start n) (q n : ℕ) : Set (ZMod (q n : ℕ)))))).toReal = a)
    (happrox : ∀ ε : ℝ, 0 < ε → ∃ k : ℕ+, ((residues (k : ℕ) A).card : ℝ) / (k : ℕ) ≤ a + ε) :
    internalSet U (fun n => ((↑) : ℕ → ZMod (q n : ℕ)) '' E n) =ᵐ[loebMeasure U hU]
      productProjection (U : Filter ℕ) (fun n => (start n : ZMod (q n : ℕ))) +ᵥ
        internalSet U (fun n => (cyclicWindow A (start n) (q n : ℕ) : Set (ZMod (q n : ℕ)))) := by
  let G := (U : Filter ℕ).Product (fun n => ZMod (q n : ℕ))
  let μ : Measure G := loebMeasure (X := fun n => ZMod (q n : ℕ)) U hU
  have : IsProbabilityMeasure μ := isProbabilityMeasure_loebMeasure U hU
  let P := internalSet U (fun n => ((↑) : ℕ → ZMod (q n : ℕ)) '' E n)
  let W := internalSet U (fun n => (cyclicWindow A (start n) (q n : ℕ) : Set (ZMod (q n : ℕ))))
  let v := productProjection (U : Filter ℕ) (fun n => (start n : ZMod (q n : ℕ)))
  have hPm : MeasurableSet P := measurable_internalSet U _
  have hWm : MeasurableSet W := measurable_internalSet U _
  have hmassV : (μ (v +ᵥ W)).toReal = a :=
    (congrArg ENNReal.toReal (loebMeasure_image_add_left U hU v W)).trans hmW
  apply ae_eq_of_common_approximate_covers μ P (v +ᵥ W) hPm
    (measurable_loeb_translate U hU W hWm v) a hmE hmassV
  intro ε hε
  obtain ⟨k, hk⟩ := happrox ε hε
  let φ := finiteQuotient U (fun n => naturalCyclicProjection (q n) k)
  let C := φ ⁻¹' (residues (k : ℕ) A : Set _)
  have himage : φ '' P = (residues (k : ℕ) A : Set _) :=
    finiteQuotient_image_of_literal_exhaustion U q A E hEA hexhaust k
      (fun n => naturalCyclicProjection (q n) k)
      ((hdiv k).mono fun n hn t => naturalCyclicProjection_natCast (q n) k hn t)
  have hPsub : P ⊆ C := by
    change P ⊆ φ ⁻¹' (residues (k : ℕ) A : Set _)
    rw [← himage]
    exact subset_preimage_image φ P
  have hv : φ v = finiteValue U (fun n => (start n : ZMod (k : ℕ))) := by
    change finiteValue U (fun n => naturalCyclicProjection (q n) k (start n : ZMod (q n : ℕ))) = _
    apply finiteValue_congr
    exact (hdiv k).mono fun n hn => naturalCyclicProjection_natCast (q n) k hn (start n)
  have hVsub : v +ᵥ W ⊆ C := by
    rintro x ⟨y, hy, rfl⟩
    change φ (v + y) ∈ residues (k : ℕ) A
    rw [map_add, hv]
    have hyR := actual_residue_of_internal_cyclic_window U q k (hdiv k) A start y hy
    simpa only [add_comm] using hyR
  refine ⟨C, hPsub.eventuallySubset, hVsub.eventuallySubset, ?_⟩
  change (loebMeasure U hU ((finiteQuotient U (fun n => naturalCyclicProjection (q n) k)) ⁻¹'
    (residues (k : ℕ) A : Set _))).toReal ≤ a + ε
  rw [loebMeasure_naturalCyclicProjection_preimage U hU q k (hdiv k),
    ENNReal.toReal_div, ENNReal.toReal_natCast, ENNReal.toReal_natCast]
  exact hk

end Erdos335.Loeb

end
