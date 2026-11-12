import Erdos335.LoebIndicators
import Erdos335.LoebInvariance

/-!
# Convolution and almost-everywhere changes in the Loeb group

Every fixed reflection-translation preserves the Loeb measure. Hence
changing either factor on a null set preserves convolution at every point.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Filter Set Topology MeasureTheory
open scoped Pointwise

noncomputable section

namespace Erdos335.Loeb

variable {X : ℕ → Type*} [∀ n, AddCommGroup (X n)] [∀ n, Fintype (X n)]

local instance aeConvolutionMeasurableSpace (U : Ultrafilter ℕ) :
    MeasurableSpace ((U : Filter ℕ).Product X) := loebMeasurableSpace U

theorem productEquiv_sub_left (U : Ultrafilter ℕ) (a : ∀ n, X n) :
    (productEquiv (U : Filter ℕ) (fun n => Equiv.subLeft (a n)) :
      (U : Filter ℕ).Product X → (U : Filter ℕ).Product X) =
        (fun x => productProjection (U : Filter ℕ) a - x) := by
  funext x
  induction x using Quotient.inductionOn with
  | h b => rfl

theorem loebMeasurePreserving_sub_left
    (U : Ultrafilter ℕ) (hU : (U : Filter ℕ) ≤ atTop)
    (a : (U : Filter ℕ).Product X) :
    MeasurePreserving (fun x => a - x) (loebMeasure U hU) (loebMeasure U hU) := by
  induction a using Quotient.inductionOn with
  | h a =>
    change MeasurePreserving (fun x => productProjection (U : Filter ℕ) a - x)
      (loebMeasure U hU) (loebMeasure U hU)
    rw [← productEquiv_sub_left U a]
    refine ⟨measurable_productEquiv U hU _, ?_⟩
    apply Measure.ext
    intro S hS
    rw [Measure.map_apply (measurable_productEquiv U hU _) hS]
    exact loebMeasure_preimage_equiv U hU _ S

theorem loeb_convolution_congr_ae
    (U : Ultrafilter ℕ) (hU : (U : Filter ℕ) ≤ atTop)
    (f f' g g' : (U : Filter ℕ).Product X → ℝ)
    (hf : f =ᵐ[loebMeasure U hU] f') (hg : g =ᵐ[loebMeasure U hU] g')
    (x : (U : Filter ℕ).Product X) :
    (∫ t, f t * g (x - t) ∂loebMeasure U hU) =
      ∫ t, f' t * g' (x - t) ∂loebMeasure U hU := by
  apply integral_congr_ae
  filter_upwards [hf, (loebMeasurePreserving_sub_left U hU x).quasiMeasurePreserving.ae hg]
    with t hft hgt
  rw [hft, hgt]

theorem loeb_indicator_convolution_congr_ae
    (U : Ultrafilter ℕ) (hU : (U : Filter ℕ) ≤ atTop)
    (A A' B B' : Set ((U : Filter ℕ).Product X))
    (hA : A =ᵐ[loebMeasure U hU] A') (hB : B =ᵐ[loebMeasure U hU] B')
    (x : (U : Filter ℕ).Product X) :
    (∫ t, A.indicator (fun _ => (1 : ℝ)) t * B.indicator (fun _ => (1 : ℝ)) (x - t)
      ∂loebMeasure U hU) =
      ∫ t, A'.indicator (fun _ => (1 : ℝ)) t * B'.indicator (fun _ => (1 : ℝ)) (x - t)
        ∂loebMeasure U hU :=
  loeb_convolution_congr_ae U hU _ _ _ _
    (indicator_ae_eq_of_ae_eq_set hA) (indicator_ae_eq_of_ae_eq_set hB) x

theorem loeb_positive_model_subset_of_ae_variants
    {Y : Type*} [AddCommGroup Y]
    (U : Ultrafilter ℕ) (hU : (U : Filter ℕ) ≤ atTop)
    (A A' B B' : Set ((U : Filter ℕ).Product X))
    (hA : A =ᵐ[loebMeasure U hU] A') (hB : B =ᵐ[loebMeasure U hU] B')
    (q : (U : Filter ℕ).Product X → Y) (C D : Set Y) (h : Y → ℝ)
    (hpos : ∀ y ∈ C + D, 0 < h y)
    (hrep : (fun x => ∫ t, A.indicator (fun _ => (1 : ℝ)) t *
        B.indicator (fun _ => (1 : ℝ)) (x - t) ∂loebMeasure U hU) =ᵐ[loebMeasure U hU]
      (fun x => h (q x))) :
    ∀ᵐ x ∂loebMeasure U hU, q x ∈ C + D → x ∈ A' + B' := by
  filter_upwards [hrep] with x hx
  intro hsum
  apply positive_indicator_convolution_subset_add (loebMeasure U hU) A' B'
  change 0 < ∫ t, A'.indicator (fun _ => (1 : ℝ)) t *
    B'.indicator (fun _ => (1 : ℝ)) (x - t) ∂loebMeasure U hU
  rw [← loeb_indicator_convolution_congr_ae U hU A A' B B' hA hB x, hx]
  exact hpos (q x) hsum

end Erdos335.Loeb

end
