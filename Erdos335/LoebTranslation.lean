import Erdos335.LoebInvariance

/-!
# Translation invariance of counting Loeb measure

Every fixed translation of the ultraproduct is induced by a sequence of
finite-group translations and preserves the Loeb measure on all sets.
-/

set_option autoImplicit false

open Filter Set Topology MeasureTheory

namespace Erdos335.Loeb

variable {X : ℕ → Type*} [∀ n, AddCommGroup (X n)] [∀ n, Finite (X n)]

omit [∀ n, Finite (X n)] in
theorem productEquiv_add_left (U : Ultrafilter ℕ) (f : ∀ n, X n) :
    (productEquiv (U : Filter ℕ) (fun n => Equiv.addLeft (f n)) :
      (U : Filter ℕ).Product X → (U : Filter ℕ).Product X) =
      fun x => productProjection (U : Filter ℕ) f + x := by
  funext x
  induction x using Quotient.inductionOn with
  | h g => rfl

theorem loebMeasure_preimage_add_left (U : Ultrafilter ℕ)
    (hU : (U : Filter ℕ) ≤ atTop) (t : (U : Filter ℕ).Product X)
    (S : Set ((U : Filter ℕ).Product X)) :
    loebMeasure U hU ((fun x => t + x) ⁻¹' S) = loebMeasure U hU S := by
  induction t using Quotient.inductionOn with
  | h f =>
    change loebMeasure U hU ((fun x => productProjection (U : Filter ℕ) f + x) ⁻¹' S) = _
    rw [← productEquiv_add_left U f]
    exact loebMeasure_preimage_equiv U hU (fun n => Equiv.addLeft (f n)) S

theorem measurable_add_left (U : Ultrafilter ℕ) (hU : (U : Filter ℕ) ≤ atTop)
    (t : (U : Filter ℕ).Product X) :
    @Measurable ((U : Filter ℕ).Product X) ((U : Filter ℕ).Product X)
      (loebMeasurableSpace U) (loebMeasurableSpace U) (fun x => t + x) := by
  induction t using Quotient.inductionOn with
  | h f =>
    change @Measurable ((U : Filter ℕ).Product X) ((U : Filter ℕ).Product X)
      (loebMeasurableSpace U) (loebMeasurableSpace U)
      (fun x => productProjection (U : Filter ℕ) f + x)
    rw [← productEquiv_add_left U f]
    exact measurable_productEquiv U hU (fun n => Equiv.addLeft (f n))

theorem loebMeasure_image_add_left (U : Ultrafilter ℕ)
    (hU : (U : Filter ℕ) ≤ atTop) (t : (U : Filter ℕ).Product X)
    (S : Set ((U : Filter ℕ).Product X)) :
    loebMeasure U hU ((fun x => t + x) '' S) = loebMeasure U hU S := by
  have hEq : (fun x => t + x) '' S = (fun x => -t + x) ⁻¹' S := by
    ext x
    constructor
    · rintro ⟨y, hy, rfl⟩
      simpa only [mem_preimage, neg_add_cancel_left] using hy
    · intro hx
      exact ⟨-t + x, hx, add_neg_cancel_left t x⟩
  rw [hEq, loebMeasure_preimage_add_left]

end Erdos335.Loeb
