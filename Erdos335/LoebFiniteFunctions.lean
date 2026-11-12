import Erdos335.LoebFiniteQuotient

/-!
# Finite-valued internal functions

A finite-valued family induces a measurable function on the ultraproduct.
Its fibers are internal and their measures are the exact counting ultralimits.
-/

set_option autoImplicit false

open Filter Set Topology MeasureTheory

namespace Erdos335.Loeb

variable {I G : Type*} {X : I → Type*} [Finite G]

noncomputable def finiteFunction (U : Ultrafilter I) (f : ∀ i, X i → G) :
    (U : Filter I).Product X → G :=
  Quotient.lift (fun x => finiteValue U (fun i => f i (x i)))
    (fun _ _ h => finiteValue_congr U _ _ (h.mono fun i hi => congrArg (f i) hi))

theorem finiteFunction_preimage (U : Ultrafilter I) (f : ∀ i, X i → G) (S : Set G) :
    finiteFunction U f ⁻¹' S = internalSet U (fun i => f i ⁻¹' S) := by
  ext x
  induction x using Quotient.inductionOn with
  | h g =>
    change finiteValue U (fun i => f i (g i)) ∈ S ↔ ∀ᶠ i in U, f i (g i) ∈ S
    constructor
    · intro hv
      exact (eventually_eq_finiteValue U (fun i => f i (g i))).mono fun i hi => hi.symm ▸ hv
    · intro hS
      obtain ⟨i, hi⟩ := Filter.nonempty_of_mem
        ((eventually_eq_finiteValue U (fun i => f i (g i))).and hS)
      exact hi.1 ▸ hi.2

theorem measurable_finiteFunction {Y : ℕ → Type*} [∀ n, Finite (Y n)] [∀ n, Nonempty (Y n)]
    [MeasurableSpace G] (U : Ultrafilter ℕ) (f : ∀ n, Y n → G) :
    @Measurable ((U : Filter ℕ).Product Y) G (loebMeasurableSpace U) _ (finiteFunction U f) := by
  intro S _
  rw [finiteFunction_preimage]
  exact measurable_internalSet U _

theorem loebMeasure_finiteFunction_preimage
    {Y : ℕ → Type*} [∀ n, Finite (Y n)] [∀ n, Nonempty (Y n)]
    (U : Ultrafilter ℕ) (hU : (U : Filter ℕ) ≤ atTop) (f : ∀ n, Y n → G) (S : Set G) :
    loebMeasure U hU (finiteFunction U f ⁻¹' S) = ultraCount U (fun n => f n ⁻¹' S) := by
  rw [finiteFunction_preimage, loebMeasure_internal]

end Erdos335.Loeb
