import Erdos335.LoebLiteralResidues

/-!
# Natural quotient maps for divisible cyclic models
-/

set_option autoImplicit false

open Filter Set MeasureTheory
open scoped ENNReal

noncomputable section

namespace Erdos335.Loeb

def naturalCyclicProjection (q h : ℕ+) : ZMod (q : ℕ) →+ ZMod (h : ℕ) := by
  classical
  exact if hd : (h : ℕ) ∣ (q : ℕ) then
    (ZMod.castHom hd (ZMod (h : ℕ))).toAddMonoidHom else 0

theorem naturalCyclicProjection_natCast (q h : ℕ+) (hd : (h : ℕ) ∣ (q : ℕ)) (n : ℕ) :
    naturalCyclicProjection q h (n : ZMod (q : ℕ)) = (n : ZMod (h : ℕ)) := by
  classical
  rw [naturalCyclicProjection, dif_pos hd]
  exact map_natCast (ZMod.castHom hd (ZMod (h : ℕ))) n

theorem naturalCyclicProjection_surjective (q h : ℕ+) (hd : (h : ℕ) ∣ (q : ℕ)) :
    Function.Surjective (naturalCyclicProjection q h) := by
  intro r
  refine ⟨(r.val : ZMod (q : ℕ)), ?_⟩
  rw [naturalCyclicProjection_natCast q h hd, ZMod.natCast_zmod_val]

theorem naturalCyclicProjection_val (q h : ℕ+) (hd : (h : ℕ) ∣ (q : ℕ))
    (r : ZMod (q : ℕ)) : naturalCyclicProjection q h r = (r.val : ZMod (h : ℕ)) := by
  have h := naturalCyclicProjection_natCast q h hd r.val
  simpa only [ZMod.natCast_zmod_val] using h

theorem finiteQuotient_eq_finiteFunction {I G : Type*} {X : I → Type*}
    [AddCommGroup G] [Finite G] [∀ i, AddCommGroup (X i)]
    (U : Ultrafilter I) (p : ∀ i, X i →+ G) :
    (finiteQuotient U p : (U : Filter I).Product X → G) = finiteFunction U (fun i => p i) := by
  funext x
  induction x using Quotient.inductionOn with
  | h f => rfl

theorem finiteQuotient_preimage_internal {I G : Type*} {X : I → Type*}
    [AddCommGroup G] [Finite G] [∀ i, AddCommGroup (X i)]
    (U : Ultrafilter I) (p : ∀ i, X i →+ G) (S : Set G) :
    (finiteQuotient U p) ⁻¹' S = internalSet U (fun i => p i ⁻¹' S) := by
  rw [finiteQuotient_eq_finiteFunction, finiteFunction_preimage]

theorem naturalCyclicProjection_kernel (U : Ultrafilter ℕ) (q : ℕ → ℕ+) (h : ℕ+)
    (hd : ∀ᶠ n in U, (h : ℕ) ∣ (q n : ℕ)) :
    naturalCyclicKernel U q h = (finiteQuotient U (fun n => naturalCyclicProjection (q n) h)).ker := by
  apply naturalCyclicKernel_eq
  exact hd.mono fun n hn t => naturalCyclicProjection_natCast (q n) h hn t

theorem loebMeasure_naturalCyclicProjection_preimage
    (U : Ultrafilter ℕ) (hU : (U : Filter ℕ) ≤ atTop) (q : ℕ → ℕ+) (h : ℕ+)
    (hd : ∀ᶠ n in U, (h : ℕ) ∣ (q n : ℕ)) (S : Finset (ZMod (h : ℕ))) :
    loebMeasure U hU ((finiteQuotient U (fun n => naturalCyclicProjection (q n) h)) ⁻¹' (S : Set _)) =
      (S.card : ℝ≥0∞) / (h : ℕ) := by
  simpa only [Nat.card_zmod] using loebMeasure_finiteQuotient_preimage U hU q
    (fun n => naturalCyclicProjection (q n) h)
    (hd.mono fun n hn => naturalCyclicProjection_surjective (q n) h hn) S

end Erdos335.Loeb

end
