import Erdos335.LoebGroup

/-!
# Internal bijections preserve counting

Fiberwise bijections induce bijections of the ultraproduct. They preserve the
internal algebra and its normalized counting content.
-/

set_option autoImplicit false

open Filter Set Topology MeasureTheory
open scoped ENNReal

namespace Erdos335.Loeb

variable {I : Type*} {X Y : I → Type*}

def productEquiv (L : Filter I) (e : ∀ i, X i ≃ Y i) : L.Product X ≃ L.Product Y where
  toFun := productMap L (fun i => e i)
  invFun := productMap L (fun i => (e i).symm)
  left_inv := by
    intro x
    induction x using Quotient.inductionOn with
    | h f =>
      apply congrArg (fun g : ∀ i, X i => (g : L.Product X))
      exact funext fun i => (e i).symm_apply_apply (f i)
  right_inv := by
    intro y
    induction y using Quotient.inductionOn with
    | h f =>
      apply congrArg (fun g : ∀ i, Y i => (g : L.Product Y))
      exact funext fun i => (e i).apply_symm_apply (f i)

theorem internalSet_preimage (U : Ultrafilter I) (f : ∀ i, X i → Y i)
    (B : ∀ i, Set (Y i)) :
    productMap (U : Filter I) f ⁻¹' internalSet U B =
      internalSet U (fun i => f i ⁻¹' B i) := by
  ext x
  induction x using Quotient.inductionOn with
  | h g => exact Iff.rfl

theorem internalSet_image_equiv (U : Ultrafilter I) (e : ∀ i, X i ≃ Y i)
    (A : ∀ i, Set (X i)) :
    productEquiv (U : Filter I) e '' internalSet U A =
      internalSet U (fun i => e i '' A i) := by
  have hfiber : (fun i => (e i).symm ⁻¹' A i) = (fun i => e i '' A i) := by
    funext i
    ext b
    constructor
    · intro hb
      exact ⟨(e i).symm b, hb, (e i).apply_symm_apply b⟩
    · rintro ⟨a, ha, rfl⟩
      change (e i).symm ((e i) a) ∈ A i
      simpa only [Equiv.symm_apply_apply] using ha
  calc
    productEquiv (U : Filter I) e '' internalSet U A =
        (productEquiv (U : Filter I) e).symm ⁻¹' internalSet U A := by
      ext y
      constructor
      · rintro ⟨x, hx, rfl⟩
        simpa only [mem_preimage, Equiv.symm_apply_apply] using hx
      · intro hy
        exact ⟨(productEquiv (U : Filter I) e).symm y, hy,
          (productEquiv (U : Filter I) e).apply_symm_apply y⟩
    _ = internalSet U (fun i => (e i).symm ⁻¹' A i) :=
      internalSet_preimage U (fun i => (e i).symm) A
    _ = _ := congrArg (internalSet U) hfiber

theorem internalSets_preimage_equiv_iff (U : Ultrafilter I) (e : ∀ i, X i ≃ Y i)
    (S : Set ((U : Filter I).Product Y)) :
    productEquiv (U : Filter I) e ⁻¹' S ∈ internalSets U ↔ S ∈ internalSets U := by
  constructor
  · rintro ⟨A, hA⟩
    refine ⟨fun i => e i '' A i, ?_⟩
    rw [← internalSet_image_equiv, hA]
    exact (productEquiv (U : Filter I) e).surjective.image_preimage S
  · rintro ⟨B, rfl⟩
    exact ⟨fun i => e i ⁻¹' B i, (internalSet_preimage U (fun i => e i) B).symm⟩

theorem countingRatio_preimage_equiv {A B : Type*} (e : A ≃ B) (S : Set B) :
    countingRatio (e ⁻¹' S) = countingRatio S := by
  have hcard : (e ⁻¹' S).ncard = S.ncard := by
    rw [← Set.ncard_image_of_injective (e ⁻¹' S) e.injective,
      e.surjective.image_preimage S]
  simp only [countingRatio, hcard, Nat.card_congr e]

theorem ultraCount_preimage_equiv (U : Ultrafilter I) (e : ∀ i, X i ≃ Y i)
    (A : ∀ i, Set (Y i)) :
    ultraCount U (fun i => e i ⁻¹' A i) = ultraCount U A := by
  apply tendsto_nhds_unique (tendsto_ultraCount U _)
  simpa only [countingRatio_preimage_equiv] using tendsto_ultraCount U A

theorem internalMass_preimage_equiv [∀ i, Nonempty (X i)] [∀ i, Nonempty (Y i)]
    (U : Ultrafilter I) (e : ∀ i, X i ≃ Y i)
    (S : Set ((U : Filter I).Product Y)) :
    internalMass U (productEquiv (U : Filter I) e ⁻¹' S) = internalMass U S := by
  classical
  by_cases hS : S ∈ internalSets U
  · obtain ⟨A, rfl⟩ := hS
    change internalMass U (productMap (U : Filter I) (fun i => e i) ⁻¹' internalSet U A) = _
    rw [internalSet_preimage, internalMass_internal, internalMass_internal]
    exact ultraCount_preimage_equiv U e A
  · have hpre : productEquiv (U : Filter I) e ⁻¹' S ∉ internalSets U :=
      fun h => hS ((internalSets_preimage_equiv_iff U e S).mp h)
    rw [internalMass, dite_eq_right hpre, internalMass, dite_eq_right hS]

end Erdos335.Loeb
