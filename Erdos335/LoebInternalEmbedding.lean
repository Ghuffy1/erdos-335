import Erdos335.LoebMaps

/-!
# Internal sets under coordinate injections
-/

set_option autoImplicit false

open Set Filter

namespace Erdos335.Loeb

variable {I : Type*} {X Y : I → Type*}

theorem productMap_injective (L : Filter I) (f : ∀ i, X i → Y i)
    (hf : ∀ i, Function.Injective (f i)) :
    Function.Injective (productMap L f) := by
  intro x y hxy
  induction x using Quotient.inductionOn with
  | h a =>
    induction y using Quotient.inductionOn with
    | h b =>
      apply Quotient.sound
      exact (Quotient.exact hxy).mono fun i hi => hf i hi

theorem internalSet_image [∀ i, Nonempty (X i)]
    (U : Ultrafilter I) (f : ∀ i, X i → Y i) (A : ∀ i, Set (X i)) :
    productMap (U : Filter I) f '' internalSet U A =
      internalSet U (fun i => f i '' A i) := by
  classical
  ext y
  induction y using Quotient.inductionOn with
  | h b =>
    constructor
    · rintro ⟨x, hx, hxy⟩
      induction x using Quotient.inductionOn with
      | h a =>
        have heq : ∀ᶠ i in U, f i (a i) = b i := Quotient.exact hxy
        filter_upwards [hx, heq] with i hi hfi
        exact ⟨a i, hi, hfi⟩
    · intro hb
      let a : ∀ i, X i := fun i => if h : b i ∈ f i '' A i
        then h.choose else Classical.choice inferInstance
      have ha : (a : (U : Filter I).Product X) ∈ internalSet U A := by
        apply hb.mono
        intro i hi
        simp only [a, dite_eq_left hi]
        exact hi.choose_spec.1
      refine ⟨a, ha, Quotient.sound ?_⟩
      apply hb.mono
      intro i hi
      simp only [a, dite_eq_left hi]
      exact hi.choose_spec.2

theorem range_productMap [∀ i, Nonempty (X i)]
    (U : Ultrafilter I) (f : ∀ i, X i → Y i) :
    Set.range (productMap (U : Filter I) f) =
      internalSet U (fun i => Set.range (f i)) := by
  simpa only [internalSet_univ, image_univ] using
    internalSet_image U f (fun _ => univ)

end Erdos335.Loeb
