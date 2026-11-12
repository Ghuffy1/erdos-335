import Erdos335.LoebSubcritical

/-!
# Finite enlargements of internal sets

Every finite subset of an ultraproduct is internal. This permits finite
tests of arbitrary summands while retaining the internal Kneser theorem.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Filter Set Topology MeasureTheory
open scoped Pointwise

namespace Erdos335.Loeb

theorem exists_internalSet_of_finite
    {I : Type*} {X : I → Type*} [∀ i, AddCommGroup (X i)]
    (U : Ultrafilter I) (S : Set ((U : Filter I).Product X)) (hS : S.Finite) :
    ∃ A : ∀ i, Set (X i), internalSet U A = S := by
  classical
  induction S, hS using Set.Finite.induction_on with
  | empty => exact ⟨fun _ => ∅, internalSet_empty U⟩
  | @insert a S ha hS ih =>
    obtain ⟨A, hA⟩ := ih
    obtain ⟨x, hx⟩ : ∃ x : ∀ i, X i, productProjection (U : Filter I) x = a :=
      ⟨Quotient.out a, Quotient.out_eq a⟩
    refine ⟨fun i => {x i} ∪ A i, ?_⟩
    rw [internalSet_union, internalSet_singleton, hx, hA, singleton_union]

theorem exists_internalSet_finite_augmentation
    {I : Type*} {X : I → Type*} [∀ i, AddCommGroup (X i)]
    (U : Ultrafilter I) (A : ∀ i, Set (X i))
    (S : Set ((U : Filter I).Product X)) (hS : S.Finite) :
    ∃ B : ∀ i, Set (X i), internalSet U B = internalSet U A ∪ S := by
  obtain ⟨C, hC⟩ := exists_internalSet_of_finite U S hS
  exact ⟨fun i => A i ∪ C i, (internalSet_union U A C).trans (congrArg (internalSet U A ∪ ·) hC)⟩

theorem finiteQuotient_eq_of_eventually_natural
    {I : Type*} (U : Ultrafilter I) (q : I → ℕ+) (h : ℕ+)
    (p r : ∀ i, ZMod (q i : ℕ) →+ ZMod (h : ℕ))
    (hp : ∀ᶠ i in U, ∀ n : ℕ, p i (n : ZMod (q i : ℕ)) = (n : ZMod (h : ℕ)))
    (hr : ∀ᶠ i in U, ∀ n : ℕ, r i (n : ZMod (q i : ℕ)) = (n : ZMod (h : ℕ))) :
    finiteQuotient U p = finiteQuotient U r := by
  ext x
  induction x using Quotient.inductionOn with
  | h a =>
    change finiteValue U (fun i => p i (a i)) = finiteValue U (fun i => r i (a i))
    apply finiteValue_congr
    filter_upwards [hp, hr] with i hpi hri
    rw [← ZMod.natCast_zmod_val (a i), hpi, hri]

end Erdos335.Loeb
