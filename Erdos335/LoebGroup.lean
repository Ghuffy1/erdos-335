import Erdos335.LoebMeasure
import Mathlib.Algebra.Group.InjSurj
import Mathlib.Algebra.Group.Pointwise.Set.Basic

/-!
# The additive group of the dependent ultraproduct

The group operations are induced by the pointwise operations on sequences.
Internal set addition agrees with the fiberwise sumsets.
-/

set_option autoImplicit false

open Filter Set
open scoped Pointwise

namespace Erdos335.Loeb

variable {I : Type*} {X Y Z : I → Type*}

def productMap (L : Filter I) (f : ∀ i, X i → Y i) : L.Product X → L.Product Y :=
  Quotient.map (fun x i => f i (x i)) fun _ _ h => h.mono fun i hi => congrArg (f i) hi

def productMap₂ (L : Filter I) (f : ∀ i, X i → Y i → Z i) :
    L.Product X → L.Product Y → L.Product Z :=
  Quotient.map₂ (fun x y i => f i (x i) (y i)) fun _ _ hx _ _ hy =>
    (hx.and hy).mono fun i hi => congrArg₂ (f i) hi.1 hi.2

instance productZero (L : Filter I) [∀ i, Zero (X i)] : Zero (L.Product X) :=
  ⟨((fun i => (0 : X i)) : L.Product X)⟩

instance productAdd (L : Filter I) [∀ i, Add (X i)] : Add (L.Product X) :=
  ⟨productMap₂ L (fun _ => (· + ·))⟩

instance productNeg (L : Filter I) [∀ i, Neg (X i)] : Neg (L.Product X) :=
  ⟨productMap L (fun _ => Neg.neg)⟩

instance productSub (L : Filter I) [∀ i, Sub (X i)] : Sub (L.Product X) :=
  ⟨productMap₂ L (fun _ => (· - ·))⟩

instance productSMul {R : Type*} (L : Filter I) [∀ i, SMul R (X i)] :
    SMul R (L.Product X) := ⟨fun r => productMap L (fun _ => (r • ·))⟩

instance productAddCommGroup (L : Filter I) [∀ i, AddCommGroup (X i)] :
    AddCommGroup (L.Product X) :=
  Function.Surjective.addCommGroup (fun f : ∀ i, X i => (f : L.Product X))
    (by intro x; induction x using Quotient.inductionOn with
        | h f => exact ⟨f, rfl⟩) rfl (fun _ _ => rfl) (fun _ => rfl)
    (fun _ _ => rfl) (fun _ _ => rfl) (fun _ _ => rfl)

def productProjection (L : Filter I) [∀ i, AddCommGroup (X i)] :
    (∀ i, X i) →+ L.Product X where
  toFun f := (f : L.Product X)
  map_zero' := rfl
  map_add' _ _ := rfl

theorem internalSet_add [∀ i, AddCommGroup (X i)] (U : Ultrafilter I)
    (A B : ∀ i, Set (X i)) :
    internalSet U (fun i => A i + B i) = internalSet U A + internalSet U B := by
  classical
  ext x
  induction x using Quotient.inductionOn with
  | h f =>
    constructor
    · intro hx
      have hex : ∀ᶠ i in U, ∃ a ∈ A i, ∃ b ∈ B i, a + b = f i := hx
      let a : ∀ i, X i := fun i => if h : ∃ a ∈ A i, ∃ b ∈ B i, a + b = f i
        then h.choose else 0
      let b : ∀ i, X i := fun i => if h : ∃ a ∈ A i, ∃ b ∈ B i, a + b = f i
        then h.choose_spec.2.choose else 0
      have ha : (a : (U : Filter I).Product X) ∈ internalSet U A := by
        apply hex.mono
        intro i hi
        simp only [a, dite_eq_left hi]
        exact hi.choose_spec.1
      have hb : (b : (U : Filter I).Product X) ∈ internalSet U B := by
        apply hex.mono
        intro i hi
        simp only [b, dite_eq_left hi]
        exact hi.choose_spec.2.choose_spec.1
      refine Set.mem_add.mpr ⟨a, ha, b, hb, ?_⟩
      apply Quotient.sound
      apply hex.mono
      intro i hi
      simp only [a, b, dite_eq_left hi]
      exact hi.choose_spec.2.choose_spec.2
    · intro hx
      obtain ⟨a, ha, b, hb, hab⟩ := Set.mem_add.mp hx
      induction a using Quotient.inductionOn with
      | h fa =>
        induction b using Quotient.inductionOn with
        | h fb =>
          have hab' : ∀ᶠ i in U, fa i + fb i = f i := Quotient.exact hab
          filter_upwards [ha, hb, hab'] with i hai hbi hi
          exact Set.mem_add.mpr ⟨fa i, hai, fb i, hbi, hi⟩

end Erdos335.Loeb
