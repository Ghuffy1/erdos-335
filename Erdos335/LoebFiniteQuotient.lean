import Erdos335.LoebGroup

/-!
# Maps from ultraproducts to finite quotients

A finite-valued sequence is constant on a set in the ultrafilter. This gives
the finite quotient map induced by a family of homomorphisms.
-/

set_option autoImplicit false

open Filter Set

namespace Erdos335.Loeb

variable {I G : Type*}

theorem exists_eventually_eq_const [Finite G] (U : Ultrafilter I) (f : I → G) :
    ∃ a : G, ∀ᶠ i in U, f i = a :=
  Ultrafilter.eventually_exists_iff.mp (.of_forall fun i => ⟨f i, rfl⟩)

noncomputable def finiteValue [Finite G] (U : Ultrafilter I) (f : I → G) : G :=
  (exists_eventually_eq_const U f).choose

theorem eventually_eq_finiteValue [Finite G] (U : Ultrafilter I) (f : I → G) :
    ∀ᶠ i in U, f i = finiteValue U f :=
  (exists_eventually_eq_const U f).choose_spec

theorem finiteValue_eq_of_eventually [Finite G] (U : Ultrafilter I)
    (f : I → G) (a : G) (h : ∀ᶠ i in U, f i = a) : finiteValue U f = a := by
  obtain ⟨i, hi⟩ := Filter.nonempty_of_mem ((eventually_eq_finiteValue U f).and h)
  exact hi.1.symm.trans hi.2

theorem finiteValue_const [Finite G] (U : Ultrafilter I) (a : G) :
    finiteValue U (fun _ : I => a) = a :=
  finiteValue_eq_of_eventually U _ a (.of_forall fun _ => rfl)

theorem finiteValue_congr [Finite G] (U : Ultrafilter I) (f g : I → G)
    (h : ∀ᶠ i in U, f i = g i) : finiteValue U f = finiteValue U g := by
  apply finiteValue_eq_of_eventually
  filter_upwards [h, eventually_eq_finiteValue U g] with i hi hgi using hi.trans hgi

theorem finiteValue_eq_iff [Finite G] (U : Ultrafilter I) (f : I → G) (a : G) :
    finiteValue U f = a ↔ ∀ᶠ i in U, f i = a := by
  constructor
  · intro h
    simpa only [h] using eventually_eq_finiteValue U f
  · exact finiteValue_eq_of_eventually U f a

noncomputable def finiteProjection [Finite G] [AddCommGroup G] (U : Ultrafilter I) :
    (U : Filter I).Product (fun _ => G) →+ G where
  toFun := Quotient.lift (finiteValue U) (fun f g h => finiteValue_congr U f g h)
  map_zero' := finiteValue_const U 0
  map_add' := by
    intro x y
    induction x using Quotient.inductionOn with
    | h f =>
      induction y using Quotient.inductionOn with
      | h g =>
        change finiteValue U (fun i => f i + g i) = finiteValue U f + finiteValue U g
        apply finiteValue_eq_of_eventually
        filter_upwards [eventually_eq_finiteValue U f, eventually_eq_finiteValue U g]
          with i hfi hgi using congrArg₂ (· + ·) hfi hgi

theorem finiteProjection_surjective [Finite G] [AddCommGroup G] (U : Ultrafilter I) :
    Function.Surjective (finiteProjection (G := G) U) := by
  intro a
  exact ⟨((fun _ : I => a) : (U : Filter I).Product (fun _ => G)), finiteValue_const U a⟩

variable {X Y : I → Type*} [∀ i, AddCommGroup (X i)] [∀ i, AddCommGroup (Y i)]

def productMapHom (L : Filter I) (p : ∀ i, X i →+ Y i) : L.Product X →+ L.Product Y where
  toFun := productMap L (fun i => p i)
  map_zero' := by
    apply congrArg (fun f : ∀ i, Y i => (f : L.Product Y))
    exact funext fun i => (p i).map_zero
  map_add' := by
    intro x y
    induction x using Quotient.inductionOn with
    | h f =>
      induction y using Quotient.inductionOn with
      | h g =>
        apply congrArg (fun a : ∀ i, Y i => (a : L.Product Y))
        exact funext fun i => (p i).map_add (f i) (g i)

noncomputable def finiteQuotient [Finite G] [AddCommGroup G] (U : Ultrafilter I)
    (p : ∀ i, X i →+ G) : (U : Filter I).Product X →+ G :=
  (finiteProjection U).comp (productMapHom (U : Filter I) p)

theorem finiteQuotient_surjective [Finite G] [AddCommGroup G] (U : Ultrafilter I)
    (p : ∀ i, X i →+ G) (hp : ∀ i, Function.Surjective (p i)) :
    Function.Surjective (finiteQuotient U p) := by
  classical
  intro a
  choose f hf using fun i => hp i a
  refine ⟨(f : (U : Filter I).Product X), ?_⟩
  change finiteValue U (fun i => p i (f i)) = a
  exact finiteValue_eq_of_eventually U _ a (.of_forall hf)

end Erdos335.Loeb
