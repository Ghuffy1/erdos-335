import Mathlib.Order.Filter.Germ.Basic
import Mathlib.Order.Filter.Ultrafilter.Basic
import Mathlib.MeasureTheory.SetAlgebra

/-!
# Internal sets in a dependent ultraproduct

The Boolean algebra is defined on Mathlib's filter product. Its order is
exactly the eventual order of representing families when the factors are
nonempty. These are foundations for a counting Loeb measure.
-/

set_option autoImplicit false

open Filter Set

namespace Erdos335.Loeb

variable {I : Type*} {X : I → Type*}

def internalSet (U : Ultrafilter I) (A : ∀ i, Set (X i)) :
    Set ((U : Filter I).Product X) := fun x =>
  Quotient.liftOn x (fun f => ∀ᶠ i in U, f i ∈ A i)
    (fun f g hfg => propext <| Filter.eventually_congr <|
      hfg.mono fun i hi => by rw [hi])

theorem mem_internalSet_iff (U : Ultrafilter I) (A : ∀ i, Set (X i))
    (f : ∀ i, X i) :
    (f : (U : Filter I).Product X) ∈ internalSet U A ↔ ∀ᶠ i in U, f i ∈ A i :=
  Iff.rfl

theorem internalSet_empty (U : Ultrafilter I) :
    internalSet U (fun i => (∅ : Set (X i))) = ∅ := by
  ext x
  induction x using Quotient.inductionOn with
  | h f =>
    change (∀ᶠ i in U, f i ∈ (∅ : Set (X i))) ↔ False
    simp
    exact U.neBot.ne

theorem internalSet_univ (U : Ultrafilter I) :
    internalSet U (fun i => (univ : Set (X i))) = univ := by
  ext x
  induction x using Quotient.inductionOn with
  | h f =>
    change (∀ᶠ i in U, f i ∈ (univ : Set (X i))) ↔ True
    simp

theorem internalSet_inter (U : Ultrafilter I) (A B : ∀ i, Set (X i)) :
    internalSet U (fun i => A i ∩ B i) = internalSet U A ∩ internalSet U B := by
  ext x
  induction x using Quotient.inductionOn with
  | h f =>
    change (∀ᶠ i in U, f i ∈ A i ∩ B i) ↔
      (∀ᶠ i in U, f i ∈ A i) ∧ ∀ᶠ i in U, f i ∈ B i
    simp only [mem_inter_iff, eventually_and]

theorem internalSet_union (U : Ultrafilter I) (A B : ∀ i, Set (X i)) :
    internalSet U (fun i => A i ∪ B i) = internalSet U A ∪ internalSet U B := by
  ext x
  induction x using Quotient.inductionOn with
  | h f =>
    change (∀ᶠ i in U, f i ∈ A i ∪ B i) ↔
      (∀ᶠ i in U, f i ∈ A i) ∨ ∀ᶠ i in U, f i ∈ B i
    simp only [mem_union, Ultrafilter.eventually_or]

theorem internalSet_compl (U : Ultrafilter I) (A : ∀ i, Set (X i)) :
    internalSet U (fun i => (A i)ᶜ) = (internalSet U A)ᶜ := by
  ext x
  induction x using Quotient.inductionOn with
  | h f =>
    change (∀ᶠ i in U, f i ∈ (A i)ᶜ) ↔ ¬∀ᶠ i in U, f i ∈ A i
    simp only [mem_compl_iff, Ultrafilter.eventually_not]

theorem internalSet_sdiff (U : Ultrafilter I) (A B : ∀ i, Set (X i)) :
    internalSet U (fun i => A i \ B i) = internalSet U A \ internalSet U B := by
  simp only [sdiff_eq_compl_inter, internalSet_inter, internalSet_compl]

theorem internalSet_biInter_finset {K : Type*} (U : Ultrafilter I)
    (J : Finset K) (A : K → ∀ i, Set (X i)) :
    internalSet U (fun i => ⋂ k ∈ J, A k i) = ⋂ k ∈ J, internalSet U (A k) := by
  ext x
  induction x using Quotient.inductionOn with
  | h f =>
    constructor
    · intro hx
      refine Set.mem_iInter.mpr fun k => Set.mem_iInter.mpr fun hk => ?_
      change ∀ᶠ i in U, f i ∈ A k i
      exact hx.mono fun i hi => Set.mem_iInter.mp (Set.mem_iInter.mp hi k) hk
    · intro hx
      change ∀ᶠ i in U, f i ∈ ⋂ k ∈ J, A k i
      have hh : ∀ k ∈ J, ∀ᶠ i in U, f i ∈ A k i :=
        fun k hk => Set.mem_iInter.mp (Set.mem_iInter.mp hx k) hk
      exact ((Filter.eventually_all_finset J).mpr hh).mono fun i hi =>
        Set.mem_iInter.mpr fun k => Set.mem_iInter.mpr fun hk => hi k hk

def internalSets (U : Ultrafilter I) : Set (Set ((U : Filter I).Product X)) :=
  Set.range (internalSet U)

theorem isSetAlgebra_internalSets (U : Ultrafilter I) :
    MeasureTheory.IsSetAlgebra (internalSets (X := X) U) where
  empty_mem := ⟨fun i => ∅, internalSet_empty U⟩
  compl_mem := by
    rintro s ⟨A, rfl⟩
    exact ⟨fun i => (A i)ᶜ, internalSet_compl U A⟩
  union_mem := by
    rintro s t ⟨A, rfl⟩ ⟨B, rfl⟩
    exact ⟨fun i => A i ∪ B i, internalSet_union U A B⟩

theorem internalSet_nonempty_iff (U : Ultrafilter I) [∀ i, Nonempty (X i)]
    (A : ∀ i, Set (X i)) :
    (internalSet U A).Nonempty ↔ ∀ᶠ i in U, (A i).Nonempty := by
  classical
  constructor
  · rintro ⟨x, hx⟩
    induction x using Quotient.inductionOn with
    | h f => exact hx.mono fun i hi => ⟨f i, hi⟩
  · intro hA
    let f : ∀ i, X i := fun i => if h : (A i).Nonempty then h.choose else
      Classical.choice inferInstance
    refine ⟨(f : (U : Filter I).Product X), ?_⟩
    apply hA.mono
    intro i hi
    simp only [f, dite_eq_left hi]
    exact hi.choose_spec

theorem internalSet_subset_iff (U : Ultrafilter I) [∀ i, Nonempty (X i)]
    (A B : ∀ i, Set (X i)) :
    internalSet U A ⊆ internalSet U B ↔ ∀ᶠ i in U, A i ⊆ B i := by
  classical
  constructor
  · intro h
    by_contra hn
    have hdiff : ∀ᶠ i in U, (A i \ B i).Nonempty :=
      (Ultrafilter.eventually_not.mpr hn).mono fun i hi => Set.not_subset.mp hi
    obtain ⟨x, hx⟩ := (internalSet_nonempty_iff U (fun i => A i \ B i)).mpr hdiff
    rw [internalSet_sdiff] at hx
    exact hx.2 (h hx.1)
  · intro h x hx
    induction x using Quotient.inductionOn with
    | h f =>
      change ∀ᶠ i in U, f i ∈ B i
      filter_upwards [h, hx] with i hi hix using hi hix

theorem internalSet_eq_iff (U : Ultrafilter I) [∀ i, Nonempty (X i)]
    (A B : ∀ i, Set (X i)) :
    internalSet U A = internalSet U B ↔ ∀ᶠ i in U, A i = B i := by
  constructor
  · intro h
    have hAB := (internalSet_subset_iff U A B).mp h.le
    have hBA := (internalSet_subset_iff U B A).mp h.ge
    exact (hAB.and hBA).mono fun i hi => Set.Subset.antisymm hi.1 hi.2
  · intro h
    apply Set.Subset.antisymm
    · exact (internalSet_subset_iff U A B).mpr (h.mono fun i hi => hi.le)
    · exact (internalSet_subset_iff U B A).mpr (h.mono fun i hi => hi.ge)

end Erdos335.Loeb
