import Erdos335.LoebKneser
import Erdos335.LoebCyclicQuotients

/-!
# Exact Kneser structure for subcritical internal pairs

The exact stabilizer of an internal set is its coordinate stabilizer.
A strict Loeb measure deficit gives the finite critical cardinal identity
on an ultrafilter-large set of coordinates and hence the exact saturated
measure identity. For cyclic coordinates its stabilizer is the kernel of
one fixed natural residue map.
-/

set_option autoImplicit false

open Filter Set Topology MeasureTheory
open scoped ENNReal Pointwise

namespace Erdos335.Loeb

theorem internalSet_singleton
    {I : Type*} {X : I → Type*} [∀ i, AddCommGroup (X i)]
    (U : Ultrafilter I) (x : ∀ i, X i) :
    internalSet U (fun i => {x i}) = {productProjection (U : Filter I) x} := by
  ext y
  induction y using Quotient.inductionOn with
  | h f =>
    change (∀ᶠ i in U, f i ∈ {x i}) ↔ (f : (U : Filter I).Product X) =
      productProjection (U : Filter I) x
    simp only [Set.mem_singleton_iff]
    constructor
    · intro h
      apply Quotient.sound
      exact h
    · intro h
      exact Quotient.exact h

theorem internalSet_vadd
    {I : Type*} {X : I → Type*} [∀ i, AddCommGroup (X i)]
    (U : Ultrafilter I) (x : ∀ i, X i) (C : ∀ i, Set (X i)) :
    internalSet U (fun i => x i +ᵥ C i) =
      productProjection (U : Filter I) x +ᵥ internalSet U C := by
  simp only [← Set.image_vadd, vadd_eq_add]
  simpa only [Set.singleton_add, internalSet_singleton] using
    (internalSet_add U (fun i => {x i}) C)

theorem internalAddSubgroup_stabilizer
    {I : Type*} {X : I → Type*} [∀ i, AddCommGroup (X i)]
    (U : Ultrafilter I) (C : ∀ i, Set (X i)) :
    internalAddSubgroup U (fun i => AddAction.stabilizer (X i) (C i)) =
      AddAction.stabilizer ((U : Filter I).Product X) (internalSet U C) := by
  ext x
  induction x using Quotient.inductionOn with
  | h f =>
    change (∀ᶠ i in U, f i +ᵥ C i = C i) ↔
      productProjection (U : Filter I) f +ᵥ internalSet U C = internalSet U C
    rw [← internalSet_vadd]
    exact (internalSet_eq_iff U _ _).symm

theorem countingRatio_critical_identity
    {G : Type*} [AddCommGroup G] [Finite G]
    (A B : Set G) (hA : A.Nonempty) (hB : B.Nonempty)
    (hsmall : (A + B).ncard < A.ncard + B.ncard) :
    countingRatio (A + (AddAction.stabilizer G (A + B) : Set G)) +
        countingRatio (B + (AddAction.stabilizer G (A + B) : Set G)) =
      countingRatio (A + B) + countingRatio (AddAction.stabilizer G (A + B) : Set G) := by
  classical
  let S := A.toFinite.toFinset
  let T := B.toFinite.toFinset
  have hScoe : (S : Set G) = A := by simp [S]
  have hTcoe : (T : Set G) = B := by simp [T]
  have hS : S.Nonempty := by simpa [S] using hA
  have hT : T.Nonempty := by simpa [T] using hB
  have hsum : ((S + T : Finset G) : Set G) = A + B := by
    rw [Finset.coe_add, hScoe, hTcoe]
  have hKcoe : ((S + T).addStab : Set G) = AddAction.stabilizer G (A + B) := by
    rw [Finset.coe_addStab (hS.add hT), hsum]
  have hs : (S + T).card < S.card + T.card := by
    have hAc : A.ncard = S.card := by rw [← hScoe]; simp
    have hBc : B.ncard = T.card := by rw [← hTcoe]; simp
    have hCc : (A + B).ncard = (S + T).card := by
      simpa only [Set.ncard_coe_finset] using congrArg Set.ncard hsum.symm
    rwa [hAc, hBc, hCc] at hsmall
  have hc := FiniteKneser.critical_card_identity hS hT hs
  have hAS : A + (AddAction.stabilizer G (A + B) : Set G) =
      ((S + (S + T).addStab : Finset G) : Set G) := by
    rw [Finset.coe_add, hScoe, hKcoe]
  have hBS : B + (AddAction.stabilizer G (A + B) : Set G) =
      ((T + (S + T).addStab : Finset G) : Set G) := by
    rw [Finset.coe_add, hTcoe, hKcoe]
  unfold countingRatio
  rw [hAS, hBS, ← hKcoe, ← hsum]
  simp only [Set.ncard_coe_finset, ← ENNReal.add_div, ← Nat.cast_add, hc]

theorem eventually_card_subcritical
    {X : ℕ → Type*} [∀ n, AddCommGroup (X n)] [∀ n, Finite (X n)]
    (U : Ultrafilter ℕ) (hU : (U : Filter ℕ) ≤ atTop)
    (A B : ∀ n, Set (X n))
    (hsmall : loebMeasure U hU (internalSet U (fun n => A n + B n)) <
      loebMeasure U hU (internalSet U A) + loebMeasure U hU (internalSet U B)) :
    ∀ᶠ n in U, (A n + B n).ncard < (A n).ncard + (B n).ncard := by
  simp only [loebMeasure_internal] at hsmall
  have hev := (tendsto_ultraCount U (fun n => A n + B n)).eventually_lt
    ((tendsto_ultraCount U A).add (tendsto_ultraCount U B)) hsmall
  apply hev.mono
  intro n hn
  by_contra hncard
  have hcard : (A n).ncard + (B n).ncard ≤ (A n + B n).ncard := by omega
  have hratio : countingRatio (A n) + countingRatio (B n) ≤ countingRatio (A n + B n) := by
    simp only [countingRatio, ← ENNReal.add_div, ← Nat.cast_add]
    exact ENNReal.div_le_div_right (by exact_mod_cast hcard) _
  exact (not_le_of_gt hn) hratio

theorem loebMeasure_critical_identity
    {X : ℕ → Type*} [∀ n, AddCommGroup (X n)] [∀ n, Finite (X n)]
    (U : Ultrafilter ℕ) (hU : (U : Filter ℕ) ≤ atTop)
    (A B : ∀ n, Set (X n))
    (hA : (internalSet U A).Nonempty) (hB : (internalSet U B).Nonempty)
    (hsmall : loebMeasure U hU (internalSet U (fun n => A n + B n)) <
      loebMeasure U hU (internalSet U A) + loebMeasure U hU (internalSet U B)) :
    let K := internalAddSubgroup U (fun n => AddAction.stabilizer (X n) (A n + B n))
    loebMeasure U hU (internalSet U A + (K : Set ((U : Filter ℕ).Product X))) +
        loebMeasure U hU (internalSet U B + (K : Set ((U : Filter ℕ).Product X))) =
      loebMeasure U hU (internalSet U (fun n => A n + B n)) +
        loebMeasure U hU (K : Set ((U : Filter ℕ).Product X)) := by
  dsimp only
  simp only [internalAddSubgroup_carrier, ← internalSet_add, loebMeasure_internal]
  apply tendsto_nhds_unique
    ((tendsto_ultraCount U _).add (tendsto_ultraCount U _))
  apply ((tendsto_ultraCount U _).add (tendsto_ultraCount U _)).congr'
  filter_upwards [eventually_card_subcritical U hU A B hsmall,
    (internalSet_nonempty_iff U A).mp hA, (internalSet_nonempty_iff U B).mp hB]
    with n hn hAn hBn
  exact (countingRatio_critical_identity (A n) (B n) hAn hBn hn).symm

theorem subcritical_stabilizer_positive
    {X : ℕ → Type*} [∀ n, AddCommGroup (X n)] [∀ n, Finite (X n)]
    (U : Ultrafilter ℕ) (hU : (U : Filter ℕ) ≤ atTop)
    (A B : ∀ n, Set (X n))
    (hA : (internalSet U A).Nonempty) (hB : (internalSet U B).Nonempty)
    (hsmall : loebMeasure U hU (internalSet U (fun n => A n + B n)) <
      loebMeasure U hU (internalSet U A) + loebMeasure U hU (internalSet U B)) :
    0 < loebMeasure U hU (AddAction.stabilizer ((U : Filter ℕ).Product X)
      (internalSet U (fun n => A n + B n)) : Set ((U : Filter ℕ).Product X)) := by
  rw [← internalAddSubgroup_stabilizer]
  have hbound := loebMeasure_internal_add_le U hU A B hA hB
  by_contra hn
  have hz : loebMeasure U hU (internalAddSubgroup U
      (fun n => AddAction.stabilizer (X n) (A n + B n)) :
        Set ((U : Filter ℕ).Product X)) = 0 := le_antisymm (le_of_not_gt hn) bot_le
  rw [hz, add_zero] at hbound
  exact (not_le_of_gt hsmall) hbound

theorem subcritical_cyclic_stabilizer
    (U : Ultrafilter ℕ) (hU : (U : Filter ℕ) ≤ atTop) (q : ℕ → ℕ+)
    (A B : ∀ n, Set (ZMod (q n : ℕ)))
    (hA : (internalSet U A).Nonempty) (hB : (internalSet U B).Nonempty)
    (hsmall : loebMeasure U hU (internalSet U (fun n => A n + B n)) <
      loebMeasure U hU (internalSet U A) + loebMeasure U hU (internalSet U B)) :
    ∃ (h : ℕ+) (p : ∀ n, ZMod (q n : ℕ) →+ ZMod (h : ℕ)),
      Function.Surjective (finiteQuotient U p) ∧
      (finiteQuotient U p).ker = AddAction.stabilizer
        ((U : Filter ℕ).Product (fun n => ZMod (q n : ℕ)))
        (internalSet U (fun n => A n + B n)) ∧
      (∀ n : ℕ, finiteQuotient U p
        (productProjection (U : Filter ℕ) (fun i => (n : ZMod (q i : ℕ)))) =
          (n : ZMod (h : ℕ))) ∧
      loebMeasure U hU (AddAction.stabilizer
        ((U : Filter ℕ).Product (fun n => ZMod (q n : ℕ)))
        (internalSet U (fun n => A n + B n)) :
          Set ((U : Filter ℕ).Product (fun n => ZMod (q n : ℕ)))) =
            1 / ((h : ℕ) : ℝ≥0∞) := by
  have hpos := subcritical_stabilizer_positive U hU A B hA hB hsmall
  rw [← internalAddSubgroup_stabilizer] at hpos ⊢
  exact exists_natural_quotient_of_positive_loebMeasure U hU q _ hpos

end Erdos335.Loeb
