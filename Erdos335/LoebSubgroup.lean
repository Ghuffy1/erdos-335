import Erdos335.LoebFiniteQuotient
import Mathlib.GroupTheory.Index

/-!
# Internal subgroups and finite quotients

Internal subgroups are the ultraproducts of their coordinate subgroups.
Surjective maps onto a fixed finite group identify their index exactly.
-/

set_option autoImplicit false

open Filter Set Topology
open scoped ENNReal

namespace Erdos335.Loeb

variable {I : Type*} {X : I → Type*} [∀ i, AddCommGroup (X i)]

def internalAddSubgroup (U : Ultrafilter I) (K : ∀ i, AddSubgroup (X i)) :
    AddSubgroup ((U : Filter I).Product X) where
  carrier := internalSet U (fun i => (K i : Set (X i)))
  zero_mem' := .of_forall fun i => (K i).zero_mem
  add_mem' := by
    intro x y hx hy
    induction x using Quotient.inductionOn with
    | h f =>
      induction y using Quotient.inductionOn with
      | h g =>
        change ∀ᶠ i in U, f i + g i ∈ K i
        filter_upwards [hx, hy] with i hxi hyi using (K i).add_mem hxi hyi
  neg_mem' := by
    intro x hx
    induction x using Quotient.inductionOn with
    | h f =>
      change ∀ᶠ i in U, -f i ∈ K i
      exact hx.mono fun i hi => (K i).neg_mem hi

theorem internalAddSubgroup_carrier (U : Ultrafilter I) (K : ∀ i, AddSubgroup (X i)) :
    (internalAddSubgroup U K : Set ((U : Filter I).Product X)) =
      internalSet U (fun i => (K i : Set (X i))) := rfl

theorem finiteQuotient_ker {G : Type*} [Finite G] [AddCommGroup G]
    (U : Ultrafilter I) (p : ∀ i, X i →+ G) :
    (finiteQuotient U p).ker = internalAddSubgroup U (fun i => (p i).ker) := by
  ext x
  induction x using Quotient.inductionOn with
  | h f =>
    change finiteValue U (fun i => p i (f i)) = 0 ↔ ∀ᶠ i in U, p i (f i) = 0
    exact finiteValue_eq_iff U _ 0

theorem internalAddSubgroup_index_of_quotients {G : Type*} [Finite G] [AddCommGroup G]
    (U : Ultrafilter I) (p : ∀ i, X i →+ G) (hp : ∀ i, Function.Surjective (p i)) :
    (internalAddSubgroup U (fun i => (p i).ker)).index = Nat.card G := by
  rw [← finiteQuotient_ker, AddSubgroup.index_eq_card]
  exact Nat.card_congr
    (QuotientAddGroup.quotientKerEquivOfSurjective (finiteQuotient U p)
      (finiteQuotient_surjective U p hp)).toEquiv

theorem countingRatio_subgroup {H : Type*} [AddCommGroup H] [Finite H]
    (K : AddSubgroup H) : countingRatio (K : Set H) = 1 / (K.index : ℝ≥0∞) := by
  have hK : (Nat.card K : ℝ≥0∞) ≠ 0 := by exact_mod_cast Nat.card_pos.ne'
  have hcard : (Nat.card H : ℝ≥0∞) = (Nat.card K : ℝ≥0∞) * K.index := by
    exact_mod_cast K.card_mul_index.symm
  calc
    countingRatio (K : Set H) = (Nat.card K : ℝ≥0∞) / ((Nat.card K : ℝ≥0∞) * K.index) := by
      rw [countingRatio, hcard]
      rfl
    _ = (Nat.card K : ℝ≥0∞) * 1 / ((Nat.card K : ℝ≥0∞) * K.index) := by rw [mul_one]
    _ = 1 / (K.index : ℝ≥0∞) := ENNReal.mul_div_mul_left _ _ hK (by simp)

theorem loebMeasure_internalSubgroup_of_quotients
    {Y : ℕ → Type*} [∀ n, AddCommGroup (Y n)] [∀ n, Finite (Y n)]
    {G : Type*} [Finite G] [AddCommGroup G]
    (U : Ultrafilter ℕ) (hU : (U : Filter ℕ) ≤ atTop)
    (p : ∀ n, Y n →+ G) (hp : ∀ n, Function.Surjective (p n)) :
    loebMeasure U hU (internalAddSubgroup U (fun n => (p n).ker) :
      Set ((U : Filter ℕ).Product Y)) = 1 / (Nat.card G : ℝ≥0∞) := by
  rw [internalAddSubgroup_carrier, loebMeasure_internal]
  have hratio : ∀ n, countingRatio ((p n).ker : Set (Y n)) = 1 / (Nat.card G : ℝ≥0∞) := by
    intro n
    rw [countingRatio_subgroup]
    have hindex : (p n).ker.index = Nat.card G := by
      rw [AddSubgroup.index_eq_card]
      exact Nat.card_congr (QuotientAddGroup.quotientKerEquivOfSurjective (p n) (hp n)).toEquiv
    rw [hindex]
  apply tendsto_nhds_unique (tendsto_ultraCount U _)
  simpa only [hratio] using
    (tendsto_const_nhds : Tendsto (fun _ : ℕ => 1 / (Nat.card G : ℝ≥0∞))
      (U : Filter ℕ) (𝓝 (1 / (Nat.card G : ℝ≥0∞))))

end Erdos335.Loeb
