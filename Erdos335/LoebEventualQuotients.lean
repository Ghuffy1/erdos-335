import Erdos335.LoebSubgroup

/-!
# Finite quotients on an ultrafilter-large set of coordinates

Local models only supply their finite quotient on a set belonging to the
ultrafilter. Values at the remaining coordinates do not affect the quotient
or the Loeb measure of its kernel.
-/

set_option autoImplicit false

open Filter Set Topology
open scoped ENNReal

namespace Erdos335.Loeb

variable {I G : Type*} {X : I → Type*}
  [∀ i, AddCommGroup (X i)] [Finite G] [AddCommGroup G]

theorem finiteQuotient_comp
    {H : Type*} [Finite H] [AddCommGroup H]
    (U : Ultrafilter I) (p : ∀ i, X i →+ G) (q : G →+ H) :
    finiteQuotient U (fun i => q.comp (p i)) = q.comp (finiteQuotient U p) := by
  apply AddMonoidHom.ext
  intro x
  induction x using Quotient.inductionOn with
  | h f =>
    change finiteValue U (fun i => q (p i (f i))) =
      q (finiteValue U (fun i => p i (f i)))
    apply finiteValue_eq_of_eventually
    exact (eventually_eq_finiteValue U (fun i => p i (f i))).mono
      fun i hi => congrArg q hi

theorem finiteQuotient_surjective_of_eventually
    (U : Ultrafilter I) (p : ∀ i, X i →+ G)
    (hp : ∀ᶠ i in U, Function.Surjective (p i)) :
    Function.Surjective (finiteQuotient U p) := by
  classical
  intro a
  let f : ∀ i, X i := fun i =>
    if hi : Function.Surjective (p i) then (hi a).choose else 0
  refine ⟨(f : (U : Filter I).Product X), ?_⟩
  change finiteValue U (fun i => p i (f i)) = a
  apply finiteValue_eq_of_eventually
  apply hp.mono
  intro i hi
  simpa only [f, dite_eq_left hi] using (hi a).choose_spec

theorem internalAddSubgroup_index_of_eventually_quotients
    (U : Ultrafilter I) (p : ∀ i, X i →+ G)
    (hp : ∀ᶠ i in U, Function.Surjective (p i)) :
    (internalAddSubgroup U (fun i => (p i).ker)).index = Nat.card G := by
  rw [← finiteQuotient_ker, AddSubgroup.index_eq_card]
  exact Nat.card_congr
    (QuotientAddGroup.quotientKerEquivOfSurjective (finiteQuotient U p)
      (finiteQuotient_surjective_of_eventually U p hp)).toEquiv

theorem loebMeasure_internalSubgroup_of_eventually_quotients
    {Y : ℕ → Type*} [∀ n, AddCommGroup (Y n)] [∀ n, Finite (Y n)]
    (U : Ultrafilter ℕ) (hU : (U : Filter ℕ) ≤ atTop)
    (p : ∀ n, Y n →+ G) (hp : ∀ᶠ n in U, Function.Surjective (p n)) :
    loebMeasure U hU (internalAddSubgroup U (fun n => (p n).ker) :
      Set ((U : Filter ℕ).Product Y)) = 1 / (Nat.card G : ℝ≥0∞) := by
  rw [internalAddSubgroup_carrier, loebMeasure_internal]
  have hratio : ∀ᶠ n in U,
      countingRatio ((p n).ker : Set (Y n)) = 1 / (Nat.card G : ℝ≥0∞) := by
    apply hp.mono
    intro n hn
    rw [countingRatio_subgroup]
    have hindex : (p n).ker.index = Nat.card G := by
      rw [AddSubgroup.index_eq_card]
      exact Nat.card_congr (QuotientAddGroup.quotientKerEquivOfSurjective (p n) hn).toEquiv
    rw [hindex]
  apply tendsto_nhds_unique (tendsto_ultraCount U _)
  exact tendsto_const_nhds.congr' (hratio.mono fun _ h => h.symm)

theorem eventually_bounded_index_of_positive_loebMeasure
    {Y : ℕ → Type*} [∀ n, AddCommGroup (Y n)] [∀ n, Finite (Y n)]
    (U : Ultrafilter ℕ) (hU : (U : Filter ℕ) ≤ atTop)
    (K : ∀ n, AddSubgroup (Y n))
    (hpos : 0 < loebMeasure U hU (internalAddSubgroup U K :
      Set ((U : Filter ℕ).Product Y))) :
    ∃ D : ℕ, ∀ᶠ n in U, (K n).index ≤ D := by
  by_contra hbounded
  have hindex : Tendsto (fun n => (K n).index) (U : Filter ℕ) atTop := by
    apply tendsto_atTop.2
    intro D
    have hnot : ¬ ∀ᶠ n in U, (K n).index ≤ D := fun h => hbounded ⟨D, h⟩
    exact (Ultrafilter.eventually_not.mpr hnot).mono fun n hn => (lt_of_not_ge hn).le
  have hzero : Tendsto (fun n => countingRatio (K n : Set (Y n)))
      (U : Filter ℕ) (𝓝 0) := by
    simpa only [countingRatio_subgroup, one_div, Function.comp_def] using
      ENNReal.tendsto_inv_nat_nhds_zero.comp hindex
  have hmass := tendsto_nhds_unique (tendsto_ultraCount U (fun n => (K n : Set (Y n)))) hzero
  rw [internalAddSubgroup_carrier, loebMeasure_internal, hmass] at hpos
  exact (lt_irrefl 0) hpos

end Erdos335.Loeb
