import Erdos335.CyclicQuotients
import Erdos335.LoebSubgroup

/-!
# Kneser's inequality for internal sets

The finite stabilizer inequality passes to normalized counting limits. The
stabilizer in this statement is the internal coordinate stabilizer.
-/

set_option autoImplicit false

open Filter Set Topology
open scoped ENNReal Pointwise

namespace Erdos335.Loeb

theorem countingRatio_add_le
    {G : Type*} [AddCommGroup G] [Finite G]
    (A B : Set G) (hA : A.Nonempty) (hB : B.Nonempty) :
    countingRatio A + countingRatio B ≤ countingRatio (A + B) +
      countingRatio (AddAction.stabilizer G (A + B) : Set G) := by
  classical
  let S := A.toFinite.toFinset
  let T := B.toFinite.toFinset
  have hScoe : (S : Set G) = A := by simp [S]
  have hTcoe : (T : Set G) = B := by simp [T]
  have hS : S.Nonempty := by
    obtain ⟨x, hx⟩ := hA
    exact ⟨x, by simpa [S] using hx⟩
  have hT : T.Nonempty := by
    obtain ⟨x, hx⟩ := hB
    exact ⟨x, by simpa [T] using hx⟩
  have hsum : ((S + T : Finset G) : Set G) = A + B := by
    rw [Finset.coe_add, hScoe, hTcoe]
  have hcard : S.card + T.card ≤ (S + T).card + (S + T).addStab.card := by
    by_cases hsmall : (S + T).card < S.card + T.card
    · exact card_deficit_le_stabilizer S T hS hT hsmall
    · omega
  have hAcard : A.ncard = S.card := by rw [← hScoe]; simp
  have hBcard : B.ncard = T.card := by rw [← hTcoe]; simp
  have hCcard : (A + B).ncard = (S + T).card := by
    rw [← hsum]
    simp only [Set.ncard_coe_finset]
  have hKcard : (AddAction.stabilizer G (A + B) : Set G).ncard =
      (S + T).addStab.card := by
    change Nat.card (AddAction.stabilizer G (A + B)) = _
    rw [← hsum]
    exact natCard_stabilizer_eq_card (S + T) (hS.add hT)
  simp only [countingRatio, hAcard, hBcard, hCcard, hKcard, ← ENNReal.add_div]
  exact ENNReal.div_le_div_right (by exact_mod_cast hcard) _

theorem loebMeasure_internal_add_le
    {X : ℕ → Type*} [∀ n, AddCommGroup (X n)] [∀ n, Finite (X n)]
    (U : Ultrafilter ℕ) (hU : (U : Filter ℕ) ≤ atTop)
    (A B : ∀ n, Set (X n))
    (hA : (internalSet U A).Nonempty) (hB : (internalSet U B).Nonempty) :
    loebMeasure U hU (internalSet U A) + loebMeasure U hU (internalSet U B) ≤
      loebMeasure U hU (internalSet U (fun n => A n + B n)) +
        loebMeasure U hU (internalAddSubgroup U
          (fun n => AddAction.stabilizer (X n) (A n + B n)) :
            Set ((U : Filter ℕ).Product X)) := by
  rw [internalAddSubgroup_carrier]
  simp only [loebMeasure_internal]
  apply le_of_tendsto_of_tendsto
    ((tendsto_ultraCount U A).add (tendsto_ultraCount U B))
    ((tendsto_ultraCount U (fun n => A n + B n)).add
      (tendsto_ultraCount U (fun n => (AddAction.stabilizer (X n) (A n + B n) : Set (X n)))))
  filter_upwards [(internalSet_nonempty_iff U A).mp hA, (internalSet_nonempty_iff U B).mp hB]
    with n hAn hBn
  exact countingRatio_add_le (A n) (B n) hAn hBn

theorem internal_stabilizer_add_mem
    {I : Type*} {X : I → Type*} [∀ i, AddCommGroup (X i)]
    (U : Ultrafilter I) (C : ∀ i, Set (X i))
    (k x : (U : Filter I).Product X)
    (hk : k ∈ internalAddSubgroup U (fun i => AddAction.stabilizer (X i) (C i)))
    (hx : x ∈ internalSet U C) : k + x ∈ internalSet U C := by
  induction k using Quotient.inductionOn with
  | h a =>
    induction x using Quotient.inductionOn with
    | h b =>
      change ∀ᶠ i in U, a i + b i ∈ C i
      filter_upwards [hk, hx] with i hki hxi
      have hfix : a i +ᵥ C i = C i := hki
      rw [← hfix]
      exact ⟨b i, hxi, rfl⟩

theorem internal_stabilizer_le_of_subset
    {I : Type*} {X : I → Type*} [∀ i, AddCommGroup (X i)]
    (U : Ultrafilter I) (C : ∀ i, Set (X i))
    (H : AddSubgroup ((U : Filter I).Product X))
    (hne : (internalSet U C).Nonempty) (hC : internalSet U C ⊆ H) :
    internalAddSubgroup U (fun i => AddAction.stabilizer (X i) (C i)) ≤ H := by
  intro k hk
  obtain ⟨x, hx⟩ := hne
  have hsum := hC (internal_stabilizer_add_mem U C k x hk hx)
  simpa only [add_sub_cancel_right] using H.sub_mem hsum (hC hx)

end Erdos335.Loeb
