import Erdos335.PeriodicRefinementTwoTemplatesPacking
import Erdos335.PeriodicRefinementSparseBranch
import Erdos335.PeriodicCoreMaskBranch

/-!
# The two-template alternative and the complete periodic-summand reduction

Private proof development. Verification status is recorded separately.
The templates describe the ordinary periodic cores. Their literal fringes
are retained in the residue-sum interval tests.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Filter Set Topology
open scoped Pointwise

noncomputable section

namespace Erdos335.Proposed

def TwoTemplateBranch (A B : Set ℕ) : Prop :=
  ∃ (q : ℕ+) (S T : Finset (ZMod (q : ℕ))),
    S.Nonempty ∧ T.Nonempty ∧
    DensityEquivalent A (periodicSet S) ∧ DensityEquivalent B (periodicSet T) ∧
    (baseline A B S T).card = S.card + T.card ∧
    ResidueSumPacking (A \ periodicSet S) (B \ periodicSet T) q (baseline A B S T)

theorem two_template_baseline_swap (A B : Set ℕ) (q : ℕ+)
    (S T : Finset (ZMod (q : ℕ))) :
    baseline B A T S = baseline A B S T := by
  unfold baseline
  rw [add_comm (residues (q : ℕ) B) S,
    add_comm T (residues (q : ℕ) A), Finset.union_comm]

theorem TwoTemplateBranch.swap {A B : Set ℕ} (h : TwoTemplateBranch A B) :
    TwoTemplateBranch B A := by
  obtain ⟨q, S, T, hS, hT, hAS, hBT, hcard, hpacking⟩ := h
  have hW := two_template_baseline_swap A B q S T
  refine ⟨q, T, S, hT, hS, hBT, hAS, ?_, ?_⟩
  · rw [hW, hcard]
    exact Nat.add_comm _ _
  · rw [hW]
    exact (residue_sum_packing_comm (A \ periodicSet S) (B \ periodicSet T)
      q (baseline A B S T)).mp hpacking

theorem TwoTemplateBranch.hasDensity {A B : Set ℕ} {a b : ℝ}
    (h : TwoTemplateBranch A B) (hApos : A ⊆ Ioi 0) (hBpos : B ⊆ Ioi 0)
    (hA : HasDensity A a) (hB : HasDensity B b) : HasDensity (A + B) (a + b) := by
  obtain ⟨q, S, T, hS, hT, hAS, hBT, hcard, hpacking⟩ := h
  have hmissing := (residue_sum_packing_iff (A \ periodicSet S) (B \ periodicSet T)
    q (baseline A B S T) (fun n hn => hApos hn.1) (fun n hn => hBpos hn.1)).mp hpacking
  have hsum := (periodic_inputs_fringe_criterion A B S T hApos hBpos hS hT hAS hBT).mpr
    ⟨hcard, hmissing⟩
  have ha : a = (S.card : ℝ) / (q : ℕ) :=
    hA.unique (hAS.symm.hasDensity (hasDensity_periodicSet S))
  have hb : b = (T.card : ℝ) / (q : ℕ) :=
    hB.unique (hBT.symm.hasDensity (hasDensity_periodicSet T))
  simpa only [← ha, ← hb] using hsum

theorem two_template_branch_of_periodic_inputs
    (A B : Set ℕ) (a b : ℝ) (hApos : A ⊆ Ioi 0) (hBpos : B ⊆ Ioi 0)
    (hA : HasDensity A a) (hB : HasDensity B b) (hC : HasDensity (A + B) (a + b))
    (q : ℕ+) (S T : Finset (ZMod (q : ℕ))) (hS : S.Nonempty) (hT : T.Nonempty)
    (hAS : DensityEquivalent A (periodicSet S))
    (hBT : DensityEquivalent B (periodicSet T)) : TwoTemplateBranch A B := by
  have ha : a = (S.card : ℝ) / (q : ℕ) :=
    hA.unique (hAS.symm.hasDensity (hasDensity_periodicSet S))
  have hb : b = (T.card : ℝ) / (q : ℕ) :=
    hB.unique (hBT.symm.hasDensity (hasDensity_periodicSet T))
  have hcriterion := (periodic_inputs_fringe_criterion A B S T hApos hBpos hS hT hAS hBT).mp
    (by simpa only [← ha, ← hb] using hC)
  refine ⟨q, S, T, hS, hT, hAS, hBT, hcriterion.1, ?_⟩
  exact (residue_sum_packing_iff (A \ periodicSet S) (B \ periodicSet T)
    q (baseline A B S T) (fun n hn => hApos hn.1) (fun n hn => hBpos hn.1)).mpr hcriterion.2

theorem two_template_branch_of_saturated_periodic_summand
    (A B : Set ℕ) (a b : ℝ) (hApos : A ⊆ Ioi 0) (hBpos : B ⊆ Ioi 0)
    (ha : 0 < a) (hb : 0 < b) (hA : HasDensity A a) (hB : HasDensity B b)
    (hC : HasDensity (A + B) (a + b)) (hgap : a + b < gamma A B)
    (m : ℕ+) (P : Finset (ZMod (m : ℕ)))
    (hAP : DensityEquivalent A (periodicSet P))
    (heq : ((P + residues (m : ℕ) B).card : ℝ) / (m : ℕ) = a + b) :
    TwoTemplateBranch A B := by
  let W := residues (m : ℕ) B + P
  have hWmass : (W.card : ℝ) / (m : ℕ) = a + b := by
    simpa only [W, add_comm (residues (m : ℕ) B) P] using heq
  have hholes : Negligible (periodicSet W \ (A + B)) := by
    apply negligible_periodic_diff_of_singletons
    intro w hw
    have hh := missing_left_baseline_singleton (A := B) (B := A) hAP hw
    simpa only [add_comm B A] using hh
  have hout : Negligible ((A + B) \ periodicSet W) := by
    change HasDensity ((A + B) \ periodicSet W) 0
    have hd := hC.sdiff_of_negligible_reverse (hasDensity_periodicSet W) hholes
    simpa only [hWmass, sub_self] using hd
  obtain ⟨S, T, hS, hT, hAS, hBT, _, _⟩ := periodic_output_forces_periodic_inputs
    A B W a b hApos hBpos ha hb hA hB hC ⟨hout, hholes⟩ hgap
  exact two_template_branch_of_periodic_inputs A B a b hApos hBpos hA hB hC
    m S T hS hT hAS hBT

theorem periodic_summand_refinement_iff
    (A B : Set ℕ) (a b : ℝ) (hApos : A ⊆ Ioi 0) (hBpos : B ⊆ Ioi 0)
    (ha : 0 < a) (hb : 0 < b) (hA : HasDensity A a) (hB : HasDensity B b)
    (hgap : a + b < gamma A B) (m : ℕ+) (P : Finset (ZMod (m : ℕ)))
    (hAP : DensityEquivalent A (periodicSet P)) :
    HasDensity (A + B) (a + b) ↔ TwoTemplateBranch A B ∨ SparseSectionBranch A B := by
  constructor
  · intro hC
    let W := residues (m : ℕ) B + P
    have hholes : Negligible (periodicSet W \ (A + B)) := by
      apply negligible_periodic_diff_of_singletons
      intro w hw
      have hh := missing_left_baseline_singleton (A := B) (B := A) hAP hw
      simpa only [add_comm B A] using hh
    have hbound : (W.card : ℝ) / (m : ℕ) ≤ a + b := by
      have hnonneg := (hC.sdiff_of_negligible_reverse (hasDensity_periodicSet W) hholes).nonneg
      linarith
    by_cases hstrict : (W.card : ℝ) / (m : ℕ) < a + b
    · right
      apply sparse_branch_of_strict_periodic_summand A B a b hApos hBpos ha hb hA hB hC
        hgap m P hAP
      simpa only [W, add_comm (residues (m : ℕ) B) P] using hstrict
    · left
      apply two_template_branch_of_saturated_periodic_summand A B a b
        hApos hBpos ha hb hA hB hC hgap m P hAP
      have heq : (W.card : ℝ) / (m : ℕ) = a + b := le_antisymm hbound (not_lt.mp hstrict)
      simpa only [W, add_comm (residues (m : ℕ) B) P] using heq
  · rintro (h | h)
    · exact h.hasDensity hApos hBpos hA hB
    · exact h.hasDensity hApos hBpos hA hB

theorem periodic_summand_refinement_iff_of_either
    (A B : Set ℕ) (a b : ℝ) (hApos : A ⊆ Ioi 0) (hBpos : B ⊆ Ioi 0)
    (ha : 0 < a) (hb : 0 < b) (hA : HasDensity A a) (hB : HasDensity B b)
    (hgap : a + b < gamma A B)
    (hperiodic : ∃ (m : ℕ+) (P : Finset (ZMod (m : ℕ))),
      DensityEquivalent A (periodicSet P) ∨ DensityEquivalent B (periodicSet P)) :
    HasDensity (A + B) (a + b) ↔ TwoTemplateBranch A B ∨ SparseSectionBranch A B := by
  constructor
  · intro hC
    obtain ⟨m, P, hAP | hBP⟩ := hperiodic
    · exact (periodic_summand_refinement_iff A B a b hApos hBpos ha hb hA hB
        hgap m P hAP).mp hC
    · have hgamma : gamma B A = gamma A B := by
        unfold gamma modularCapacity
        simp only [add_comm]
      have hgap' : b + a < gamma B A := by
        simpa only [hgamma, add_comm b a] using hgap
      have hC' : HasDensity (B + A) (b + a) := by
        simpa only [add_comm A B, add_comm a b] using hC
      have hresult := (periodic_summand_refinement_iff B A b a hBpos hApos hb ha hB hA
        hgap' m P hBP).mp hC'
      rcases hresult with h | h
      · exact Or.inl h.swap
      · exact Or.inr h.swap
  · rintro (h | h)
    · exact h.hasDensity hApos hBpos hA hB
    · exact h.hasDensity hApos hBpos hA hB

end Erdos335.Proposed

end
