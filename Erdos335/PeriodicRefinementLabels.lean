import Erdos335.FiniteCriticalCrossBaselines
import Erdos335.FiniteProfileSupport

/-!
# Finite labels for the periodic-summand refinement

Private proof development. Verification status is recorded separately. A saturated periodic mask has one compatible
partner profile. Two periodic masks have a saturated cross-baseline.
-/

set_option autoImplicit false

open scoped Pointwise BigOperators

noncomputable section

namespace Erdos335.PeriodicRefinementLabels

variable {G : Type*} [AddCommGroup G] [DecidableEq G]

theorem compatible_partner_card_bound
    (P R S U T : Finset G)
    (hP : P.Nonempty) (hT : T.Nonempty) (hPR : P ⊆ R)
    (hPS : P + S ⊆ U) (hRT : R + T ⊆ U) (houtside : ¬R + S ⊆ U) :
    P.card + T.card ≤ U.card := by
  by_contra hnot
  have hsmall : U.card < P.card + T.card := by omega
  have hcore : P + T ⊆ U :=
    (Finset.add_subset_add hPR (Finset.Subset.refl T)).trans hRT
  have hcomplete := FiniteKneser.extended_support_sum_subset
    (P := P) (Q := T) (S := R) (T := S) (U := U)
    hP hT hcore hRT hPS hsmall
  exact houtside (hcomplete.trans hcore)

def completionMask [Fintype G] (R U : Finset G) : Finset G := by
  classical
  exact Finset.univ.filter (fun t => t ∈ FiniteKneser.completionSet R U)

theorem mem_completionMask [Fintype G] (R U : Finset G) (t : G) :
    t ∈ completionMask R U ↔ ∀ r ∈ R, r + t ∈ U := by
  classical
  simp only [completionMask, FiniteKneser.completionSet, Finset.mem_filter,
    Finset.mem_univ, true_and, Set.mem_setOf_eq]
  constructor
  · intro ht r hr
    simpa only [add_comm] using ht r hr
  · intro ht r hr
    simpa only [add_comm] using ht r hr

theorem saturated_partner_eq_completion [Fintype G]
    (P R S U T : Finset G)
    (hP : P.Nonempty) (hT : T.Nonempty) (hPR : P ⊆ R)
    (hPS : P + S ⊆ U) (hRT : R + T ⊆ U) (houtside : ¬R + S ⊆ U)
    (hsaturated : U.card ≤ P.card + T.card) :
    U.card = P.card + T.card ∧ T = completionMask R U := by
  classical
  have hTC : T ⊆ completionMask R U := by
    intro t ht
    apply (mem_completionMask R U t).mpr
    intro r hr
    exact hRT (Finset.add_mem_add hr ht)
  have hRC : R + completionMask R U ⊆ U := by
    intro z hz
    obtain ⟨r, hr, t, ht, rfl⟩ := Finset.mem_add.mp hz
    exact (mem_completionMask R U t).mp ht r hr
  have hC : (completionMask R U).Nonempty := hT.mono hTC
  have hbound := compatible_partner_card_bound P R S U (completionMask R U)
    hP hC hPR hPS hRC houtside
  have hCTcard : (completionMask R U).card ≤ T.card := by omega
  have hTCeq : T = completionMask R U := Finset.eq_of_subset_of_card_le hTC hCTcard
  have hTbound := compatible_partner_card_bound P R S U T hP hT hPR hPS hRT houtside
  exact ⟨Nat.le_antisymm hsaturated hTbound, hTCeq⟩

theorem saturated_partner_profile [Fintype G]
    (P R S U : Finset G) (f : G → ℝ)
    (hP : P.Nonempty) (hPR : P ⊆ R) (hPS : P + S ⊆ U)
    (houtside : ¬R + S ⊆ U)
    (hf : ∀ t, 0 ≤ f t ∧ f t ≤ 1) (hzero : ∀ t ∉ S, f t = 0)
    (hpositive : 0 < ∑ t, f t)
    (htranslate : ∀ r ∈ R, ∀ t, f t ≤ if r + t ∈ U then (1 : ℝ) else 0)
    (hmass : (P.card : ℝ) + (∑ t, f t) = U.card) :
    completionMask R U ⊆ S ∧ U.card = P.card + (completionMask R U).card ∧
      ∀ t, f t = if t ∈ completionMask R U then (1 : ℝ) else 0 := by
  classical
  let T := FiniteProfiles.positiveProfileSupport f
  have hT : T.Nonempty :=
    FiniteProfiles.positiveProfileSupport_nonempty f (fun t => (hf t).1) hpositive
  have hTS : T ⊆ S := FiniteProfiles.positiveProfileSupport_subset f S hzero
  have hRT : R + T ⊆ U := by
    intro z hz
    obtain ⟨r, hr, t, ht, rfl⟩ := Finset.mem_add.mp hz
    by_contra hout
    have hle := htranslate r hr t
    rw [if_neg hout] at hle
    exact (not_lt_of_ge hle) (Finset.mem_filter.mp ht).2
  have hsumT : (∑ t ∈ T, f t) = ∑ t, f t :=
    FiniteProfiles.sum_positiveProfileSupport f (fun t => (hf t).1)
  have hsumBound : (∑ t, f t) ≤ (T.card : ℝ) := by
    rw [← hsumT]
    calc
      (∑ t ∈ T, f t) ≤ ∑ _t ∈ T, (1 : ℝ) :=
        Finset.sum_le_sum (fun t _ => (hf t).2)
      _ = (T.card : ℝ) := by simp
  have hsaturated : U.card ≤ P.card + T.card := by
    have hreal : (U.card : ℝ) ≤ (P.card : ℝ) + T.card := by linarith
    exact_mod_cast hreal
  obtain ⟨hcard, hTC⟩ := saturated_partner_eq_completion P R S U T
    hP hT hPR hPS hRT houtside hsaturated
  have hcardReal : (U.card : ℝ) = (P.card : ℝ) + T.card := by exact_mod_cast hcard
  have hsumExact : (∑ t ∈ T, f t) = (T.card : ℝ) := by linarith
  have hfull : ∀ t ∈ T, f t = 1 := by
    apply (Finset.sum_eq_sum_iff_of_le (fun t _ => (hf t).2)).mp
    simpa using hsumExact
  have hindicator : ∀ t, f t = if t ∈ T then (1 : ℝ) else 0 := by
    intro t
    by_cases ht : t ∈ T
    · rw [if_pos ht]
      exact hfull t ht
    · rw [if_neg ht]
      have hnot : ¬0 < f t := by
        simpa only [T, FiniteProfiles.positiveProfileSupport, Finset.mem_filter,
          Finset.mem_univ, true_and] using ht
      exact le_antisymm (le_of_not_gt hnot) (hf t).1
  refine ⟨?_, ?_, ?_⟩
  · simpa only [hTC] using hTS
  · simpa only [hTC] using hcard
  · simpa only [hTC] using hindicator

theorem saturated_partner_profiles_unique [Fintype G]
    (P R S U : Finset G) (f g : G → ℝ)
    (hP : P.Nonempty) (hPR : P ⊆ R) (hPS : P + S ⊆ U)
    (houtside : ¬R + S ⊆ U)
    (hf : ∀ t, 0 ≤ f t ∧ f t ≤ 1) (hg : ∀ t, 0 ≤ g t ∧ g t ≤ 1)
    (hfzero : ∀ t ∉ S, f t = 0) (hgzero : ∀ t ∉ S, g t = 0)
    (hfpositive : 0 < ∑ t, f t) (hgpositive : 0 < ∑ t, g t)
    (hftranslate : ∀ r ∈ R, ∀ t, f t ≤ if r + t ∈ U then (1 : ℝ) else 0)
    (hgtranslate : ∀ r ∈ R, ∀ t, g t ≤ if r + t ∈ U then (1 : ℝ) else 0)
    (hfmass : (P.card : ℝ) + (∑ t, f t) = U.card)
    (hgmass : (P.card : ℝ) + (∑ t, g t) = U.card) : f = g := by
  obtain ⟨_, _, hfprofile⟩ := saturated_partner_profile P R S U f
    hP hPR hPS houtside hf hfzero hfpositive hftranslate hfmass
  obtain ⟨_, _, hgprofile⟩ := saturated_partner_profile P R S U g
    hP hPR hPS houtside hg hgzero hgpositive hgtranslate hgmass
  funext t
  exact (hfprofile t).trans (hgprofile t).symm

theorem both_periodic_profiles_have_saturated_baseline [Fintype G]
    (P Q R S : Finset G) (c : G → ℝ)
    (hP : P.Nonempty) (hQ : Q.Nonempty) (hPR : P ⊆ R) (hQS : Q ⊆ S)
    (hc : ∀ u, 0 ≤ c u)
    (hfull : ∀ u ∈ (P + S) ∪ (R + Q), c u = 1)
    (hmass : (∑ u, c u) = (P.card : ℝ) + Q.card)
    (houtside : ¬R + S ⊆ (P + S) ∪ (R + Q)) :
    ((P + S) ∪ (R + Q)).card = P.card + Q.card ∧
      (P + S = (P + S) ∪ (R + Q) ∨ R + Q = (P + S) ∪ (R + Q)) := by
  classical
  let U := (P + S) ∪ (R + Q)
  have hsumU : (∑ u ∈ U, c u) = (U.card : ℝ) := by
    calc
      (∑ u ∈ U, c u) = ∑ _u ∈ U, (1 : ℝ) := Finset.sum_congr rfl (fun u hu => hfull u hu)
      _ = (U.card : ℝ) := by simp
  have hsumLe : (∑ u ∈ U, c u) ≤ ∑ u, c u :=
    Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ U) (fun u _ _ => hc u)
  have hcard : U.card ≤ P.card + Q.card := by
    rw [hsumU, hmass] at hsumLe
    exact_mod_cast hsumLe
  exact FiniteKneser.critical_cross_union_has_full_baseline P Q R S U
    hP hQ hPR hQS rfl hcard houtside

end Erdos335.PeriodicRefinementLabels

end
