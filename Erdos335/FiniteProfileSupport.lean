import Erdos335.FiniteProfiles

/-!
# Positive support of a nonnegative finite profile
-/

set_option autoImplicit false

open scoped BigOperators Pointwise

namespace Erdos335.FiniteProfiles

noncomputable def positiveProfileSupport {G : Type*} [Fintype G] (f : G → ℝ) : Finset G := by
  classical
  exact Finset.univ.filter (fun r => 0 < f r)

theorem sum_positiveProfileSupport {G : Type*} [Fintype G]
    (f : G → ℝ) (hf : ∀ r, 0 ≤ f r) :
    (∑ r ∈ positiveProfileSupport f, f r) = ∑ r, f r := by
  classical
  apply Finset.sum_subset (Finset.filter_subset _ _)
  intro r hr hnot
  have hn : ¬0 < f r := by simpa [positiveProfileSupport] using hnot
  exact le_antisymm (le_of_not_gt hn) (hf r)

theorem positiveProfileSupport_nonempty {G : Type*} [Fintype G]
    (f : G → ℝ) (hf : ∀ r, 0 ≤ f r) (hpos : 0 < ∑ r, f r) :
    (positiveProfileSupport f).Nonempty := by
  classical
  by_contra hn
  have he : positiveProfileSupport f = ∅ := Finset.not_nonempty_iff_eq_empty.mp hn
  have hsum := sum_positiveProfileSupport f hf
  rw [he, Finset.sum_empty] at hsum
  linarith

theorem positiveProfileSupport_subset {G : Type*} [Fintype G]
    (f : G → ℝ) (R : Finset G) (hzero : ∀ r ∉ R, f r = 0) :
    positiveProfileSupport f ⊆ R := by
  classical
  intro r hr
  have hp : 0 < f r := (Finset.mem_filter.mp hr).2
  by_contra hn
  rw [hzero r hn] at hp
  exact lt_irrefl 0 hp

theorem periodic_output_forces_indicator_profiles
    {G : Type*} [AddCommGroup G] [Fintype G] [DecidableEq G]
    (R T U : Finset G) (a b : G → ℝ)
    (ha : ∀ r, 0 ≤ a r ∧ a r ≤ 1) (hb : ∀ r, 0 ≤ b r ∧ b r ≤ 1)
    (haR : ∀ r ∉ R, a r = 0) (hbT : ∀ r ∉ T, b r = 0)
    (haPos : 0 < ∑ r, a r) (hbPos : 0 < ∑ r, b r)
    (hleft : ∀ r, ∀ t ∈ T, a r ≤ if r + t ∈ U then (1 : ℝ) else 0)
    (hright : ∀ r ∈ R, ∀ t, b t ≤ if r + t ∈ U then (1 : ℝ) else 0)
    (hgap : ¬R + T ⊆ U)
    (hmass : (∑ r, a r) + (∑ r, b r) = U.card) :
    let P := positiveProfileSupport a
    let Q := positiveProfileSupport b
    U.card = P.card + Q.card ∧
      (∀ r, a r = if r ∈ P then 1 else 0) ∧
      (∀ r, b r = if r ∈ Q then 1 else 0) ∧
      (P + T) ∪ (R + Q) = U := by
  classical
  dsimp only
  let P := positiveProfileSupport a
  let Q := positiveProfileSupport b
  have hP : P.Nonempty := positiveProfileSupport_nonempty a (fun r => (ha r).1) haPos
  have hQ : Q.Nonempty := positiveProfileSupport_nonempty b (fun r => (hb r).1) hbPos
  have hPR : P ⊆ R := positiveProfileSupport_subset a R haR
  have hQT : Q ⊆ T := positiveProfileSupport_subset b T hbT
  have hPT : P + T ⊆ U := by
    rintro u hu
    obtain ⟨r, hr, t, ht, rfl⟩ := Finset.mem_add.mp hu
    by_contra hout
    have hb := hleft r t ht
    rw [if_neg hout] at hb
    exact not_lt_of_ge hb (Finset.mem_filter.mp hr).2
  have hRQ : R + Q ⊆ U := by
    rintro u hu
    obtain ⟨r, hr, t, ht, rfl⟩ := Finset.mem_add.mp hu
    by_contra hout
    have hb := hright r hr t
    rw [if_neg hout] at hb
    exact not_lt_of_ge hb (Finset.mem_filter.mp ht).2
  have hmass' : (∑ r ∈ P, a r) + (∑ r ∈ Q, b r) = U.card := by
    rw [sum_positiveProfileSupport a (fun r => (ha r).1),
      sum_positiveProfileSupport b (fun r => (hb r).1)]
    exact hmass
  obtain ⟨hcard, haFull, hbFull, hfill⟩ := periodic_output_forces_full_inputs P Q R T U a b
    hP hQ hPR hQT hPT hRQ hgap (fun r hr => (ha r).2) (fun r hr => (hb r).2) hmass'
  refine ⟨hcard, ?_, ?_, hfill⟩
  · intro r
    change a r = if r ∈ P then 1 else 0
    by_cases hr : r ∈ P
    · simpa only [if_pos hr] using haFull r hr
    · have hn : ¬0 < a r := by simpa [P, positiveProfileSupport] using hr
      simpa only [if_neg hr] using le_antisymm (le_of_not_gt hn) (ha r).1
  · intro r
    change b r = if r ∈ Q then 1 else 0
    by_cases hr : r ∈ Q
    · simpa only [if_pos hr] using hbFull r hr
    · have hn : ¬0 < b r := by simpa [Q, positiveProfileSupport] using hr
      simpa only [if_neg hr] using le_antisymm (le_of_not_gt hn) (hb r).1

end Erdos335.FiniteProfiles
