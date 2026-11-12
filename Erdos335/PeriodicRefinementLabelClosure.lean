import Erdos335.PeriodicRefinementLabelClosureCore

/-!
# Closure of finite periodic labels under a cross-window sum

Private proof development. Verification status is recorded separately. The strict label frame explicitly retains
the active translation equality at every literal fine residue.
-/

set_option autoImplicit false

open scoped Pointwise BigOperators

noncomputable section

namespace Erdos335.PeriodicRefinementLabelClosure

variable {G : Type*} [AddCommGroup G] [Fintype G] [DecidableEq G]

structure StrictRightFrame {R S : Finset G} {a b : ℝ}
    (p : LocalProfile R S a b) (Q : Finset G) where
  active : Finset G
  active_subset : active ⊆ R
  background_full : ∀ r ∈ R \ active, p.left r = 1
  active_translation : ∀ v ∈ S \ Q, ∀ r ∈ active, p.output (r + v) = p.left r

def LabelFrame {R S : Finset G} {a b : ℝ}
    (p : LocalProfile R S a b) : LocalLabel G → Prop
  | .left P => Nonempty (StrictRightFrame p.swap P)
  | .right Q => Nonempty (StrictRightFrame p Q)
  | .both P Q => ∀ r ∈ R \ P, ∀ v ∈ S \ Q, p.output (r + v) = 0

def CrossInequality {R S : Finset G} {a b : ℝ}
    (p q target : LocalProfile R S a b) : Prop :=
  ∀ r v, 0 < p.left r → 0 < q.right v →
    max (p.left r) (q.right v) ≤ target.output (r + v)

theorem positive_outside_mask_of_not_indicator
    (f : G → ℝ) (R P : Finset G)
    (hbound : ∀ r, 0 ≤ f r ∧ f r ≤ 1) (hzero : ∀ r ∉ R, f r = 0)
    (hmass : (∑ r, f r) = (P.card : ℝ)) (hnot : ¬IsIndicator f P) :
    ∃ r ∈ R \ P, 0 < f r := by
  classical
  by_contra hnone
  apply hnot
  apply indicator_of_supported_mass f P (fun r => (hbound r).2) ?_ hmass
  intro r hrP
  by_cases hrR : r ∈ R
  · have hn : ¬0 < f r := fun hpos => hnone ⟨r, Finset.mem_sdiff.mpr ⟨hrR, hrP⟩, hpos⟩
    exact le_antisymm (le_of_not_gt hn) (hbound r).1
  · exact hzero r hrR

theorem same_label_one_indicator
    {R S : Finset G} {a b : ℝ} (p q : LocalProfile R S a b)
    (label : LocalLabel G) (hp : HasLabel p label) (hq : HasLabel q label) :
    (∀ r, p.left r = 0 ∨ p.left r = 1) ∨
      (∀ v, q.right v = 0 ∨ q.right v = 1) := by
  cases label with
  | left P => exact Or.inl (indicator_zero_or_one p.left P hp.1)
  | right Q => exact Or.inr (indicator_zero_or_one q.right Q hq.1)
  | both P Q => exact Or.inl (indicator_zero_or_one p.left P hp.1)

theorem strict_right_label_closed
    {R S : Finset G} {a b : ℝ} (p q target : LocalProfile R S a b)
    (ha : 0 < a) (hb : 0 < b) (hgap : a + b < ((R + S).card : ℝ))
    (label : LocalLabel G) (Q : Finset G)
    (hp : HasLabel p label) (hq : HasLabel q label)
    (htarget : HasLabel target (.right Q))
    (frame : StrictRightFrame target Q) (hcross : CrossInequality p q target) :
    label = .right Q := by
  classical
  by_cases hqMask : IsIndicator q.right Q
  · exact label_eq_right_of_indicator q ha hb hgap label hq Q hqMask htarget.2
  obtain ⟨v, hv, hvpos⟩ := positive_outside_mask_of_not_indicator q.right S Q
    q.right_bound q.right_zero (q.right_mass.trans (right_mask_card target Q htarget.1)) hqMask
  have honeSide := same_label_one_indicator p q label hp hq
  have hOutputOne (r : G) (hr : r ∈ frame.active) (hrpos : 0 < p.left r) :
      target.output (r + v) = 1 := by
    have hle := hcross r v hrpos hvpos
    have hone : (1 : ℝ) ≤ max (p.left r) (q.right v) := by
      rcases honeSide with hleft | hright
      · rcases hleft r with hz | ho
        · rw [hz] at hrpos
          exact False.elim ((lt_irrefl 0) hrpos)
        · rw [ho]
          exact le_max_left _ _
      · rcases hright v with hz | ho
        · rw [hz] at hvpos
          exact False.elim ((lt_irrefl 0) hvpos)
        · rw [ho]
          exact le_max_right _ _
    exact le_antisymm (target.output_bound _).2 (hone.trans hle)
  have hTargetLeftOne (r : G) (hr : r ∈ frame.active) (hrpos : 0 < p.left r) :
      target.left r = 1 :=
    (frame.active_translation v hv r hr).symm.trans (hOutputOne r hr hrpos)
  have hle : ∀ r, p.left r ≤ target.left r := by
    intro r
    by_cases hrR : r ∈ R
    · by_cases hrI : r ∈ frame.active
      · by_cases hrpos : 0 < p.left r
        · rw [hTargetLeftOne r hrI hrpos]
          exact (p.left_bound r).2
        · exact (le_of_not_gt hrpos).trans (target.left_bound r).1
      · rw [frame.background_full r (Finset.mem_sdiff.mpr ⟨hrR, hrI⟩)]
        exact (p.left_bound r).2
    · rw [p.left_zero r hrR, target.left_zero r hrR]
  have hLeftEq : p.left = target.left := eq_of_pointwise_le_of_sum_eq p.left target.left hle
    (p.left_mass.trans target.left_mass.symm)
  have hLeft01 : ∀ r, p.left r = 0 ∨ p.left r = 1 := by
    intro r
    by_cases hrpos : 0 < p.left r
    · right
      have hrR : r ∈ R := by
        by_contra hr
        rw [p.left_zero r hr] at hrpos
        exact (lt_irrefl 0) hrpos
      apply (congrFun hLeftEq r).trans
      by_cases hrI : r ∈ frame.active
      · exact hTargetLeftOne r hrI hrpos
      · exact frame.background_full r (Finset.mem_sdiff.mpr ⟨hrR, hrI⟩)
    · exact Or.inl (le_antisymm (le_of_not_gt hrpos) (p.left_bound r).1)
  let P := FiniteProfiles.positiveProfileSupport p.left
  have hPMask : IsIndicator p.left P := indicator_of_zero_or_one p.left hLeft01
  have hTargetPMask : IsIndicator target.left P := by
    intro r
    exact (congrFun hLeftEq r).symm.trans (hPMask r)
  have hPsat : ((P + S).card : ℝ) = a + b := by
    rcases both_periodic_baseline_saturated target ha hb hgap P Q hTargetPMask htarget.1
        with hs | hs
    · exact hs
    · exact False.elim (not_lt_of_ge hs.ge htarget.2)
  have hRightEq := partner_eq_of_saturated_left p target ha hb hgap P hPMask hTargetPMask hPsat
  have hpQ : IsIndicator p.right Q := by
    intro r
    exact (congrFun hRightEq r).trans (htarget.1 r)
  exact label_eq_right_of_indicator p ha hb hgap label hp Q hpQ htarget.2

theorem saturated_label_closed
    {R S : Finset G} {a b : ℝ} (p q target : LocalProfile R S a b)
    (ha : 0 < a) (hb : 0 < b) (hgap : a + b < ((R + S).card : ℝ))
    (label : LocalLabel G) (P Q : Finset G)
    (hp : HasLabel p label) (hq : HasLabel q label)
    (htarget : HasLabel target (.both P Q))
    (hforbidden : ∀ r ∈ R \ P, ∀ v ∈ S \ Q, target.output (r + v) = 0)
    (hcross : CrossInequality p q target) : label = .both P Q := by
  classical
  by_cases hpP : IsIndicator p.left P
  · have hRightEq := partner_eq_of_saturated_left p target ha hb hgap P hpP htarget.1 htarget.2.2.1
    have hpQ : IsIndicator p.right Q := by
      intro r
      exact (congrFun hRightEq r).trans (htarget.2.1 r)
    exact label_eq_both_of_indicators p label hp P Q hpP hpQ htarget.2.2.1 htarget.2.2.2
  by_cases hqQ : IsIndicator q.right Q
  · have hLeftEq := partner_eq_of_saturated_right q target ha hb hgap Q hqQ htarget.2.1 htarget.2.2.2
    have hqP : IsIndicator q.left P := by
      intro r
      exact (congrFun hLeftEq r).trans (htarget.1 r)
    exact label_eq_both_of_indicators q label hq P Q hqP hqQ htarget.2.2.1 htarget.2.2.2
  obtain ⟨r, hr, hrpos⟩ := positive_outside_mask_of_not_indicator p.left R P
    p.left_bound p.left_zero (p.left_mass.trans (left_mask_card target P htarget.1)) hpP
  obtain ⟨v, hv, hvpos⟩ := positive_outside_mask_of_not_indicator q.right S Q
    q.right_bound q.right_zero (q.right_mass.trans (right_mask_card target Q htarget.2.1)) hqQ
  have hle := hcross r v hrpos hvpos
  rw [hforbidden r hr v hv] at hle
  exact False.elim (not_le_of_gt hrpos ((le_max_left _ _).trans hle))

theorem same_label_sum_has_same_label
    {R S : Finset G} {a b : ℝ} (p q target : LocalProfile R S a b)
    (ha : 0 < a) (hb : 0 < b) (hgap : a + b < ((R + S).card : ℝ))
    (sourceLabel targetLabel : LocalLabel G)
    (hp : HasLabel p sourceLabel) (hq : HasLabel q sourceLabel)
    (htarget : HasLabel target targetLabel)
    (frame : LabelFrame target targetLabel) (hcross : CrossInequality p q target) :
    sourceLabel = targetLabel := by
  cases targetLabel with
  | right Q =>
      obtain ⟨rightFrame⟩ := frame
      exact strict_right_label_closed p q target ha hb hgap sourceLabel Q hp hq htarget rightFrame hcross
  | left P =>
      obtain ⟨leftFrame⟩ := frame
      have hcrossSwap : CrossInequality q.swap p.swap target.swap := by
        intro r v hr hv
        have h := hcross v r hv hr
        simpa only [LocalProfile.swap, add_comm, max_comm] using h
      have heq := strict_right_label_closed q.swap p.swap target.swap hb ha
        (by simpa only [add_comm] using hgap) sourceLabel.swap P hq.swap hp.swap
        htarget.swap leftFrame hcrossSwap
      have hback := congrArg LocalLabel.swap heq
      rw [LocalLabel.swap_swap] at hback
      exact hback
  | both P Q =>
      exact saturated_label_closed p q target ha hb hgap sourceLabel P Q hp hq htarget frame hcross

end Erdos335.PeriodicRefinementLabelClosure

end
