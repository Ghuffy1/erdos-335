import Erdos335.PeriodicRefinementLabels

/-!
# Finite profile contracts for periodic label closure

Private proof development. Verification status is recorded separately. All masses are sums over the fixed fine
quotient. Division by its cardinality gives the normalized window masses.
-/

set_option autoImplicit false

open scoped Pointwise BigOperators

noncomputable section

namespace Erdos335.PeriodicRefinementLabelClosure

variable {G : Type*} [AddCommGroup G] [Fintype G] [DecidableEq G]

def IsIndicator (f : G → ℝ) (P : Finset G) : Prop :=
  ∀ r, f r = if r ∈ P then (1 : ℝ) else 0

structure LocalProfile (R S : Finset G) (a b : ℝ) where
  left : G → ℝ
  right : G → ℝ
  output : G → ℝ
  left_bound : ∀ r, 0 ≤ left r ∧ left r ≤ 1
  right_bound : ∀ r, 0 ≤ right r ∧ right r ≤ 1
  output_bound : ∀ r, 0 ≤ output r ∧ output r ≤ 1
  left_zero : ∀ r ∉ R, left r = 0
  right_zero : ∀ r ∉ S, right r = 0
  left_mass : (∑ r, left r) = a
  right_mass : (∑ r, right r) = b
  output_mass : (∑ r, output r) = a + b
  literal_left : ∀ r, ∀ v ∈ S, left r ≤ output (r + v)
  literal_right : ∀ r ∈ R, ∀ v, right v ≤ output (r + v)

inductive LocalLabel (G : Type*) where
  | left (P : Finset G)
  | right (Q : Finset G)
  | both (P Q : Finset G)

instance localLabelFinite : Finite (LocalLabel G) := by
  classical
  let encode : LocalLabel G → Finset G ⊕ (Finset G ⊕ (Finset G × Finset G)) :=
    fun label => match label with
      | .left P => Sum.inl P
      | .right Q => Sum.inr (Sum.inl Q)
      | .both P Q => Sum.inr (Sum.inr (P, Q))
  refine Finite.of_injective encode ?_
  intro x y h
  cases x <;> cases y <;> simp_all [encode]

def HasLabel {R S : Finset G} {a b : ℝ} (p : LocalProfile R S a b) : LocalLabel G → Prop
  | .left P => IsIndicator p.left P ∧ ((P + S).card : ℝ) < a + b
  | .right Q => IsIndicator p.right Q ∧ ((R + Q).card : ℝ) < a + b
  | .both P Q => IsIndicator p.left P ∧ IsIndicator p.right Q ∧
      ((P + S).card : ℝ) = a + b ∧ ((R + Q).card : ℝ) = a + b

def LocalLabel.swap : LocalLabel G → LocalLabel G
  | .left P => .right P
  | .right Q => .left Q
  | .both P Q => .both Q P

theorem LocalLabel.swap_swap (label : LocalLabel G) : label.swap.swap = label := by
  cases label <;> rfl

def LocalProfile.swap {R S : Finset G} {a b : ℝ} (p : LocalProfile R S a b) :
    LocalProfile S R b a where
  left := p.right
  right := p.left
  output := p.output
  left_bound := p.right_bound
  right_bound := p.left_bound
  output_bound := p.output_bound
  left_zero := p.right_zero
  right_zero := p.left_zero
  left_mass := p.right_mass
  right_mass := p.left_mass
  output_mass := by simpa only [add_comm b a] using p.output_mass
  literal_left := by
    intro r v hv
    simpa only [add_comm r v] using p.literal_right v hv r
  literal_right := by
    intro r hr v
    simpa only [add_comm r v] using p.literal_left v r hr

theorem HasLabel.swap {R S : Finset G} {a b : ℝ} {p : LocalProfile R S a b}
    {label : LocalLabel G} (h : HasLabel p label) : HasLabel p.swap label.swap := by
  cases label with
  | left P =>
      exact ⟨h.1, by simpa only [add_comm S P, add_comm b a] using h.2⟩
  | right Q =>
      exact ⟨h.1, by simpa only [add_comm Q R, add_comm b a] using h.2⟩
  | both P Q =>
      exact ⟨h.2.1, h.1,
        by simpa only [add_comm Q R, add_comm b a] using h.2.2.2,
        by simpa only [add_comm S P, add_comm b a] using h.2.2.1⟩

theorem indicator_sum (f : G → ℝ) (P : Finset G) (h : IsIndicator f P) :
    (∑ r, f r) = (P.card : ℝ) := by
  classical
  calc
    _ = ∑ r : G, if r ∈ P then (1 : ℝ) else 0 :=
      Finset.sum_congr rfl (fun r _ => h r)
    _ = _ := by simp

theorem indicator_masks_eq (f : G → ℝ) (P Q : Finset G)
    (hP : IsIndicator f P) (hQ : IsIndicator f Q) : P = Q := by
  classical
  ext r
  have h := (hP r).symm.trans (hQ r)
  by_cases hrP : r ∈ P <;> by_cases hrQ : r ∈ Q <;> simp [hrP, hrQ] at h ⊢

theorem indicator_zero_or_one (f : G → ℝ) (P : Finset G) (h : IsIndicator f P) :
    ∀ r, f r = 0 ∨ f r = 1 := by
  intro r
  by_cases hr : r ∈ P
  · exact Or.inr (by simpa only [if_pos hr] using h r)
  · exact Or.inl (by simpa only [if_neg hr] using h r)

theorem indicator_of_zero_or_one (f : G → ℝ) (h : ∀ r, f r = 0 ∨ f r = 1) :
    IsIndicator f (FiniteProfiles.positiveProfileSupport f) := by
  classical
  intro r
  rcases h r with hr | hr <;> simp [FiniteProfiles.positiveProfileSupport, hr]

theorem eq_of_pointwise_le_of_sum_eq (f g : G → ℝ)
    (hle : ∀ r, f r ≤ g r) (hsum : (∑ r, f r) = ∑ r, g r) : f = g := by
  funext r
  exact (Finset.sum_eq_sum_iff_of_le (fun r _ => hle r)).mp hsum r (Finset.mem_univ r)

theorem indicator_of_supported_mass (f : G → ℝ) (P : Finset G)
    (hbound : ∀ r, f r ≤ 1) (hzero : ∀ r ∉ P, f r = 0)
    (hmass : (∑ r, f r) = (P.card : ℝ)) : IsIndicator f P := by
  classical
  let g := fun r => if r ∈ P then (1 : ℝ) else 0
  have hle : ∀ r, f r ≤ g r := by
    intro r
    by_cases hr : r ∈ P
    · simpa only [g, if_pos hr] using hbound r
    · simp only [g, if_neg hr, hzero r hr, le_refl]
  have hsum : (∑ r, f r) = ∑ r, g r := by simpa [g] using hmass
  have heq := eq_of_pointwise_le_of_sum_eq f g hle hsum
  intro r
  exact congrFun heq r

theorem left_mask_card {R S : Finset G} {a b : ℝ} (p : LocalProfile R S a b)
    (P : Finset G) (hP : IsIndicator p.left P) : a = (P.card : ℝ) :=
  p.left_mass.symm.trans (indicator_sum p.left P hP)

theorem right_mask_card {R S : Finset G} {a b : ℝ} (p : LocalProfile R S a b)
    (Q : Finset G) (hQ : IsIndicator p.right Q) : b = (Q.card : ℝ) :=
  p.right_mass.symm.trans (indicator_sum p.right Q hQ)

theorem left_mask_subset {R S : Finset G} {a b : ℝ} (p : LocalProfile R S a b)
    (P : Finset G) (hP : IsIndicator p.left P) : P ⊆ R := by
  intro r hr
  by_contra hnot
  have h := hP r
  rw [p.left_zero r hnot, if_pos hr] at h
  norm_num at h

theorem right_mask_subset {R S : Finset G} {a b : ℝ} (p : LocalProfile R S a b)
    (Q : Finset G) (hQ : IsIndicator p.right Q) : Q ⊆ S :=
  left_mask_subset p.swap Q hQ

theorem left_baseline_full {R S : Finset G} {a b : ℝ} (p : LocalProfile R S a b)
    (P : Finset G) (hP : IsIndicator p.left P) :
    ∀ u ∈ P + S, p.output u = 1 := by
  intro u hu
  obtain ⟨r, hr, v, hv, rfl⟩ := Finset.mem_add.mp hu
  have hle := p.literal_left r v hv
  rw [hP r, if_pos hr] at hle
  exact le_antisymm (p.output_bound _).2 hle

theorem right_baseline_full {R S : Finset G} {a b : ℝ} (p : LocalProfile R S a b)
    (Q : Finset G) (hQ : IsIndicator p.right Q) :
    ∀ u ∈ R + Q, p.output u = 1 := by
  intro u hu
  have h := left_baseline_full p.swap Q hQ u
  apply h
  simpa only [add_comm] using hu

theorem full_mask_card_le_mass (f : G → ℝ) (U : Finset G)
    (hnonneg : ∀ r, 0 ≤ f r) (hfull : ∀ r ∈ U, f r = 1) :
    (U.card : ℝ) ≤ ∑ r, f r := by
  classical
  have hsum : (∑ r ∈ U, f r) = (U.card : ℝ) := by
    calc
      (∑ r ∈ U, f r) = ∑ _r ∈ U, (1 : ℝ) := Finset.sum_congr rfl hfull
      _ = _ := by simp
  rw [← hsum]
  exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ U) (fun r _ _ => hnonneg r)

theorem both_periodic_baseline_saturated
    {R S : Finset G} {a b : ℝ} (p : LocalProfile R S a b)
    (ha : 0 < a) (hb : 0 < b) (hgap : a + b < ((R + S).card : ℝ))
    (P Q : Finset G) (hP : IsIndicator p.left P) (hQ : IsIndicator p.right Q) :
    ((P + S).card : ℝ) = a + b ∨ ((R + Q).card : ℝ) = a + b := by
  classical
  let U := (P + S) ∪ (R + Q)
  have hfull : ∀ r ∈ U, p.output r = 1 := by
    intro r hr
    rcases Finset.mem_union.mp hr with hr | hr
    · exact left_baseline_full p P hP r hr
    · exact right_baseline_full p Q hQ r hr
  have hUbound : (U.card : ℝ) ≤ a + b := by
    simpa only [p.output_mass] using full_mask_card_le_mass p.output U
      (fun r => (p.output_bound r).1) hfull
  have houtside : ¬R + S ⊆ U := by
    intro hsub
    have hcard : ((R + S).card : ℝ) ≤ U.card := by exact_mod_cast Finset.card_le_card hsub
    exact not_le_of_gt hgap (hcard.trans hUbound)
  have hPcard := left_mask_card p P hP
  have hQcard := right_mask_card p Q hQ
  have hPpositive : (0 : ℝ) < P.card := by rw [← hPcard]; exact ha
  have hQpositive : (0 : ℝ) < Q.card := by rw [← hQcard]; exact hb
  have hPne : P.Nonempty := Finset.card_pos.mp (by exact_mod_cast hPpositive)
  have hQne : Q.Nonempty := Finset.card_pos.mp (by exact_mod_cast hQpositive)
  obtain ⟨hcard, hsat⟩ := PeriodicRefinementLabels.both_periodic_profiles_have_saturated_baseline
    P Q R S p.output hPne hQne (left_mask_subset p P hP) (right_mask_subset p Q hQ)
    (fun r => (p.output_bound r).1) hfull
    (by rw [p.output_mass, ← hPcard, ← hQcard]) houtside
  have hUcard : (U.card : ℝ) = a + b := by
    rw [hcard, Nat.cast_add, ← hPcard, ← hQcard]
  rcases hsat with hs | hs
  · exact Or.inl (by rw [hs]; exact hUcard)
  · exact Or.inr (by rw [hs]; exact hUcard)

theorem saturated_left_partner_indicator
    {R S : Finset G} {a b : ℝ} (p : LocalProfile R S a b)
    (ha : 0 < a) (hb : 0 < b) (hgap : a + b < ((R + S).card : ℝ))
    (P : Finset G) (hP : IsIndicator p.left P) (hsat : ((P + S).card : ℝ) = a + b) :
    IsIndicator p.right (PeriodicRefinementLabels.completionMask R (P + S)) := by
  classical
  let U := P + S
  have hfull := left_baseline_full p P hP
  let f := fun r => if r ∈ U then (1 : ℝ) else 0
  have hle : ∀ r, f r ≤ p.output r := by
    intro r
    by_cases hr : r ∈ U
    · simpa only [f, if_pos hr, hfull r hr] using (le_refl (1 : ℝ))
    · simpa only [f, if_neg hr] using (p.output_bound r).1
  have hsum : (∑ r, f r) = ∑ r, p.output r :=
    (indicator_sum f U (fun _ => rfl)).trans (hsat.trans p.output_mass.symm)
  have hOutput : IsIndicator p.output U := by
    have heq := eq_of_pointwise_le_of_sum_eq f p.output hle hsum
    intro r
    exact (congrFun heq r).symm
  have houtside : ¬R + S ⊆ U := by
    intro hsub
    have hcard : ((R + S).card : ℝ) ≤ U.card := by exact_mod_cast Finset.card_le_card hsub
    exact not_le_of_gt hgap (hcard.trans_eq hsat)
  have hPcard := left_mask_card p P hP
  have hPpositive : (0 : ℝ) < P.card := by rw [← hPcard]; exact ha
  have hPne : P.Nonempty := Finset.card_pos.mp (by exact_mod_cast hPpositive)
  have htranslate : ∀ r ∈ R, ∀ t, p.right t ≤ if r + t ∈ U then (1 : ℝ) else 0 := by
    intro r hr t
    simpa only [hOutput (r + t)] using p.literal_right r hr t
  exact (PeriodicRefinementLabels.saturated_partner_profile P R S U p.right hPne
    (left_mask_subset p P hP) (Finset.Subset.refl U) houtside p.right_bound p.right_zero
    (by simpa only [p.right_mass] using hb) htranslate
    (by rw [p.right_mass, ← hPcard]; exact hsat.symm)).2.2

theorem partner_eq_of_saturated_left
    {R S : Finset G} {a b : ℝ} (p q : LocalProfile R S a b)
    (ha : 0 < a) (hb : 0 < b) (hgap : a + b < ((R + S).card : ℝ))
    (P : Finset G) (hP : IsIndicator p.left P) (hQ : IsIndicator q.left P)
    (hsat : ((P + S).card : ℝ) = a + b) : p.right = q.right := by
  have hp := saturated_left_partner_indicator p ha hb hgap P hP hsat
  have hq := saturated_left_partner_indicator q ha hb hgap P hQ hsat
  funext r
  exact (hp r).trans (hq r).symm

theorem partner_eq_of_saturated_right
    {R S : Finset G} {a b : ℝ} (p q : LocalProfile R S a b)
    (ha : 0 < a) (hb : 0 < b) (hgap : a + b < ((R + S).card : ℝ))
    (Q : Finset G) (hP : IsIndicator p.right Q) (hQ : IsIndicator q.right Q)
    (hsat : ((R + Q).card : ℝ) = a + b) : p.left = q.left := by
  exact partner_eq_of_saturated_left p.swap q.swap hb ha
    (by simpa only [add_comm] using hgap) Q hP hQ
    (by simpa only [add_comm] using hsat)

theorem label_eq_right_of_indicator
    {R S : Finset G} {a b : ℝ} (p : LocalProfile R S a b)
    (ha : 0 < a) (hb : 0 < b) (hgap : a + b < ((R + S).card : ℝ))
    (label : LocalLabel G) (hlabel : HasLabel p label)
    (Q : Finset G) (hQ : IsIndicator p.right Q) (hstrict : ((R + Q).card : ℝ) < a + b) :
    label = .right Q := by
  cases label with
  | left P =>
      rcases both_periodic_baseline_saturated p ha hb hgap P Q hlabel.1 hQ with hsat | hsat
      · exact False.elim (not_lt_of_ge hsat.ge hlabel.2)
      · exact False.elim (not_lt_of_ge hsat.ge hstrict)
  | right Q' =>
      have heq := indicator_masks_eq p.right Q' Q hlabel.1 hQ
      subst Q'
      rfl
  | both P Q' =>
      have heq := indicator_masks_eq p.right Q' Q hlabel.2.1 hQ
      subst Q'
      exact False.elim (not_lt_of_ge hlabel.2.2.2.ge hstrict)

theorem label_eq_both_of_indicators
    {R S : Finset G} {a b : ℝ} (p : LocalProfile R S a b)
    (label : LocalLabel G) (hlabel : HasLabel p label)
    (P Q : Finset G) (hP : IsIndicator p.left P) (hQ : IsIndicator p.right Q)
    (hPsat : ((P + S).card : ℝ) = a + b) (hQsat : ((R + Q).card : ℝ) = a + b) :
    label = .both P Q := by
  cases label with
  | left P' =>
      have heq := indicator_masks_eq p.left P' P hlabel.1 hP
      subst P'
      exact False.elim (not_lt_of_ge hPsat.ge hlabel.2)
  | right Q' =>
      have heq := indicator_masks_eq p.right Q' Q hlabel.1 hQ
      subst Q'
      exact False.elim (not_lt_of_ge hQsat.ge hlabel.2)
  | both P' Q' =>
      have heqP := indicator_masks_eq p.left P' P hlabel.1 hP
      have heqQ := indicator_masks_eq p.right Q' Q hlabel.2.1 hQ
      subst P'
      subst Q'
      rfl

end Erdos335.PeriodicRefinementLabelClosure

end
