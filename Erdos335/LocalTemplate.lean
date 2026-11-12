import Erdos335.LocalCompensation
import Erdos335.RepresentationBound

/-!
# The finite template forced by a positive local deficit

The extra output has one expression. All other input classes are full, and
the literal support on the window side has exactly one additional class.
-/

set_option autoImplicit false

open scoped BigOperators Pointwise

namespace Erdos335.FiniteProfiles

theorem local_deficit_template {G : Type*} [AddCommGroup G] [DecidableEq G]
    (R S T : Finset G) (a b c : G → ℝ) (hSR : S ⊆ R)
    (hcard : (S + T).card + 1 = S.card + T.card)
    (hextra : ¬R + T ⊆ S + T)
    (ha : ∀ s ∈ S, a s ≤ 1) (hb : ∀ t ∈ T, b t ≤ 1)
    (hc : ∀ u ∈ R + T, 0 ≤ c u)
    (hfull : ∀ u ∈ S + T, c u = 1)
    (htranslate : ∀ r ∈ R, ∀ t ∈ T, b t ≤ c (r + t))
    (hmass : (∑ u ∈ R + T, c u) = (∑ s ∈ S, a s) + ∑ t ∈ T, b t)
    (he : 0 < (∑ t ∈ T, b t) - ((T.card : ℝ) - 1))
    (hgap : (∑ u ∈ R + T, c u) < ((R + T).card : ℝ)) :
    ∃ r t : G, r ∈ R ∧ t ∈ T ∧ r ∉ S ∧ R = insert r S ∧
      (R + T) \ (S + T) = {r + t} ∧
      (∀ s ∈ S, a s = 1) ∧ (∀ y ∈ T.erase t, b y = 1) ∧
      b t = (∑ y ∈ T, b y) - ((T.card : ℝ) - 1) ∧
      (∑ y ∈ T, b y) - ((T.card : ℝ) - 1) < 1 ∧
      ∀ x ∈ R, ∀ y ∈ T, x + y = r + t → x = r ∧ y = t := by
  classical
  let e := (∑ t ∈ T, b t) - ((T.card : ℝ) - 1)
  obtain ⟨haSum, haFull⟩ := extra_residue_forces_full_profile R S T a b c hSR hcard
    hextra ha hb hc hfull htranslate hmass
  obtain ⟨u, hD, huMass⟩ := extra_output_is_singleton R S T a b c hSR hcard
    hextra ha hb hc hfull htranslate hmass he
  have hu : u ∈ (R + T) \ (S + T) := by rw [hD]; simp
  obtain ⟨r, hr, t, ht, hrt⟩ := Finset.mem_add.mp (Finset.mem_sdiff.mp hu).1
  subst u
  have hrnot : r ∉ S := by
    intro hrs
    exact (Finset.mem_sdiff.mp hu).2 (Finset.add_mem_add hrs ht)
  have hcore : S + T ⊆ R + T := Finset.add_subset_add hSR (Finset.Subset.refl _)
  have hdiffCard := Finset.card_sdiff_of_subset hcore
  rw [hD, Finset.card_singleton] at hdiffCard
  have hcoreCard := Finset.card_le_card hcore
  have hwholeCard : (R + T).card = (S + T).card + 1 := by omega
  have hwholeCard' : (R + T).card = S.card + T.card := by omega
  have hcoreSum : (∑ u ∈ S + T, c u) = ((S + T).card : ℝ) := by
    calc
      (∑ u ∈ S + T, c u) = ∑ u ∈ S + T, (1 : ℝ) := Finset.sum_congr rfl hfull
      _ = _ := by simp
  have hcardR : ((S + T).card : ℝ) + 1 = (S.card : ℝ) + T.card := by exact_mod_cast hcard
  have hwholeCardR : ((R + T).card : ℝ) = ((S + T).card : ℝ) + 1 := by exact_mod_cast hwholeCard
  have he1 : e < 1 := by
    dsimp only [e]
    rw [hmass, haSum] at hgap
    linarith
  have hbt : b t = e := by
    have hlo := coordinate_ge_sum_sub_card T b hb ht
    have hhi := htranslate r hr t ht
    change c (r + t) = e at huMass
    linarith
  have hbErase : (∑ y ∈ T.erase t, b y) = ((T.erase t).card : ℝ) := by
    have hsum := Finset.sum_erase_add T b ht
    have hcardErase : ((T.erase t).card : ℝ) + 1 = T.card := by
      exact_mod_cast Finset.card_erase_add_one ht
    dsimp only [e] at hbt
    linarith
  have hbFull : ∀ y ∈ T.erase t, b y = 1 := by
    apply (Finset.sum_eq_sum_iff_of_le (fun y hy => hb y (Finset.mem_of_mem_erase hy))).mp
    simpa using hbErase
  have hunique : ∀ x ∈ R, ∀ y ∈ T, x + y = r + t → x = r ∧ y = t := by
    intro x hx y hy hxy
    have hylo := coordinate_ge_sum_sub_card T b hb hy
    have hyhi := htranslate x hx y hy
    rw [hxy, huMass] at hyhi
    have hye : b y = e := by linarith
    have hyt : y = t := by
      by_contra hne
      have hyy := hbFull y (Finset.mem_erase.mpr ⟨hne, hy⟩)
      linarith
    refine ⟨?_, hyt⟩
    subst y
    exact add_right_cancel hxy
  have hproper : S ⊂ R := Finset.ssubset_iff_subset_ne.mpr
    ⟨hSR, fun hEq => hrnot (hEq.symm ▸ hr)⟩
  have hRcard : R.card = S.card + 1 :=
    FiniteKneser.card_of_unique_extra_sum R S T hproper hr ht hunique hwholeCard'
  have hsub : insert r S ⊆ R := Finset.insert_subset hr hSR
  have hinsert : (insert r S).card = R.card := by
    rw [Finset.card_insert_of_notMem hrnot, hRcard]
  have hR : R = insert r S := (Finset.eq_of_subset_of_card_le hsub hinsert.ge).symm
  exact ⟨r, t, hr, ht, hrnot, hR, hD, haFull, hbFull, hbt, he1, hunique⟩

end Erdos335.FiniteProfiles
