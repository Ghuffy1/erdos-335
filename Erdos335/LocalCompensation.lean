import Erdos335.FiniteProfiles

/-!
# Compensation by a literal extra residue

A full finite sumset core and one fixed literal translate force saturation
of the window-side input profile. This is the exact finite limiting form of
the local deficit compensation argument.
-/

set_option autoImplicit false

open scoped BigOperators Pointwise

namespace Erdos335.FiniteProfiles

theorem coordinate_ge_sum_sub_card {G : Type*} [DecidableEq G]
    (T : Finset G) (b : G → ℝ) (hb : ∀ t ∈ T, b t ≤ 1) {t : G} (ht : t ∈ T) :
    (∑ x ∈ T, b x) - ((T.card : ℝ) - 1) ≤ b t := by
  have hbErase : (∑ x ∈ T.erase t, b x) ≤ ((T.erase t).card : ℝ) := by
    calc
      (∑ x ∈ T.erase t, b x) ≤ ∑ x ∈ T.erase t, (1 : ℝ) :=
        Finset.sum_le_sum fun x hx => hb x (Finset.mem_of_mem_erase hx)
      _ = _ := by simp
  have hbSum : (∑ x ∈ T.erase t, b x) + b t = ∑ x ∈ T, b x := Finset.sum_erase_add T b ht
  have hEraseCard : ((T.erase t).card : ℝ) + 1 = T.card := by
    exact_mod_cast Finset.card_erase_add_one ht
  linarith

theorem extra_residue_forces_full_profile {G : Type*} [AddCommGroup G] [DecidableEq G]
    (R S T : Finset G) (a b c : G → ℝ) (hSR : S ⊆ R)
    (hcard : (S + T).card + 1 = S.card + T.card)
    (hextra : ¬R + T ⊆ S + T)
    (ha : ∀ s ∈ S, a s ≤ 1) (hb : ∀ t ∈ T, b t ≤ 1)
    (hc : ∀ u ∈ R + T, 0 ≤ c u)
    (hfull : ∀ u ∈ S + T, c u = 1)
    (htranslate : ∀ r ∈ R, ∀ t ∈ T, b t ≤ c (r + t))
    (hmass : (∑ u ∈ R + T, c u) = (∑ s ∈ S, a s) + ∑ t ∈ T, b t) :
    (∑ s ∈ S, a s) = (S.card : ℝ) ∧ ∀ s ∈ S, a s = 1 := by
  classical
  obtain ⟨u, hu, huout⟩ := Finset.not_subset.mp hextra
  obtain ⟨r, hr, t, ht, rfl⟩ := Finset.mem_add.mp hu
  have hcore : S + T ⊆ R + T := Finset.add_subset_add hSR (Finset.Subset.refl _)
  have hcoreSum : (∑ u ∈ S + T, c u) = ((S + T).card : ℝ) := by
    calc
      (∑ u ∈ S + T, c u) = ∑ u ∈ S + T, (1 : ℝ) := Finset.sum_congr rfl hfull
      _ = _ := by simp
  have hsubset : insert (r + t) (S + T) ⊆ R + T := by
    intro u hu
    rcases Finset.mem_insert.mp hu with rfl | hu
    · exact Finset.add_mem_add hr ht
    · exact hcore hu
  have hsum : (∑ u ∈ insert (r + t) (S + T), c u) ≤ ∑ u ∈ R + T, c u :=
    Finset.sum_le_sum_of_subset_of_nonneg hsubset (fun u hu _ => hc u hu)
  rw [Finset.sum_insert huout, hcoreSum, hmass] at hsum
  have htranslated := htranslate r hr t ht
  have hbLower := coordinate_ge_sum_sub_card T b hb ht
  have hcardR : ((S + T).card : ℝ) + 1 = (S.card : ℝ) + T.card := by exact_mod_cast hcard
  have haUpper : (∑ s ∈ S, a s) ≤ (S.card : ℝ) := by simpa using Finset.sum_le_sum ha
  have haExact : (∑ s ∈ S, a s) = (S.card : ℝ) := by linarith
  refine ⟨haExact, ?_⟩
  apply (Finset.sum_eq_sum_iff_of_le ha).mp
  simpa using haExact

theorem extra_output_is_singleton {G : Type*} [AddCommGroup G] [DecidableEq G]
    (R S T : Finset G) (a b c : G → ℝ) (hSR : S ⊆ R)
    (hcard : (S + T).card + 1 = S.card + T.card)
    (hextra : ¬R + T ⊆ S + T)
    (ha : ∀ s ∈ S, a s ≤ 1) (hb : ∀ t ∈ T, b t ≤ 1)
    (hc : ∀ u ∈ R + T, 0 ≤ c u)
    (hfull : ∀ u ∈ S + T, c u = 1)
    (htranslate : ∀ r ∈ R, ∀ t ∈ T, b t ≤ c (r + t))
    (hmass : (∑ u ∈ R + T, c u) = (∑ s ∈ S, a s) + ∑ t ∈ T, b t)
    (he : 0 < (∑ t ∈ T, b t) - ((T.card : ℝ) - 1)) :
    ∃ u : G, (R + T) \ (S + T) = {u} ∧
      c u = (∑ t ∈ T, b t) - ((T.card : ℝ) - 1) := by
  classical
  let D := (R + T) \ (S + T)
  let e := (∑ t ∈ T, b t) - ((T.card : ℝ) - 1)
  have haExact := (extra_residue_forces_full_profile R S T a b c hSR hcard hextra
    ha hb hc hfull htranslate hmass).1
  have hcore : S + T ⊆ R + T := Finset.add_subset_add hSR (Finset.Subset.refl _)
  have hcoreSum : (∑ u ∈ S + T, c u) = ((S + T).card : ℝ) := by
    calc
      (∑ u ∈ S + T, c u) = ∑ u ∈ S + T, (1 : ℝ) := Finset.sum_congr rfl hfull
      _ = _ := by simp
  have hcardR : ((S + T).card : ℝ) + 1 = (S.card : ℝ) + T.card := by exact_mod_cast hcard
  have hDsum : (∑ u ∈ D, c u) = e := by
    have hpartition : (∑ u ∈ D, c u) + (∑ u ∈ S + T, c u) = ∑ u ∈ R + T, c u :=
      Finset.sum_sdiff hcore
    rw [hmass, haExact, hcoreSum] at hpartition
    dsimp only [e]
    linarith
  have hEach : ∀ u ∈ D, e ≤ c u := by
    intro u hu
    obtain ⟨r, hr, t, ht, rfl⟩ := Finset.mem_add.mp (Finset.mem_sdiff.mp hu).1
    exact (coordinate_ge_sum_sub_card T b hb ht).trans (htranslate r hr t ht)
  have hbound : (D.card : ℝ) * e ≤ e := by
    calc
      (D.card : ℝ) * e = ∑ u ∈ D, e := by simp
      _ ≤ ∑ u ∈ D, c u := Finset.sum_le_sum hEach
      _ = e := hDsum
  have hDcardR : (D.card : ℝ) ≤ 1 :=
    le_of_mul_le_mul_right (by simpa only [one_mul] using hbound) he
  have hDcard : D.card ≤ 1 := by exact_mod_cast hDcardR
  have hDnonempty : D.Nonempty := by
    obtain ⟨u, hu, hout⟩ := Finset.not_subset.mp hextra
    exact ⟨u, Finset.mem_sdiff.mpr ⟨hu, hout⟩⟩
  have hDone : D.card = 1 := by have hpos := Finset.card_pos.mpr hDnonempty; omega
  obtain ⟨u, hu⟩ := Finset.card_eq_one.mp hDone
  refine ⟨u, hu, ?_⟩
  simpa only [hu, Finset.sum_singleton] using hDsum

end Erdos335.FiniteProfiles
