import Erdos335.FiniteExceptionalCapacity

/-!
# A positive capacity gap supplies two literal points in a null class
-/

set_option autoImplicit false

open Set
open scoped Classical

namespace Erdos335

theorem capacity_bound_of_singleton_residue
    (A : Set ℕ) (h L : ℕ+) (hL : (h : ℕ) ∣ (L : ℕ))
    (i : ZMod (h : ℕ)) (hi : i ∈ residues (h : ℕ) A)
    (u : ℕ) (hunique : ∀ v ∈ A, (v : ZMod (h : ℕ)) = i → v = u) :
    ((residues (L : ℕ) A).card : ℝ) / (L : ℕ) ≤
      (((residues (h : ℕ) A).card : ℝ) - 1) / (h : ℕ) + 1 / (L : ℕ) := by
  let S := Finset.univ.filter (fun r : ZMod (L : ℕ) =>
    Loeb.naturalCyclicProjection L h r ∈ (residues (h : ℕ) A).erase i)
  have hsub : residues (L : ℕ) A ⊆ insert (u : ZMod (L : ℕ)) S := by
    intro r hr
    obtain ⟨v, hv, rfl⟩ := mem_residues.mp hr
    by_cases hvi : (v : ZMod (h : ℕ)) = i
    · exact Finset.mem_insert.mpr (Or.inl (congrArg (fun n : ℕ => (n : ZMod (L : ℕ)))
        (hunique v hv hvi)))
    · apply Finset.mem_insert.mpr
      right
      apply Finset.mem_filter.mpr
      refine ⟨Finset.mem_univ _, ?_⟩
      rw [Loeb.naturalCyclicProjection_natCast L h hL]
      exact Finset.mem_erase.mpr ⟨hvi, mem_residues.mpr ⟨v, hv, rfl⟩⟩
  have hcard : (residues (L : ℕ) A).card ≤ S.card + 1 :=
    (Finset.card_le_card hsub).trans (Finset.card_insert_le _ _)
  have hbase := natural_preimage_capacity L h hL ((residues (h : ℕ) A).erase i)
  have herase : (((residues (h : ℕ) A).erase i).card : ℝ) =
      ((residues (h : ℕ) A).card : ℝ) - 1 := by
    have hc : (((residues (h : ℕ) A).erase i).card : ℝ) + 1 = (residues (h : ℕ) A).card := by
      exact_mod_cast Finset.card_erase_add_one hi
    linarith
  have hLpos : (0 : ℝ) < (L : ℕ) := by exact_mod_cast L.pos
  calc
    ((residues (L : ℕ) A).card : ℝ) / (L : ℕ) ≤ ((S.card : ℝ) + 1) / (L : ℕ) :=
      div_le_div_of_nonneg_right (by exact_mod_cast hcard) hLpos.le
    _ = (S.card : ℝ) / (L : ℕ) + 1 / (L : ℕ) := add_div _ _ _
    _ = _ := by rw [show (S.card : ℝ) / (L : ℕ) = _ from hbase, herase]

theorem positive_gap_null_class_has_two_points
    (A : Set ℕ) (a δ : ℝ) (hδ : 0 < δ)
    (hcapacity : ∀ k : ℕ+, a + δ ≤ ((residues (k : ℕ) A).card : ℝ) / (k : ℕ))
    (h : ℕ+) (i : ZMod (h : ℕ)) (hi : i ∈ residues (h : ℕ) A)
    (ha : a = (((residues (h : ℕ) A).card : ℝ) - 1) / (h : ℕ)) :
    ∃ u ∈ A, ∃ v ∈ A, u < v ∧ (u : ZMod (h : ℕ)) = i ∧ (v : ZMod (h : ℕ)) = i := by
  by_contra hnone
  obtain ⟨u, hu, hui⟩ := mem_residues.mp hi
  have hunique : ∀ v ∈ A, (v : ZMod (h : ℕ)) = i → v = u := by
    intro v hv hvi
    by_contra hne
    rcases lt_or_gt_of_ne hne with hlt | hgt
    · exact hnone ⟨v, hv, u, hu, hlt, hvi, hui⟩
    · exact hnone ⟨u, hu, v, hv, hgt, hui, hvi⟩
  obtain ⟨n, hn⟩ := exists_nat_gt (1 / δ)
  have hn0 : 0 < n := by
    have hnpos : (0 : ℝ) < n := (one_div_pos.mpr hδ).trans hn
    exact_mod_cast hnpos
  let k : ℕ+ := ⟨n, hn0⟩
  let L := h * k
  have hbound := capacity_bound_of_singleton_residue A h L ⟨k, rfl⟩ i hi u hunique
  rw [← ha] at hbound
  have hle : δ ≤ 1 / (L : ℕ) := by linarith [hcapacity L]
  have hLge : (n : ℝ) ≤ (L : ℕ) := by
    have hh : (1 : ℝ) ≤ (h : ℕ) := by exact_mod_cast h.pos
    change (n : ℝ) ≤ (((h : ℕ) * n : ℕ) : ℝ)
    push_cast
    nlinarith
  have hLpos : (0 : ℝ) < (L : ℕ) := by exact_mod_cast L.pos
  have hsmall : 1 / (L : ℕ) < δ := by
    apply (div_lt_iff₀ hLpos).mpr
    have hproduct : (1 : ℝ) < δ * n := by
      have hp := (div_lt_iff₀ hδ).mp hn
      nlinarith
    nlinarith
  exact not_le_of_gt hsmall hle

end Erdos335
