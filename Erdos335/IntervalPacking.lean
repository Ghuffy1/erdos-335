import Mathlib.Data.Int.Interval
import Mathlib.Data.Finset.Max
import Mathlib.Data.Finset.Powerset
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Tactic

/-!
# The finite interval-packing lemma

The proposed Erdős 335 proof converts escaping sumsets into unions of integer
intervals. This module proves the factor-three packing estimate used there.
All intervals are literal finite integer intervals, including empty intervals.
-/

set_option autoImplicit false

namespace Erdos335.IntervalPacking

abbrev Interval := ℤ × ℤ

def points (I : Interval) : Finset ℤ := Finset.Icc I.1 I.2

def covered (F : Finset Interval) : Finset ℤ := F.biUnion points

def weight (F : Finset Interval) : ℕ := ∑ I ∈ F, (points I).card

def DisjointFamily (F : Finset Interval) : Prop :=
  ∀ I ∈ F, ∀ J ∈ F, I ≠ J → Disjoint (points I) (points J)

noncomputable def packingSize (F : Finset Interval) : ℕ := by
  classical
  exact (F.powerset.filter DisjointFamily).sup weight

lemma overlapping_subset_enlargement {I J : Interval}
    (hI : I.1 ≤ I.2) (hcard : (points J).card ≤ (points I).card)
    (hoverlap : ¬Disjoint (points I) (points J)) :
    points J ⊆ Finset.Icc (2 * I.1 - I.2) (2 * I.2 - I.1) := by
  classical
  obtain ⟨z, hzI, hzJ⟩ := Finset.not_disjoint_iff.mp hoverlap
  simp only [points, Finset.mem_Icc] at hzI hzJ
  simp only [points, Int.card_Icc] at hcard
  intro x hx
  simp only [points, Finset.mem_Icc] at hx ⊢
  constructor <;> omega

lemma enlargement_card_le (I : Interval) (hI : I.1 ≤ I.2) :
    (Finset.Icc (2 * I.1 - I.2) (2 * I.2 - I.1)).card ≤
      3 * (points I).card := by
  simp only [points, Int.card_Icc]
  omega

lemma disjoint_weight_eq_card {F : Finset Interval} (hF : DisjointFamily F) :
    weight F = (covered F).card := by
  classical
  symm
  exact Finset.card_biUnion hF

/-- Greedy selection gives disjoint intervals of at least one third of the union size. -/
theorem exists_disjoint_cover_bound (F : Finset Interval) :
    ∃ G ⊆ F, DisjointFamily G ∧ (covered F).card ≤ 3 * weight G := by
  classical
  induction F using Finset.strongInductionOn with
  | _ F ih =>
    by_cases hempty : ∀ I ∈ F, points I = ∅
    · refine ⟨∅, Finset.empty_subset F, ?_, ?_⟩
      · simp [DisjointFamily]
      · have hc : covered F = ∅ := by
          apply Finset.eq_empty_iff_forall_notMem.mpr
          intro x hx
          obtain ⟨I, hIF, hx⟩ := Finset.mem_biUnion.mp hx
          simp [hempty I hIF] at hx
        simp [hc, weight]
    · push Not at hempty
      obtain ⟨K, hKF, hK⟩ := hempty
      obtain ⟨I, hIF, hmax⟩ :=
        Finset.exists_max_image F (fun J => (points J).card) ⟨K, hKF⟩
      have hIne : (points I).Nonempty := by
        have hKpos := Finset.card_pos.mpr hK
        exact Finset.card_pos.mp (lt_of_lt_of_le hKpos (hmax K hKF))
      have hI : I.1 ≤ I.2 := by
        obtain ⟨x, hx⟩ := hIne
        exact (Finset.mem_Icc.mp hx).1.trans (Finset.mem_Icc.mp hx).2
      let R := F.filter (fun J => Disjoint (points I) (points J))
      have hRsub : R ⊆ F := Finset.filter_subset _ _
      have hInR : I ∉ R := by
        simp only [R, Finset.mem_filter, not_and]
        intro _ hself
        obtain ⟨z, hz⟩ := hIne
        exact Finset.disjoint_left.mp hself hz hz
      have hRproper : R ⊂ F := Finset.ssubset_iff_subset_ne.mpr
        ⟨hRsub, fun hEq => hInR (hEq.symm ▸ hIF)⟩
      obtain ⟨G, hGR, hG, hbound⟩ := ih R hRproper
      have hIG : I ∉ G := fun h => hInR (hGR h)
      have hdisjoint : ∀ J ∈ G, Disjoint (points I) (points J) := by
        intro J hJG
        exact (Finset.mem_filter.mp (hGR hJG)).2
      refine ⟨insert I G, ?_, ?_, ?_⟩
      · exact Finset.insert_subset hIF (hGR.trans hRsub)
      · intro J hJ L hL hJL
        rcases Finset.mem_insert.mp hJ with hJI | hJG
        · rcases Finset.mem_insert.mp hL with hLI | hLG
          · exact (hJL (hJI.trans hLI.symm)).elim
          · simpa only [hJI] using hdisjoint L hLG
        · rcases Finset.mem_insert.mp hL with hLI | hLG
          · simpa only [hLI] using (hdisjoint J hJG).symm
          · exact hG J hJG L hLG hJL
      · have hcover : covered F ⊆
            Finset.Icc (2 * I.1 - I.2) (2 * I.2 - I.1) ∪ covered R := by
          intro x hx
          obtain ⟨J, hJF, hxJ⟩ := Finset.mem_biUnion.mp hx
          by_cases hd : Disjoint (points I) (points J)
          · exact Finset.mem_union_right _
              (Finset.mem_biUnion.mpr ⟨J, Finset.mem_filter.mpr ⟨hJF, hd⟩, hxJ⟩)
          · exact Finset.mem_union_left _
              (overlapping_subset_enlargement hI (hmax J hJF) hd hxJ)
        have hcount := (Finset.card_le_card hcover).trans (Finset.card_union_le _ _)
        have henlarge := enlargement_card_le I hI
        have hweight : weight (insert I G) = (points I).card + weight G := by
          simp only [weight, Finset.sum_insert hIG]
        rw [hweight]
        omega

theorem packingSize_le_card (F : Finset Interval) : packingSize F ≤ (covered F).card := by
  classical
  apply Finset.sup_le
  intro G hG
  obtain ⟨hGF, hd⟩ := Finset.mem_filter.mp hG
  rw [disjoint_weight_eq_card hd]
  apply Finset.card_le_card
  exact Finset.biUnion_subset_biUnion_of_subset_left points (Finset.mem_powerset.mp hGF)

/-- The exact bound used to replace an interval union by its disjoint packing test. -/
theorem card_le_three_mul_packingSize (F : Finset Interval) :
    (covered F).card ≤ 3 * packingSize F := by
  classical
  obtain ⟨G, hGF, hG, hbound⟩ := exists_disjoint_cover_bound F
  have hweight : weight G ≤ packingSize F :=
    Finset.le_sup (Finset.mem_filter.mpr ⟨Finset.mem_powerset.mpr hGF, hG⟩)
  exact hbound.trans (Nat.mul_le_mul_left 3 hweight)

/-- Exact endpoints for the sum of two nonempty integer intervals. -/
theorem mem_sum_interval_iff (a b c d n : ℤ) (hab : a ≤ b) (hcd : c ≤ d) :
    (∃ x ∈ Finset.Icc a b, ∃ y ∈ Finset.Icc c d, x + y = n) ↔
      n ∈ Finset.Icc (a + c) (b + d) := by
  constructor
  · rintro ⟨x, hx, y, hy, rfl⟩
    simp only [Finset.mem_Icc] at hx hy ⊢
    omega
  · intro hn
    simp only [Finset.mem_Icc] at hn
    refine ⟨max a (n - d), ?_, n - max a (n - d), ?_, by omega⟩
    · simp only [Finset.mem_Icc]
      omega
    · simp only [Finset.mem_Icc]
      omega

end Erdos335.IntervalPacking
