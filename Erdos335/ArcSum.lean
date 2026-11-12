import Erdos335.ArcDensity

/-!
# Interior overlap for the filled-arc sum argument
-/

set_option autoImplicit false

open Set Filter Topology
open scoped Pointwise

namespace Erdos335.Proposed

theorem exists_good_complement (A B S T : Set ℕ) (candidates : Finset ℕ) (n : ℕ)
    (hbounds : ∀ a ∈ candidates, 0 < a ∧ a ≤ n)
    (hleft : ∀ a ∈ candidates, a ∈ S)
    (hright : ∀ a ∈ candidates, a < n → n - a ∈ T)
    (hcount : count (S \ A) n + count (T \ B) n + 1 < candidates.card) :
    ∃ a ∈ candidates, a < n ∧ a ∈ A ∧ n - a ∈ B := by
  classical
  by_contra hnone
  push Not at hnone
  let badA := (Finset.Icc 1 n).filter (fun a => a ∈ S \ A)
  let badB := (Finset.Icc 1 n).filter (fun b => b ∈ T \ B)
  let reflected := badB.image (fun b => n - b)
  have hcover : candidates ⊆ ({n} ∪ badA) ∪ reflected := by
    intro a ha
    have hb := hbounds a ha
    by_cases han : a = n
    · exact Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_singleton.mpr han))
    · have haltn : a < n := by omega
      by_cases haA : a ∈ A
      · have hnB : n - a ∉ B := hnone a ha haltn haA
        apply Finset.mem_union_right
        apply Finset.mem_image.mpr
        refine ⟨n - a, Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr ⟨by omega, Nat.sub_le _ _⟩,
          hright a ha haltn, hnB⟩, Nat.sub_sub_self hb.2⟩
      · apply Finset.mem_union_left
        apply Finset.mem_union_right
        exact Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr ⟨hb.1, hb.2⟩, hleft a ha, haA⟩
  have hc : candidates.card ≤ ({n} : Finset ℕ).card + badA.card + badB.card := by
    calc
      candidates.card ≤ (({n} ∪ badA) ∪ reflected).card := Finset.card_le_card hcover
      _ ≤ ({n} ∪ badA).card + reflected.card := Finset.card_union_le _ _
      _ ≤ (({n} : Finset ℕ).card + badA.card) + badB.card :=
        Nat.add_le_add (Finset.card_union_le _ _) (Finset.card_image_le)
  have hca : badA.card = count (S \ A) n := by
    dsimp only [badA]
    unfold count
    congr 1
    ext a
    simp only [Finset.mem_filter]
  have hcb : badB.card = count (T \ B) n := by
    dsimp only [badB]
    unfold count
    congr 1
    ext b
    simp only [Finset.mem_filter]
  simp only [Finset.card_singleton, hca, hcb] at hc
  omega

theorem exists_stable_overlap_interval (a b c d x : ℝ)
    (hab : a < b) (hcd : c < d) (hx0 : a + c < x) (hx1 : x < b + d) :
    ∃ lo hi radius : ℝ, lo < hi ∧ 0 < radius ∧ a < lo ∧ hi < b ∧
      ∀ y ∈ Ioo (x - radius) (x + radius), ∀ t ∈ Icc lo hi,
        c < y - t ∧ y - t < d := by
  let left := max a (x - d)
  let right := min b (x - c)
  have hgap : left < right := by
    dsimp [left, right]
    rw [max_lt_iff]
    constructor <;> rw [lt_min_iff] <;> constructor <;> linarith
  have hal : a ≤ left := le_max_left _ _
  have hxl : x - d ≤ left := le_max_right _ _
  have hrb : right ≤ b := min_le_left _ _
  have hrx : right ≤ x - c := min_le_right _ _
  refine ⟨left + (right - left) / 3, left + 2 * (right - left) / 3,
    (right - left) / 6, ?_, ?_, ?_, ?_, ?_⟩
  · linarith
  · linarith
  · linarith
  · linarith
  · intro y hy t ht
    obtain ⟨hyl, hyr⟩ := hy
    obtain ⟨htl, htr⟩ := ht
    constructor <;> linarith

theorem finite_overlap_cover (a b c d lower upper : ℝ)
    (hab : a < b) (hcd : c < d) (hlower : a + c < lower) (hupper : upper < b + d) :
    ∃ (F : Finset (Icc lower upper)) (lo hi radius : Icc lower upper → ℝ),
      (∀ x ∈ F, lo x < hi x ∧ 0 < radius x ∧ a < lo x ∧ hi x < b ∧
        ∀ y ∈ Ioo ((x : ℝ) - radius x) ((x : ℝ) + radius x),
          ∀ t ∈ Icc (lo x) (hi x), c < y - t ∧ y - t < d) ∧
      Icc lower upper ⊆ ⋃ x ∈ F, Ioo ((x : ℝ) - radius x) ((x : ℝ) + radius x) := by
  classical
  have hpoint : ∀ x : Icc lower upper, ∃ lo hi radius : ℝ,
      lo < hi ∧ 0 < radius ∧ a < lo ∧ hi < b ∧
        ∀ y ∈ Ioo ((x : ℝ) - radius) ((x : ℝ) + radius),
          ∀ t ∈ Icc lo hi, c < y - t ∧ y - t < d := by
    intro x
    exact exists_stable_overlap_interval a b c d x hab hcd
      (hlower.trans_le x.property.1) (x.property.2.trans_lt hupper)
  choose lo hi radius hgood using hpoint
  let U := fun x : Icc lower upper => Ioo ((x : ℝ) - radius x) ((x : ℝ) + radius x)
  have hopen : ∀ x, IsOpen (U x) := fun _ => isOpen_Ioo
  have hcover : Icc lower upper ⊆ ⋃ x, U x := by
    intro x hx
    apply mem_iUnion.mpr
    refine ⟨⟨x, hx⟩, ?_⟩
    have hrad := (hgood ⟨x, hx⟩).2.1
    change x - radius ⟨x, hx⟩ < x ∧ x < x + radius ⟨x, hx⟩
    constructor <;> linarith
  obtain ⟨F, hF⟩ := isCompact_Icc.elim_finite_subcover U hopen hcover
  exact ⟨F, lo, hi, radius, fun x _ => hgood x, hF⟩

theorem eventual_inner_arc_subset_sum {A B : Set ℕ} {θ startA startB lenA lenB δ : ℝ}
    (hθ : Irrational θ) (hA0 : 0 < lenA) (hB0 : 0 < lenB)
    (hlen : lenA + lenB ≤ 1) (hδ : 0 < δ)
    (hholesA : Negligible (closedArcPullback θ startA lenA \ A))
    (hholesB : Negligible (closedArcPullback θ startB lenB \ B)) :
    ∀ᶠ n : ℕ in atTop, n ∈ closedArcPullback θ (startA + startB + δ) (lenA + lenB - 2 * δ) →
      n ∈ A + B := by
  classical
  let lower := startA + startB + δ
  let upper := startA + lenA + startB + lenB - δ
  obtain ⟨F, lo, hi, radius, hinterval, hcover⟩ := finite_overlap_cover
    startA (startA + lenA) startB (startB + lenB) lower upper
    (by linarith) (by linarith) (by dsimp [lower]; linarith) (by dsimp [upper]; linarith)
  let P := fun i : Icc lower upper => closedArcPullback θ (lo i) (hi i - lo i)
  have hcounts : ∀ i ∈ F, ∀ᶠ n : ℕ in atTop,
      count (closedArcPullback θ startA lenA \ A) n +
        count (closedArcPullback θ startB lenB \ B) n + 1 < count (P i) n := by
    intro i hiF
    have hp := hinterval i hiF
    have hP : HasDensity (P i) (hi i - lo i) :=
      closedArcPullback_hasDensity hθ _ _ (by linarith [hp.1])
        (by linarith [hp.2.2.1, hp.2.2.2.1])
    have hlim : Tendsto (fun n =>
        ((count (P i) n : ℝ) - count (closedArcPullback θ startA lenA \ A) n -
          count (closedArcPullback θ startB lenB \ B) n - 1) / n)
        atTop (𝓝 (hi i - lo i)) := by
      simpa only [← sub_div, sub_zero] using
        (((hP.sub hholesA).sub hholesB).sub (tendsto_const_div_atTop_nhds_zero_nat (1 : ℝ)))
    have hpos : ∀ᶠ n : ℕ in atTop, 0 <
        ((count (P i) n : ℝ) - count (closedArcPullback θ startA lenA \ A) n -
          count (closedArcPullback θ startB lenB \ B) n - 1) / n :=
      hlim (lt_mem_nhds (by linarith [hp.1]))
    filter_upwards [hpos, eventually_ge_atTop 1] with n hn hn1
    have hn0 : (0 : ℝ) < n := by exact_mod_cast hn1
    have hnum := (div_pos_iff_of_pos_right hn0).mp hn
    exact_mod_cast (show (count (closedArcPullback θ startA lenA \ A) n : ℝ) +
      count (closedArcPullback θ startB lenB \ B) n + 1 < count (P i) n by linarith)
  have hall := (F.eventually_all).mpr hcounts
  filter_upwards [hall] with n hn
  rintro ⟨hn0, k, hnlo, hnhi⟩
  let x : ℝ := (n : ℝ) * θ - k
  have hx : x ∈ Icc lower upper := by
    dsimp [x, lower, upper]
    constructor <;> linarith
  obtain ⟨i, hiF, hxi⟩ := mem_iUnion₂.mp (hcover hx)
  let candidates := (Finset.Icc 1 n).filter (fun a => a ∈ P i)
  have hcand : candidates.card = count (P i) n := by
    dsimp [candidates]
    unfold count
    congr 1
  have hleft : ∀ a ∈ candidates, a ∈ closedArcPullback θ startA lenA := by
    intro a ha
    obtain ⟨haN, haP⟩ := Finset.mem_filter.mp ha
    obtain ⟨ha0, j, haj, haj'⟩ := haP
    have hp := hinterval i hiF
    exact ⟨ha0, j, by linarith [hp.2.2.1], by linarith [hp.2.2.2.1]⟩
  have hright : ∀ a ∈ candidates, a < n → n - a ∈ closedArcPullback θ startB lenB := by
    intro a ha han
    obtain ⟨haN, haP⟩ := Finset.mem_filter.mp ha
    have hale := (Finset.mem_Icc.mp haN).2
    obtain ⟨ha0, j, haj, haj'⟩ := haP
    have hphase := (hinterval i hiF).2.2.2.2 x hxi ((a : ℝ) * θ - j)
      ⟨by linarith, by linarith⟩
    dsimp [x] at hphase
    refine ⟨Nat.sub_pos_of_lt han, k - j, ?_, ?_⟩
    · simp only [Nat.cast_sub hale, Int.cast_sub]
      nlinarith [hphase.1]
    · simp only [Nat.cast_sub hale, Int.cast_sub]
      nlinarith [hphase.2]
  obtain ⟨a, ha, han, haA, hbB⟩ := exists_good_complement A B
    (closedArcPullback θ startA lenA) (closedArcPullback θ startB lenB) candidates n
    (fun a ha => by
      have h := (Finset.mem_filter.mp ha).1
      have h' := Finset.mem_Icc.mp h
      exact ⟨h'.1, h'.2⟩)
    hleft hright (by rw [hcand]; exact hn i hiF)
  refine ⟨a, haA, n - a, hbB, ?_⟩
  change a + (n - a) = n
  exact Nat.add_sub_of_le han.le

theorem filled_closedArcs_sum_hasDensity {A B : Set ℕ} {θ startA startB lenA lenB : ℝ}
    (hθ : Irrational θ) (hA0 : 0 < lenA) (hB0 : 0 < lenB) (hlen : lenA + lenB ≤ 1)
    (hA : A ⊆ closedArcPullback θ startA lenA)
    (hB : B ⊆ closedArcPullback θ startB lenB)
    (hholesA : Negligible (closedArcPullback θ startA lenA \ A))
    (hholesB : Negligible (closedArcPullback θ startB lenB \ B)) :
    HasDensity (A + B) (lenA + lenB) := by
  let s := lenA + lenB
  have hs : 0 < s := by dsimp [s]; linarith
  change Tendsto (fun n => (count (A + B) n : ℝ) / n) atTop (𝓝 s)
  apply Metric.tendsto_atTop.mpr
  intro ε hε
  let δ := min (ε / 8) (s / 8)
  have hδ : 0 < δ := lt_min (by positivity) (by positivity)
  have hδε : δ ≤ ε / 8 := min_le_left _ _
  have hδs : δ ≤ s / 8 := min_le_right _ _
  let inner := closedArcPullback θ (startA + startB + δ) (s - 2 * δ)
  have hInner : HasDensity inner (s - 2 * δ) :=
    closedArcPullback_hasDensity hθ _ _ (by linarith) (by dsimp [s] at *; linarith)
  have hrep : ∀ᶠ n : ℕ in atTop, n ∈ inner → n ∈ A + B :=
    eventual_inner_arc_subset_sum hθ hA0 hB0 hlen hδ hholesA hholesB
  obtain ⟨K, hK⟩ := eventually_atTop.mp hrep
  have hcount : ∀ N, count inner N ≤ count (A + B) N + K :=
    fun N => count_le_count_add inner (A + B) K (fun n hn => hK n hn.le) N
  have hlow : Tendsto (fun N => (count inner N : ℝ) / N - (K : ℝ) / N)
      atTop (𝓝 (s - 2 * δ)) := by
    simpa only [sub_zero] using hInner.sub (tendsto_const_div_atTop_nhds_zero_nat (K : ℝ))
  have hlowEv : ∀ᶠ N : ℕ in atTop,
      s - ε < (count inner N : ℝ) / N - (K : ℝ) / N :=
    hlow (lt_mem_nhds (by linarith))
  have huppEv := closedArc_sum_upper_bound hθ (by linarith) hlen hA hB
    (ε := ε / 2) (by positivity)
  apply eventually_atTop.mp
  filter_upwards [hlowEv, huppEv] with N hlowN huppN
  have hc : (count inner N : ℝ) ≤ (count (A + B) N : ℝ) + K := by exact_mod_cast hcount N
  have hcdiv := div_le_div_of_nonneg_right hc (Nat.cast_nonneg N)
  rw [add_div] at hcdiv
  change |(count (A + B) N : ℝ) / N - s| < ε
  rw [abs_lt]
  constructor <;> dsimp only [s] at * <;> linarith

end Erdos335.Proposed
