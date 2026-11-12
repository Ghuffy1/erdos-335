/-
Lean formalization credited to Steve Hubbard and the goldbach-lean project.
Released under Apache 2.0, as specified by the upstream repository LICENSE.

Adapted from sthubbar/goldbach-lean at
559706d617bc554787e10dba07066dc63ab69cb5, entries/mann1942.
The upstream source credits Claude for the Lean implementation and
Mann (1942), Dyson (1945), and Nathanson (arXiv:2407.12253v4) for the mathematics.
The original source and license are retained in public_sources/mann1942.
-/

import Erdos335.Density

set_option autoImplicit false

open Finset
open scoped Classical

namespace LeanLab.Ramare1995.Section9

noncomputable def cnt (A : Set ℕ) (n : ℕ) : ℕ := #{a ∈ Icc 1 n | a ∈ A}

end LeanLab.Ramare1995.Section9

namespace LeanLab.Ramare1995.Theorem91
open LeanLab.Ramare1995.Section9

lemma cnt_zero (A : Set ℕ) : cnt A 0 = 0 := by simp [cnt]

lemma cnt_split (A : Set ℕ) {k m : ℕ} (h : k ≤ m) :
    cnt A m = cnt A k + #{x ∈ Ioc k m | x ∈ A} := by
  unfold cnt
  rw [← card_union_of_disjoint]
  · congr 1; ext a; simp only [mem_filter, mem_union, mem_Icc, mem_Ioc]
    constructor
    · rintro ⟨⟨h1, h2⟩, h3⟩
      by_cases hk : a ≤ k
      · exact Or.inl ⟨⟨h1, hk⟩, h3⟩
      · exact Or.inr ⟨⟨by omega, h2⟩, h3⟩
    · rintro (⟨⟨h1, h2⟩, h3⟩ | ⟨⟨h1, h2⟩, h3⟩)
      · exact ⟨⟨h1, by omega⟩, h3⟩
      · exact ⟨⟨by omega, h2⟩, h3⟩
  · rw [disjoint_left]; intro a h1 h2
    simp only [mem_filter, mem_Icc, mem_Ioc] at h1 h2; omega

lemma cnt_mono_set {A B : Set ℕ} (h : A ⊆ B) (m : ℕ) : cnt A m ≤ cnt B m := by
  unfold cnt
  exact card_le_card (fun x hx => by
    simp only [mem_filter] at hx ⊢; exact ⟨hx.1, h hx.2⟩)

lemma cnt_mono (A : Set ℕ) {k m : ℕ} (h : k ≤ m) : cnt A k ≤ cnt A m := by
  rw [cnt_split A h]; omega

lemma cnt_le (A : Set ℕ) (m : ℕ) : cnt A m ≤ m := by
  unfold cnt
  calc #{a ∈ Icc 1 m | a ∈ A} ≤ #(Icc 1 m) := card_filter_le _ _
    _ = m := by simp

lemma cnt_eq_zero {A : Set ℕ} {m : ℕ} (h : ∀ x, 1 ≤ x → x ≤ m → x ∉ A) : cnt A m = 0 := by
  unfold cnt
  rw [card_eq_zero, filter_eq_empty_iff]
  intro x hx; simp only [mem_Icc] at hx; exact h x hx.1 hx.2

lemma cnt_pos {A : Set ℕ} {m c : ℕ} (hc : c ∈ A) (h1 : 1 ≤ c) (h2 : c ≤ m) : 1 ≤ cnt A m := by
  unfold cnt
  rw [Nat.one_le_iff_ne_zero, Ne, card_eq_zero, ← Ne, ← nonempty_iff_ne_empty]
  exact ⟨c, by simp [hc, h1, h2]⟩

lemma cnt_diff {B T : Set ℕ} (hT : T ⊆ B) (m : ℕ) : cnt (B \ T) m + cnt T m = cnt B m := by
  unfold cnt
  rw [← card_union_of_disjoint]
  · congr 1; ext a; simp only [mem_filter, mem_union, Set.mem_sdiff]
    constructor
    · rintro (⟨h1, h2, -⟩ | ⟨h1, h2⟩)
      · exact ⟨h1, h2⟩
      · exact ⟨h1, hT h2⟩
    · rintro ⟨h1, h2⟩
      by_cases h3 : a ∈ T
      · exact Or.inr ⟨h1, h3⟩
      · exact Or.inl ⟨h1, h2, h3⟩
  · rw [disjoint_left]; intro a h1 h2
    simp only [mem_filter, Set.mem_sdiff] at h1 h2; exact h1.2.2 h2.2

lemma cnt_sub_le (S : Set ℕ) (m k : ℕ) : cnt S m ≤ cnt S (m - k) + k := by
  rw [cnt_split S (Nat.sub_le m k)]
  have : #{x ∈ Ioc (m - k) m | x ∈ S} ≤ k :=
    (card_filter_le _ _).trans (by simp; omega)
  omega

/-- The last point. -/
lemma cnt_last {A : Set ℕ} {n : ℕ} (hn : 1 ≤ n) (h : n ∉ A) : cnt A n ≤ n - 1 := by
  rw [cnt_split A (Nat.sub_le n 1)]
  have : #{x ∈ Ioc (n - 1) n | x ∈ A} = 0 := by
    rw [card_eq_zero, filter_eq_empty_iff]
    intro x hx; simp only [mem_Ioc] at hx
    have : x = n := by omega
    rwa [this]
  have := cnt_le A (n - 1)
  omega

/-! ### Sums over `range` changed at one or two indices -/

lemma sum_two {s : Finset ℕ} {f g : ℕ → ℕ} {a b : ℕ} (ha : a ∈ s) (hb : b ∈ s) (hab : a ≠ b)
    (h : ∀ i ∈ s, i ≠ a → i ≠ b → f i = g i) :
    ∑ i ∈ s, f i + (g a + g b) = ∑ i ∈ s, g i + (f a + f b) := by
  have hb' : b ∈ s.erase a := mem_erase.2 ⟨hab.symm, hb⟩
  rw [← add_sum_erase s f ha, ← add_sum_erase s g ha, ← add_sum_erase _ f hb',
    ← add_sum_erase _ g hb']
  have : ∑ i ∈ (s.erase a).erase b, f i = ∑ i ∈ (s.erase a).erase b, g i := by
    apply sum_congr rfl
    intro i hi
    simp only [mem_erase] at hi
    exact h i hi.2.2 hi.2.1 hi.1
  rw [this]; ring

lemma sum_one {s : Finset ℕ} {f g : ℕ → ℕ} {a : ℕ} (ha : a ∈ s)
    (h : ∀ i ∈ s, i ≠ a → f i = g i) :
    ∑ i ∈ s, f i + g a = ∑ i ∈ s, g i + f a := by
  rw [← add_sum_erase s f ha, ← add_sum_erase s g ha]
  have : ∑ i ∈ s.erase a, f i = ∑ i ∈ s.erase a, g i := by
    apply sum_congr rfl
    intro i hi
    simp only [mem_erase] at hi
    exact h i hi.2 hi.1
  rw [this]; ring

/-! ### Dyson's theorem, covering case

Families are `A : ℕ → Set ℕ`, of which the first `k` sets are used. `Rep A k p`: `p` is a sum
`f 0 + ⋯ + f (k-1)` with `f i ∈ A i ∪ {0}`. -/

def Rep (A : ℕ → Set ℕ) (k p : ℕ) : Prop :=
  ∃ f : ℕ → ℕ, (∀ i < k, f i = 0 ∨ f i ∈ A i) ∧ ∑ i ∈ range k, f i = p

/-- The rank one counting function `A_0(m) + ⋯ + A_{k-1}(m)`. -/
noncomputable def phi (A : ℕ → Set ℕ) (k m : ℕ) : ℕ := ∑ i ∈ range k, cnt (A i) m

/-- Dyson's hypothesis with `γ = 1` on `[1, n]`. -/
def DysonHyp (A : ℕ → Set ℕ) (k n : ℕ) : Prop := ∀ m, 1 ≤ m → m ≤ n → m ≤ phi A k m

section transform
variable (A : ℕ → Set ℕ) (h n : ℕ)

/-- Dyson triple for the family `A 0, …, A (h+1)`, the last set being `A (h+1)`. -/
def Trip (a ℓ c : ℕ) : Prop :=
  ℓ ≤ h ∧ (a = 0 ∨ a ∈ A ℓ) ∧ a ≤ n ∧ c ∈ A (h + 1) ∧ 1 ≤ c ∧ c ≤ n ∧
    (c + a ≤ n → c + a ∉ A ℓ)

/-- The set `T(a, ℓ)`. -/
def Tset (a ℓ : ℕ) : Set ℕ :=
  {c | c ∈ A (h + 1) ∧ 1 ≤ c ∧ c ≤ n ∧ (c + a ≤ n → c + a ∉ A ℓ)}

/-- `T + a`. -/
def Tsh (a ℓ : ℕ) : Set ℕ := {x | a ≤ x ∧ x - a ∈ Tset A h n a ℓ}

/-- The Dyson transform. -/
def tr (a ℓ : ℕ) : ℕ → Set ℕ := fun i =>
  if i = h + 1 then A (h + 1) \ Tset A h n a ℓ
  else if i = ℓ then A ℓ ∪ Tsh A h n a ℓ else A i

end transform

lemma tr_last (A : ℕ → Set ℕ) (h n a ℓ : ℕ) :
    tr A h n a ℓ (h + 1) = A (h + 1) \ Tset A h n a ℓ := by simp [tr]

lemma tr_l (A : ℕ → Set ℕ) {h n a ℓ : ℕ} (hℓ : ℓ ≤ h) :
    tr A h n a ℓ ℓ = A ℓ ∪ Tsh A h n a ℓ := by
  simp [tr, show ℓ ≠ h + 1 by omega]

lemma tr_ne (A : ℕ → Set ℕ) {h n a ℓ i : ℕ} (h1 : i ≠ h + 1) (h2 : i ≠ ℓ) :
    tr A h n a ℓ i = A i := by simp [tr, h1, h2]

/-- Lemma 1 of Nathanson: sums of the transformed family below `n` are sums of the family. -/
lemma rep_back {A : ℕ → Set ℕ} {h n a ℓ p : ℕ} (hℓ : ℓ ≤ h) (ha : a = 0 ∨ a ∈ A ℓ)
    (hp : p ≤ n) (hr : Rep (tr A h n a ℓ) (h + 2) p) : Rep A (h + 2) p := by
  obtain ⟨f, hf, hs⟩ := hr
  have hne : ℓ ≠ h + 1 := by omega
  have hmemL : h + 1 ∈ range (h + 2) := mem_range.2 (by omega)
  have hmeml : ℓ ∈ range (h + 2) := mem_range.2 (by omega)
  have htwo : f ℓ + f (h + 1) ≤ p := by
    rw [← hs, ← add_sum_erase _ f hmeml, ← add_sum_erase _ f (mem_erase.2 ⟨hne.symm, hmemL⟩)]
    omega
  have hL := hf (h + 1) (by omega)
  have hl := hf ℓ (by omega)
  rw [tr_last] at hL
  rw [tr_l A hℓ] at hl
  have hy : f (h + 1) = 0 ∨ f (h + 1) ∈ A (h + 1) := by
    rcases hL with h0 | h0
    · exact Or.inl h0
    · exact Or.inr h0.1
  have hother : ∀ i < h + 2, i ≠ h + 1 → i ≠ ℓ → f i = 0 ∨ f i ∈ A i := by
    intro i hi h1 h2
    have := hf i hi; rwa [tr_ne A h1 h2] at this
  rcases hl with hx | hx | hx
  · refine ⟨f, fun i hi => ?_, hs⟩
    by_cases h1 : i = h + 1
    · subst h1; exact hy
    by_cases h2 : i = ℓ
    · subst h2; exact Or.inl hx
    · exact hother i hi h1 h2
  · refine ⟨f, fun i hi => ?_, hs⟩
    by_cases h1 : i = h + 1
    · subst h1; exact hy
    by_cases h2 : i = ℓ
    · subst h2; exact Or.inr hx
    · exact hother i hi h1 h2
  · obtain ⟨hax, hT⟩ := hx
    have hay : a + f (h + 1) = 0 ∨ a + f (h + 1) ∈ A ℓ := by
      rcases hL with h0 | ⟨h0, h0'⟩
      · rw [h0, add_zero]; exact ha
      · by_cases hy0 : f (h + 1) = 0
        · rw [hy0, add_zero]; exact ha
        · right
          have hnT : ¬ (f (h + 1) + a ≤ n → f (h + 1) + a ∉ A ℓ) := by
            intro hc; exact h0' ⟨h0, by omega, by omega, hc⟩
          push Not at hnT
          rw [add_comm]; exact hnT.2
    set g : ℕ → ℕ := Function.update (Function.update f ℓ (a + f (h + 1))) (h + 1) (f ℓ - a)
      with hg
    have g1 : g (h + 1) = f ℓ - a := by simp [hg]
    have g2 : g ℓ = a + f (h + 1) := by simp [hg, hne]
    have g3 : ∀ i, i ≠ h + 1 → i ≠ ℓ → g i = f i := by
      intro i h1 h2; simp [hg, h1, h2]
    refine ⟨g, fun i hi => ?_, ?_⟩
    · by_cases h1 : i = h + 1
      · subst h1; rw [g1]; exact Or.inr hT.1
      by_cases h2 : i = ℓ
      · subst h2; rw [g2]; exact hay
      · rw [g3 i h1 h2]; exact hother i hi h1 h2
    · have := sum_two (f := f) (g := g) hmeml hmemL hne
        (fun i _ h1 h2 => (g3 i h2 h1).symm)
      rw [g1, g2] at this
      omega

/-- `B(m) + T(m - a) ≤ (B ∪ (T + a))(m)` when `T + a` misses `B` below `n`. -/
lemma cnt_union_shift (B T : Set ℕ) (a m n : ℕ) (hm : m ≤ n)
    (hT : ∀ c ∈ T, c + a ≤ n → c + a ∉ B) :
    cnt B m + cnt T (m - a) ≤ cnt (B ∪ {x | a ≤ x ∧ x - a ∈ T}) m := by
  unfold cnt
  have hinj : #(({c ∈ Icc 1 (m - a) | c ∈ T}).image (· + a)) = #{c ∈ Icc 1 (m - a) | c ∈ T} :=
    card_image_of_injective _ (add_left_injective a)
  rw [← hinj, ← card_union_of_disjoint]
  · apply card_le_card
    intro x hx
    simp only [mem_union, mem_filter, mem_image, mem_Icc] at hx ⊢
    rcases hx with ⟨⟨h1, h2⟩, h3⟩ | ⟨c, ⟨⟨h1, h2⟩, h3⟩, rfl⟩
    · exact ⟨⟨h1, h2⟩, Or.inl h3⟩
    · refine ⟨⟨by omega, by omega⟩, Or.inr ⟨by omega, ?_⟩⟩
      simpa using h3
  · rw [disjoint_left]
    intro x h1 h2
    simp only [mem_filter, mem_image, mem_Icc] at h1 h2
    obtain ⟨c, ⟨⟨c1, c2⟩, c3⟩, rfl⟩ := h2
    exact hT c c3 (by omega) h1.2

/-- Lemma 6 of Nathanson, counting form. -/
lemma cnt_shift_lower (B : Set ℕ) {c m : ℕ} (hc : 1 ≤ c) (hcm : c ≤ m)
    (hB : ∀ a, a ≤ m - c → (a = 0 ∨ a ∈ B) → a + c ∈ B) :
    cnt B (m - c) + 1 + cnt B (c - 1) ≤ cnt B m := by
  rw [cnt_split B (show c - 1 ≤ m by omega)]
  have e : #{a ∈ range (m - c + 1) | a = 0 ∨ a ∈ B} = cnt B (m - c) + 1 := by
    unfold cnt
    have : ({a ∈ range (m - c + 1) | a = 0 ∨ a ∈ B} : Finset ℕ) =
        insert 0 {a ∈ Icc 1 (m - c) | a ∈ B} := by
      ext x; simp only [mem_filter, mem_range, mem_insert, mem_Icc]
      constructor
      · rintro ⟨h1, h2 | h2⟩
        · exact Or.inl h2
        · by_cases hx : x = 0
          · exact Or.inl hx
          · exact Or.inr ⟨⟨by omega, by omega⟩, h2⟩
      · rintro (h1 | ⟨⟨h1, h2⟩, h3⟩)
        · exact ⟨by omega, Or.inl h1⟩
        · exact ⟨by omega, Or.inr h3⟩
    rw [this, card_insert_of_notMem (by simp)]
  have hinj : #(({a ∈ range (m - c + 1) | a = 0 ∨ a ∈ B}).image (· + c)) =
      #{a ∈ range (m - c + 1) | a = 0 ∨ a ∈ B} :=
    card_image_of_injective _ (add_left_injective c)
  have hsub : ({a ∈ range (m - c + 1) | a = 0 ∨ a ∈ B}).image (· + c) ⊆
      {x ∈ Ioc (c - 1) m | x ∈ B} := by
    intro x hx
    simp only [mem_image, mem_filter, mem_range] at hx
    obtain ⟨a, ⟨h1, h2⟩, rfl⟩ := hx
    simp only [mem_filter, mem_Ioc]
    exact ⟨⟨by omega, by omega⟩, hB a (by omega) h2⟩
  have := card_le_card hsub
  omega


end LeanLab.Ramare1995.Theorem91
