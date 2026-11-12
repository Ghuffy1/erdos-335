import Erdos335.Residues

/-!
# Density-zero errors and fixed translates

All counts refer to the actual positive integer prefix. In particular a point
at zero is accounted for when a fixed translate moves it into that prefix.
-/

set_option autoImplicit false

open Filter Topology
open scoped Pointwise

namespace Erdos335

def Negligible (A : Set ℕ) : Prop := HasDensity A 0

def DensityEquivalent (A B : Set ℕ) : Prop :=
  Negligible (A \ B) ∧ Negligible (B \ A)

def shift (A : Set ℕ) (t : ℕ) : Set ℕ := (fun a => a + t) '' A

theorem hasDensity_empty : HasDensity (∅ : Set ℕ) 0 := by
  simp [HasDensity, count]

theorem count_union_le (A B : Set ℕ) (N : ℕ) :
    count (A ∪ B) N ≤ count A N + count B N := by
  classical
  unfold count
  simpa only [Set.mem_union, Finset.filter_or] using
    Finset.card_union_le ((Finset.Icc 1 N).filter (fun n => n ∈ A))
      ((Finset.Icc 1 N).filter (fun n => n ∈ B))

theorem count_union_of_disjoint (A B : Set ℕ) (hAB : Disjoint A B) (N : ℕ) :
    count (A ∪ B) N = count A N + count B N := by
  classical
  unfold count
  simp only [Set.mem_union, Finset.filter_or]
  apply Finset.card_union_of_disjoint
  apply Finset.disjoint_left.mpr
  intro n hnA hnB
  exact Set.disjoint_left.mp hAB (Finset.mem_filter.mp hnA).2 (Finset.mem_filter.mp hnB).2

theorem count_partition (A B : Set ℕ) (N : ℕ) :
    count A N = count (A \ B) N + count (A ∩ B) N := by
  have heq : A = (A \ B) ∪ (A ∩ B) := by
    ext n
    constructor
    · intro hn
      by_cases hnB : n ∈ B
      · exact Or.inr ⟨hn, hnB⟩
      · exact Or.inl ⟨hn, hnB⟩
    · rintro (⟨hn, _⟩ | ⟨hn, _⟩) <;> exact hn
  have hd : Disjoint (A \ B) (A ∩ B) := by
    apply Set.disjoint_left.mpr
    intro n hn hm
    exact hn.2 hm.2
  conv_lhs => rw [heq]
  exact count_union_of_disjoint _ _ hd N

theorem count_balance (A B : Set ℕ) (N : ℕ) :
    count A N + count (B \ A) N = count B N + count (A \ B) N := by
  have hA := count_partition A B N
  have hB := count_partition B A N
  rw [Set.inter_comm B A] at hB
  omega

theorem Negligible.mono {A B : Set ℕ} (hB : Negligible B) (hAB : A ⊆ B) :
    Negligible A := by
  apply squeeze_zero (fun N => by positivity) ?_ hB
  intro N
  exact div_le_div_of_nonneg_right (by exact_mod_cast count_mono hAB N) (Nat.cast_nonneg N)

theorem Negligible.union {A B : Set ℕ} (hA : Negligible A) (hB : Negligible B) :
    Negligible (A ∪ B) := by
  have hlim : Tendsto (fun N => (count A N : ℝ) / N + (count B N : ℝ) / N)
      atTop (𝓝 0) := by simpa using hA.add hB
  apply squeeze_zero (fun N => by positivity) ?_ hlim
  intro N
  rw [← add_div]
  exact div_le_div_of_nonneg_right (by exact_mod_cast count_union_le A B N) (Nat.cast_nonneg N)

theorem densityEquivalent_iff_symmetric_difference (A B : Set ℕ) :
    DensityEquivalent A B ↔ Negligible ((A \ B) ∪ (B \ A)) := by
  constructor
  · intro h
    exact h.1.union h.2
  · intro h
    exact ⟨h.mono (by intro n hn; exact Or.inl hn),
      h.mono (by intro n hn; exact Or.inr hn)⟩

theorem Negligible.of_bounded {A : Set ℕ} (K : ℕ) (hA : ∀ n ∈ A, n ≤ K) :
    Negligible A := by
  apply hasDensity_empty.of_eventually_eq K
  intro n hn
  constructor
  · intro h
    exact h.elim
  · intro h
    have := hA n h
    omega

theorem DensityEquivalent.refl (A : Set ℕ) : DensityEquivalent A A := by
  simpa [DensityEquivalent, Negligible] using And.intro hasDensity_empty hasDensity_empty

theorem DensityEquivalent.symm {A B : Set ℕ} (h : DensityEquivalent A B) :
    DensityEquivalent B A := ⟨h.2, h.1⟩

theorem DensityEquivalent.trans {A B C : Set ℕ}
    (hAB : DensityEquivalent A B) (hBC : DensityEquivalent B C) : DensityEquivalent A C := by
  constructor
  · apply (hAB.1.union hBC.1).mono
    intro n hn
    by_cases hnB : n ∈ B
    · exact Or.inr ⟨hnB, hn.2⟩
    · exact Or.inl ⟨hn.1, hnB⟩
  · apply (hBC.2.union hAB.2).mono
    intro n hn
    by_cases hnB : n ∈ B
    · exact Or.inr ⟨hnB, hn.2⟩
    · exact Or.inl ⟨hn.1, hnB⟩

theorem DensityEquivalent.hasDensity {A B : Set ℕ} {d : ℝ}
    (hAB : DensityEquivalent A B) (hA : HasDensity A d) : HasDensity B d := by
  have hlim := (hA.add hAB.2).sub hAB.1
  simp only [add_zero, sub_zero] at hlim
  apply hlim.congr
  intro N
  have hbal : (count A N : ℝ) + count (B \ A) N =
      (count B N : ℝ) + count (A \ B) N := by exact_mod_cast count_balance A B N
  change (count A N : ℝ) / N + (count (B \ A) N : ℝ) / N -
    (count (A \ B) N : ℝ) / N = (count B N : ℝ) / N
  rw [← add_div, ← sub_div]
  congr 1
  linarith

theorem DensityEquivalent.hasDensity_iff {A B : Set ℕ} {d : ℝ}
    (hAB : DensityEquivalent A B) : HasDensity A d ↔ HasDensity B d :=
  ⟨hAB.hasDensity, hAB.symm.hasDensity⟩

theorem count_add_le (A : Set ℕ) (N t : ℕ) : count A (N + t) ≤ count A N + t := by
  classical
  induction t with
  | zero => simp
  | succ t ih =>
    rw [Nat.add_succ, count_succ]
    split_ifs <;> omega

theorem count_le_count_shift (A : Set ℕ) (N t : ℕ) :
    count A N ≤ count (shift A t) (N + t) := by
  classical
  apply Finset.card_le_card_of_injOn (fun a => a + t)
  · intro a ha
    obtain ⟨haN, haA⟩ := Finset.mem_filter.mp ha
    obtain ⟨ha0, haN⟩ := Finset.mem_Icc.mp haN
    refine Finset.mem_filter.mpr ⟨?_, ⟨a, haA, rfl⟩⟩
    apply Finset.mem_Icc.mpr
    change 1 ≤ a + t ∧ a + t ≤ N + t
    omega
  · intro a _ b _ h
    exact Nat.add_right_cancel h

theorem count_shift_le_count_add_one (A : Set ℕ) (N t : ℕ) :
    count (shift A t) N ≤ count A N + 1 := by
  classical
  have hcount : count (shift A t) N ≤
      (((Finset.Icc 1 N).filter (fun a => a ∈ A)) ∪ {0}).card := by
    apply Finset.card_le_card_of_injOn (fun n => n - t)
    · intro n hn
      obtain ⟨hnN, hnA⟩ := Finset.mem_filter.mp hn
      obtain ⟨a, ha, rfl⟩ := hnA
      dsimp only at hnN ⊢
      rw [Nat.add_sub_cancel]
      have haN := (Finset.mem_Icc.mp hnN).2
      by_cases ha0 : a = 0
      · simp [ha0]
      · apply Finset.mem_union_left
        exact Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr (by omega), by simpa using ha⟩
    · intro n hn m hm hnm
      obtain ⟨a, ha, heqa⟩ := (Finset.mem_filter.mp hn).2
      obtain ⟨b, hb, heqb⟩ := (Finset.mem_filter.mp hm).2
      change a + t = n at heqa
      change b + t = m at heqb
      change n - t = m - t at hnm
      omega
  exact hcount.trans ((Finset.card_union_le _ _).trans (by simp [count]))

theorem count_shift_error (A : Set ℕ) (N t : ℕ) :
    |(count (shift A t) N : ℝ) - count A N| ≤ t + 1 := by
  have hupper : (count (shift A t) N : ℝ) ≤ count A N + 1 := by
    exact_mod_cast count_shift_le_count_add_one A N t
  have hlower : (count A N : ℝ) ≤ count (shift A t) N + t := by
    exact_mod_cast (count_le_count_shift A N t).trans (count_add_le (shift A t) N t)
  rw [abs_le]
  constructor <;> linarith

theorem HasDensity.shift {A : Set ℕ} {d : ℝ} (hA : HasDensity A d) (t : ℕ) :
    HasDensity (Erdos335.shift A t) d := by
  have hdiff : Tendsto (fun N => ((count (Erdos335.shift A t) N : ℝ) - count A N) / N)
      atTop (𝓝 0) := by
    have h := tendsto_div_of_bounded
      (fun N => (count (Erdos335.shift A t) N : ℝ) - count A N) 0 (t + 1)
      (fun N => by simpa using count_shift_error A N t)
    simpa using h
  have hlim := hA.add hdiff
  simp only [add_zero] at hlim
  apply hlim.congr
  intro N
  ring

theorem Negligible.shift {A : Set ℕ} (hA : Negligible A) (t : ℕ) :
    Negligible (Erdos335.shift A t) := HasDensity.shift hA t

theorem shift_sdiff (A B : Set ℕ) (t : ℕ) :
    shift (A \ B) t = shift A t \ shift B t := by
  ext n
  constructor
  · rintro ⟨a, ⟨haA, haB⟩, rfl⟩
    refine ⟨⟨a, haA, rfl⟩, ?_⟩
    rintro ⟨b, hb, hba⟩
    have : b = a := Nat.add_right_cancel hba
    exact haB (this ▸ hb)
  · rintro ⟨⟨a, ha, rfl⟩, hn⟩
    refine ⟨a, ⟨ha, ?_⟩, rfl⟩
    intro haB
    exact hn ⟨a, haB, rfl⟩

theorem DensityEquivalent.shift {A B : Set ℕ} (hAB : DensityEquivalent A B) (t : ℕ) :
    DensityEquivalent (Erdos335.shift A t) (Erdos335.shift B t) := by
  constructor
  · rw [← shift_sdiff]
    exact Negligible.shift hAB.1 t
  · rw [← shift_sdiff]
    exact Negligible.shift hAB.2 t

theorem DensityEquivalent.of_eventually_eq {A B : Set ℕ} (K : ℕ)
    (h : ∀ n, K < n → (n ∈ A ↔ n ∈ B)) : DensityEquivalent A B := by
  constructor
  · apply Negligible.of_bounded K
    rintro n ⟨hnA, hnB⟩
    by_contra hK
    have hn : K < n := by omega
    exact hnB ((h n hn).mp hnA)
  · apply Negligible.of_bounded K
    rintro n ⟨hnB, hnA⟩
    by_contra hK
    have hn : K < n := by omega
    exact hnA ((h n hn).mpr hnB)

def finiteUnion {ι : Type*} (F : Finset ι) (E : ι → Set ℕ) : Set ℕ :=
  {n | ∃ i ∈ F, n ∈ E i}

theorem negligible_finiteUnion {ι : Type*} (F : Finset ι) (E : ι → Set ℕ)
    (h : ∀ i ∈ F, Negligible (E i)) : Negligible (finiteUnion F E) := by
  classical
  revert h
  induction F using Finset.induction_on with
  | empty =>
    intro _
    simpa [finiteUnion, Negligible] using hasDensity_empty
  | @insert i F hi ih =>
    intro h
    have hrest := ih (fun j hj => h j (Finset.mem_insert_of_mem hj))
    have heq : finiteUnion (insert i F) E = E i ∪ finiteUnion F E := by
      ext n
      simp only [finiteUnion, Set.mem_ofPred_eq, Finset.mem_insert, Set.mem_union]
      constructor
      · rintro ⟨j, rfl | hj, hn⟩
        · exact Or.inl hn
        · exact Or.inr ⟨j, hj, hn⟩
      · rintro (hn | ⟨j, hj, hn⟩)
        · exact ⟨i, Or.inl rfl, hn⟩
        · exact ⟨j, Or.inr hj, hn⟩
    rw [heq]
    exact (h i (Finset.mem_insert_self i F)).union hrest

theorem periodicSet_mono {q : ℕ} {S T : Finset (ZMod q)} (hST : S ⊆ T) :
    periodicSet S ⊆ periodicSet T := fun _ hn => ⟨hn.1, hST hn.2⟩

theorem shift_periodic_equiv {q : ℕ} [NeZero q] (S : Finset (ZMod q)) (t : ℕ) :
    DensityEquivalent (shift (periodicSet S) t) (periodicSet ({(t : ZMod q)} + S)) := by
  classical
  apply DensityEquivalent.of_eventually_eq t
  intro n hn
  constructor
  · rintro ⟨a, ha, rfl⟩
    refine ⟨by omega, ?_⟩
    exact Finset.mem_add.mpr ⟨(t : ZMod q), by simp, (a : ZMod q), ha.2,
      by simp [Nat.cast_add, add_comm]⟩
  · rintro ⟨_, hr⟩
    obtain ⟨r, hr, s, hs, hrs⟩ := Finset.mem_add.mp hr
    have hr' : r = (t : ZMod q) := by simpa using hr
    subst r
    refine ⟨n - t, ⟨by omega, ?_⟩, ?_⟩
    · rw [Nat.cast_sub (by omega), ← hrs]
      simpa using hs
    · change n - t + t = n
      omega

theorem shift_subset_sum {A B : Set ℕ} {a : ℕ} (ha : a ∈ A) : shift B a ⊆ A + B := by
  rintro n ⟨b, hb, rfl⟩
  exact ⟨a, ha, b, hb, Nat.add_comm a b⟩

theorem periodic_core_subset_residues {q : ℕ} [NeZero q] {A : Set ℕ}
    {S : Finset (ZMod q)} (hA : DensityEquivalent A (periodicSet S)) :
    S ⊆ residues q A := by
  classical
  intro r hr
  by_contra hnot
  have hsmall : Negligible (periodicSet ({r} : Finset (ZMod q))) := by
    apply hA.2.mono
    intro n hn
    have hnr : (n : ZMod q) = r := by simpa using hn.2
    refine ⟨⟨hn.1, hnr ▸ hr⟩, ?_⟩
    intro hnA
    exact hnot (mem_residues.mpr ⟨n, hnA, hnr⟩)
  have hlarge : HasDensity (periodicSet ({r} : Finset (ZMod q))) (1 / (q : ℝ)) := by
    simpa using hasDensity_periodicSet ({r} : Finset (ZMod q))
  have hz := HasDensity.unique hsmall hlarge
  have hq : (0 : ℝ) < q := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne q)
  have hp : 0 < 1 / (q : ℝ) := one_div_pos.mpr hq
  linarith

theorem HasDensity.sdiff_of_negligible_reverse {A B : Set ℕ} {a b : ℝ}
    (hA : HasDensity A a) (hB : HasDensity B b) (hBA : Negligible (B \ A)) :
    HasDensity (A \ B) (a - b) := by
  have hlim := (hA.add hBA).sub hB
  simp only [add_zero] at hlim
  apply hlim.congr
  intro N
  have hbal : (count A N : ℝ) + count (B \ A) N =
      (count B N : ℝ) + count (A \ B) N := by exact_mod_cast count_balance A B N
  rw [← add_div, ← sub_div]
  congr 1
  linarith

end Erdos335
