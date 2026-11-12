import Erdos335.DysonDensity

/-!
# Fixed translations and tail sections in ordinary lower density

All counting identities retain the point zero. Tail sections are used to
normalize a prescribed representation in Kneser's pointwise argument.
-/

set_option autoImplicit false

open Filter Topology
open scoped Pointwise

namespace Erdos335

def tailShift (A : Set ℕ) (t : ℕ) : Set ℕ := {n | n + t ∈ A}

theorem prefixCount_le (A : Set ℕ) (N : ℕ) : prefixCount A N ≤ N := by
  classical
  exact (Finset.card_filter_le _ _).trans_eq (Finset.card_range N)

theorem prefixCount_add_tailShift (A : Set ℕ) (t N : ℕ) :
    prefixCount A (t + N) = prefixCount A t + prefixCount (tailShift A t) N := by
  classical
  induction N with
  | zero => simp [prefixCount]
  | succ N ih =>
      rw [Nat.add_succ, prefixCount_succ, prefixCount_succ, ih]
      simp only [tailShift, Set.mem_ofPred_eq, Nat.add_comm N t, Nat.add_assoc]

theorem count_tailShift_error (A : Set ℕ) (t N : ℕ) :
    |(count (tailShift A t) N : ℝ) - count A N| ≤ t + 2 := by
  have hsplit := prefixCount_add_tailShift A t N
  have hmono := prefixCount_mono A (show N ≤ t + N by omega)
  have hupp := prefixCount_add_le A N t
  rw [Nat.add_comm N t] at hupp
  have ht := prefixCount_le A t
  have h1 := prefixCount_error A N
  have h2 := prefixCount_error (tailShift A t) N
  have hup : prefixCount (tailShift A t) N ≤ prefixCount A N + t := by omega
  have hlo : prefixCount A N ≤ prefixCount (tailShift A t) N + t := by omega
  have hupR : (prefixCount (tailShift A t) N : ℝ) ≤ prefixCount A N + t := by exact_mod_cast hup
  have hloR : (prefixCount A N : ℝ) ≤ prefixCount (tailShift A t) N + t := by exact_mod_cast hlo
  rw [abs_le] at *
  constructor <;> linarith

theorem count_difference_tendsto_zero_of_bounded {A B : Set ℕ} {K : ℝ}
    (h : ∀ N, |(count B N : ℝ) - count A N| ≤ K) :
    Tendsto (fun N : ℕ => ((count B N : ℝ) - count A N) / N) atTop (𝓝 0) := by
  have ht := tendsto_div_of_bounded (fun N => (count B N : ℝ) - count A N) 0 K
    (fun N => by simpa only [zero_mul, sub_zero] using h N)
  simpa using ht

theorem lowerDensity_eq_of_bounded_count_error {A B : Set ℕ} {K : ℝ}
    (h : ∀ N, |(count B N : ℝ) - count A N| ≤ K) : lowerDensity B = lowerDensity A := by
  have hz := count_difference_tendsto_zero_of_bounded h
  have hl := liminf_add_of_tendsto_zero hz (count_ratio_bounded_below A) (count_ratio_bounded_above A)
  unfold lowerDensity
  rw [← hl]
  apply liminf_congr
  apply Eventually.of_forall
  intro N
  simp only [Pi.add_apply]
  ring

theorem HasDensity.of_bounded_count_error {A B : Set ℕ} {K d : ℝ}
    (hA : HasDensity A d) (h : ∀ N, |(count B N : ℝ) - count A N| ≤ K) : HasDensity B d := by
  have ht := hA.add (count_difference_tendsto_zero_of_bounded h)
  rw [add_zero] at ht
  apply ht.congr
  intro N
  ring

theorem lowerDensity_shift (A : Set ℕ) (t : ℕ) : lowerDensity (shift A t) = lowerDensity A :=
  lowerDensity_eq_of_bounded_count_error (fun N => count_shift_error A N t)

theorem lowerDensity_tailShift (A : Set ℕ) (t : ℕ) : lowerDensity (tailShift A t) = lowerDensity A :=
  lowerDensity_eq_of_bounded_count_error (fun N => count_tailShift_error A t N)

theorem HasDensity.tailShift {A : Set ℕ} {d : ℝ} (hA : HasDensity A d) (t : ℕ) :
    HasDensity (Erdos335.tailShift A t) d :=
  hA.of_bounded_count_error (fun N => count_tailShift_error A t N)

theorem jointLowerDensity_tailShift (A B : Set ℕ) (a b : ℕ) :
    jointLowerDensity (tailShift A a) (tailShift B b) = jointLowerDensity A B := by
  have hbound : ∀ N : ℕ,
      |((count (tailShift A a) N : ℝ) + count (tailShift B b) N) -
        (count A N + count B N)| ≤ a + b + 4 := by
    intro N
    have h1 := count_tailShift_error A a N
    have h2 := count_tailShift_error B b N
    rw [abs_le] at *
    constructor <;> linarith
  have hz := tendsto_div_of_bounded
    (fun N => ((count (tailShift A a) N : ℝ) + count (tailShift B b) N) -
      (count A N + count B N)) 0 (a + b + 4) (fun N => by simpa using hbound N)
  have hl := liminf_add_of_tendsto_zero hz (jointCount_bounded_below A B) (jointCount_bounded_above A B)
  unfold jointLowerDensity
  rw [← hl]
  apply liminf_congr
  apply Eventually.of_forall
  intro N
  simp only [Pi.add_apply]
  ring

theorem shift_tailShift (A : Set ℕ) (t : ℕ) : shift (tailShift A t) t = A ∩ Set.Ici t := by
  ext n
  constructor
  · rintro ⟨a, ha, rfl⟩
    exact ⟨ha, by simp⟩
  · rintro ⟨hn, htn⟩
    exact ⟨n - t, by simpa [tailShift, Nat.sub_add_cancel htn] using hn,
      Nat.sub_add_cancel htn⟩

theorem shift_tailShift_sum_subset (A B : Set ℕ) (a b : ℕ) :
    shift (tailShift A a + tailShift B b) (a + b) ⊆ A + B := by
  rintro n ⟨z, ⟨x, hx, y, hy, rfl⟩, rfl⟩
  exact ⟨x + a, hx, y + b, hy, by dsimp only; omega⟩

theorem lowerDensity_ge_of_prefixCount {A : Set ℕ} {δ : ℝ}
    (h : ∀ N : ℕ, δ * N ≤ (prefixCount A N : ℝ)) : δ ≤ lowerDensity A := by
  have ht := (tendsto_const_nhds.sub (tendsto_const_div_atTop_nhds_zero_nat 1) :
    Tendsto (fun N : ℕ => δ - 1 / (N : ℝ)) atTop (𝓝 (δ - 0)))
  have hb : ∀ᶠ N : ℕ in atTop, δ - 1 / (N : ℝ) ≤ (count A N : ℝ) / N := by
    filter_upwards [eventually_ge_atTop 1] with N hN
    have hNR : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
    have hp := h N
    have he := (abs_le.mp (prefixCount_error A N)).2
    apply (le_div_iff₀ hNR).mpr
    have hcancel : (1 / (N : ℝ)) * N = 1 := by field_simp
    nlinarith
  have hl := liminf_le_liminf hb ht.isBoundedUnder_ge
    (count_ratio_bounded_above A).isCobounded_flip
  simpa only [lowerDensity, ht.liminf_eq, sub_zero] using hl

theorem eq_univ_of_full_prefixCount {A : Set ℕ}
    (h : ∀ N : ℕ, (N : ℝ) ≤ (prefixCount A N : ℝ)) : A = Set.univ := by
  classical
  apply Set.eq_univ_of_forall
  intro n
  have hcard : n + 1 ≤ ((Finset.range (n + 1)).filter (· ∈ A)).card := by
    exact_mod_cast h (n + 1)
  have heq : (Finset.range (n + 1)).filter (· ∈ A) = Finset.range (n + 1) := by
    apply Finset.eq_of_subset_of_card_le (Finset.filter_subset _ _)
    simpa only [Finset.card_range] using hcard
  have hn : n ∈ (Finset.range (n + 1)).filter (· ∈ A) := by rw [heq]; simp
  exact (Finset.mem_filter.mp hn).2

theorem lowerDensity_sum_ge_joint_of_finite_right (A B : Set ℕ)
    (hB0 : 0 ∈ B) (hB : B.Finite) : jointLowerDensity A B ≤ lowerDensity (A + B) := by
  obtain ⟨K, hK⟩ := hB.bddAbove
  have hd : HasDensity B 0 := Negligible.of_bounded K hK
  have hsum := jointLowerDensity_le_upperDensity_add_lowerDensity A B
  rw [hd.upperDensity_eq, zero_add] at hsum
  have hsub : A ⊆ A + B := fun a ha => ⟨a, ha, 0, hB0, by simp⟩
  exact hsum.trans (lowerDensity_mono hsub)

theorem infinite_right_of_lowerDensity_sum_lt (A B : Set ℕ) (hB0 : 0 ∈ B)
    (hgap : lowerDensity (A + B) < jointLowerDensity A B) : B.Infinite := by
  by_contra h
  exact hgap.not_ge (lowerDensity_sum_ge_joint_of_finite_right A B hB0 (Set.not_infinite.mp h))

end Erdos335
