import Erdos335.PeriodicOutput
import Erdos335.Specification
import Mathlib.Algebra.BigOperators.Group.Finset.Sigma

/-!
# Block counts and ordinary density

Half-open prefix counts make the block-mask identities exact. Their difference
from the positive-integer counting convention is uniformly bounded.
-/

set_option autoImplicit false

open Filter Topology
open scoped Pointwise

namespace Erdos335

noncomputable def prefixCount (A : Set ℕ) (N : ℕ) : ℕ := by
  classical
  exact ((Finset.range N).filter (· ∈ A)).card

theorem prefixCount_succ (A : Set ℕ) (N : ℕ) :
    prefixCount A (N + 1) = prefixCount A N +
      (by classical exact if N ∈ A then 1 else 0) := by
  classical
  simp only [prefixCount, Finset.range_add_one, Finset.filter_insert]
  split_ifs with h
  · rw [Finset.card_insert_of_notMem (by simp)]
  · omega

theorem prefixCount_succ_eq_count (A : Set ℕ) (N : ℕ) :
    prefixCount A (N + 1) = count A N +
      (by classical exact if 0 ∈ A then 1 else 0) := by
  classical
  induction N with
  | zero =>
      simpa only [Nat.zero_add, count_zero, show prefixCount A 0 = 0 by simp [prefixCount]]
        using prefixCount_succ A 0
  | succ N ih =>
      rw [prefixCount_succ, count_succ, ih]
      omega

theorem prefixCount_balance (A : Set ℕ) (N : ℕ) :
    prefixCount A N + (by classical exact if N ∈ A then 1 else 0) =
      count A N + (by classical exact if 0 ∈ A then 1 else 0) := by
  rw [← prefixCount_succ, prefixCount_succ_eq_count]

theorem prefixCount_error (A : Set ℕ) (N : ℕ) :
    |(prefixCount A N : ℝ) - count A N| ≤ 1 := by
  classical
  have h := prefixCount_balance A N
  have hupper : prefixCount A N ≤ count A N + 1 := by split_ifs at h <;> omega
  have hlower : count A N ≤ prefixCount A N + 1 := by split_ifs at h <;> omega
  have hrupper : (prefixCount A N : ℝ) ≤ count A N + 1 := by exact_mod_cast hupper
  have hrlower : (count A N : ℝ) ≤ prefixCount A N + 1 := by exact_mod_cast hlower
  rw [abs_le]
  constructor <;> linarith

theorem hasDensity_iff_prefixCount (A : Set ℕ) (d : ℝ) :
    HasDensity A d ↔ Tendsto (fun N => (prefixCount A N : ℝ) / N) atTop (𝓝 d) := by
  have hdiff : Tendsto (fun N => ((prefixCount A N : ℝ) - count A N) / N)
      atTop (𝓝 0) := by
    have h := tendsto_div_of_bounded (fun N => (prefixCount A N : ℝ) - count A N)
      0 1 (fun N => by simpa only [zero_mul, sub_zero] using prefixCount_error A N)
    simpa only [zero_mul, sub_zero] using h
  constructor
  · intro h
    have ht := h.add hdiff
    simp only [add_zero] at ht
    apply ht.congr
    intro N
    ring
  · intro h
    have ht := h.sub hdiff
    simp only [sub_zero] at ht
    apply ht.congr
    intro N
    ring

theorem prefixCount_mono (A : Set ℕ) {N M : ℕ} (h : N ≤ M) :
    prefixCount A N ≤ prefixCount A M := by
  classical
  apply Finset.card_le_card
  apply Finset.filter_subset_filter
  exact Finset.range_mono h

theorem prefixCount_add_le (A : Set ℕ) (N k : ℕ) :
    prefixCount A (N + k) ≤ prefixCount A N + k := by
  classical
  induction k with
  | zero => simp
  | succ k ih =>
      rw [Nat.add_succ, prefixCount_succ]
      split_ifs <;> omega

theorem prefixCount_multiple_error (A : Set ℕ) (q : ℕ+) (N : ℕ) :
    |(prefixCount A N : ℝ) - prefixCount A ((q : ℕ) * (N / (q : ℕ)))| ≤ q := by
  have hfloor := Nat.mod_add_div N (q : ℕ)
  have hrem := Nat.mod_lt N q.pos
  have hm : (q : ℕ) * (N / (q : ℕ)) ≤ N := by omega
  have hmono := prefixCount_mono A hm
  have hstep := prefixCount_add_le A ((q : ℕ) * (N / (q : ℕ))) (N % (q : ℕ))
  have hstep' : prefixCount A N ≤ prefixCount A ((q : ℕ) * (N / (q : ℕ))) + (q : ℕ) := by
    have hsum : (q : ℕ) * (N / (q : ℕ)) + N % (q : ℕ) = N := by omega
    rw [hsum] at hstep
    omega
  rw [abs_of_nonneg (sub_nonneg.mpr (by exact_mod_cast hmono))]
  have hc : (prefixCount A N : ℝ) ≤
      (prefixCount A ((q : ℕ) * (N / (q : ℕ))) : ℝ) + (q : ℕ) := by
    exact_mod_cast hstep'
  linarith

theorem hasDensity_iff_prefixCount_multiples (A : Set ℕ) (q : ℕ+) (d : ℝ) :
    HasDensity A d ↔ Tendsto
      (fun N => (prefixCount A ((q : ℕ) * N) : ℝ) / ((q : ℕ) * N : ℕ))
      atTop (𝓝 d) := by
  have hmul : Tendsto (fun N : ℕ => (q : ℕ) * N) atTop atTop := by
    apply tendsto_atTop.mpr
    intro b
    filter_upwards [eventually_ge_atTop b] with N hN
    exact hN.trans (Nat.le_mul_of_pos_left N q.pos)
  have hdiv : Tendsto (fun N : ℕ => N / (q : ℕ)) atTop atTop := by
    apply tendsto_atTop.mpr
    intro b
    filter_upwards [eventually_ge_atTop ((q : ℕ) * b)] with N hN
    exact (Nat.le_div_iff_mul_le q.pos).mpr (by simpa only [Nat.mul_comm] using hN)
  constructor
  · intro h
    exact ((hasDensity_iff_prefixCount A d).mp h).comp hmul
  · intro h
    have hsub := h.comp hdiv
    have hscale : Tendsto
        (fun N : ℕ => (((q : ℕ) * (N / (q : ℕ)) : ℕ) : ℝ) / N) atTop (𝓝 1) := by
      apply tendsto_div_of_bounded _ 1 (q : ℕ)
      intro N
      have heq := Nat.mod_add_div N (q : ℕ)
      have hrem := Nat.mod_lt N q.pos
      have hr : (((q : ℕ) * (N / (q : ℕ)) : ℕ) : ℝ) +
          ((N % (q : ℕ) : ℕ) : ℝ) = N := by
        exact_mod_cast (by omega : (q : ℕ) * (N / (q : ℕ)) + N % (q : ℕ) = N)
      have hrem' : ((N % (q : ℕ) : ℕ) : ℝ) ≤ (q : ℕ) := by exact_mod_cast hrem.le
      rw [one_mul, show (((q : ℕ) * (N / (q : ℕ)) : ℕ) : ℝ) - N =
        -((N % (q : ℕ) : ℕ) : ℝ) by linarith, abs_neg, abs_of_nonneg (by positivity)]
      exact hrem'
    have hproduct := hsub.mul hscale
    simp only [mul_one] at hproduct
    have hbase : Tendsto
        (fun N : ℕ => (prefixCount A ((q : ℕ) * (N / (q : ℕ))) : ℝ) / N)
        atTop (𝓝 d) := by
      apply hproduct.congr
      intro N
      by_cases hz : (q : ℕ) * (N / (q : ℕ)) = 0
      · simp [hz, prefixCount]
      · have hm0 : ((((q : ℕ) * (N / (q : ℕ)) : ℕ) : ℝ)) ≠ 0 := by exact_mod_cast hz
        dsimp only [Function.comp_def]
        field_simp
    have hdiff : Tendsto
        (fun N => ((prefixCount A N : ℝ) - prefixCount A ((q : ℕ) * (N / (q : ℕ)))) / N)
        atTop (𝓝 0) := by
      have ht := tendsto_div_of_bounded
        (fun N => (prefixCount A N : ℝ) - prefixCount A ((q : ℕ) * (N / (q : ℕ))))
        0 (q : ℕ) (fun N => by simpa using prefixCount_multiple_error A q N)
      simpa using ht
    apply (hasDensity_iff_prefixCount A d).mpr
    have ht := hbase.add hdiff
    simp only [add_zero] at ht
    apply ht.congr
    intro N
    ring

def blockSet (q : ℕ+) (F : ℕ → Finset (ZMod (q : ℕ))) : Set ℕ :=
  {n | (n : ZMod (q : ℕ)) ∈ F (n / (q : ℕ))}

theorem prefixCount_blockSet (q : ℕ+) (F : ℕ → Finset (ZMod (q : ℕ))) (N : ℕ) :
    prefixCount (blockSet q F) ((q : ℕ) * N) = ∑ k ∈ Finset.range N, (F k).card := by
  classical
  rw [← Finset.card_sigma]
  apply Finset.card_bij (fun n _ => (⟨n / (q : ℕ), (n : ZMod (q : ℕ))⟩ :
    Sigma (fun _ : ℕ => ZMod (q : ℕ))))
  · intro n hn
    obtain ⟨hn, hF⟩ := Finset.mem_filter.mp hn
    apply Finset.mem_sigma.mpr
    refine ⟨Finset.mem_range.mpr ?_, hF⟩
    exact (Nat.div_lt_iff_lt_mul q.pos).mpr (by simpa only [Nat.mul_comm] using Finset.mem_range.mp hn)
  · intro n hn m hm heq
    have hdiv := congrArg Sigma.fst heq
    have hmod := congrArg (fun p : Sigma (fun _ : ℕ => ZMod (q : ℕ)) => p.2.val) heq
    change n / (q : ℕ) = m / (q : ℕ) at hdiv
    change (n : ZMod (q : ℕ)).val = (m : ZMod (q : ℕ)).val at hmod
    simp only [ZMod.val_natCast] at hmod
    calc
      n = n % (q : ℕ) + (q : ℕ) * (n / (q : ℕ)) := (Nat.mod_add_div n (q : ℕ)).symm
      _ = m % (q : ℕ) + (q : ℕ) * (m / (q : ℕ)) := by rw [hdiv, hmod]
      _ = m := Nat.mod_add_div m (q : ℕ)
  · rintro ⟨k, r⟩ hp
    obtain ⟨hk, hr⟩ := Finset.mem_sigma.mp hp
    have hkN := Finset.mem_range.mp hk
    have hrq := r.val_lt
    refine ⟨(q : ℕ) * k + r.val, ?_, ?_⟩
    · apply Finset.mem_filter.mpr
      refine ⟨Finset.mem_range.mpr ?_, ?_⟩
      · nlinarith
      · change (((q : ℕ) * k + r.val : ℕ) : ZMod (q : ℕ)) ∈
          F (((q : ℕ) * k + r.val) / (q : ℕ))
        simpa only [Nat.mul_add_div q.pos, Nat.div_eq_of_lt hrq,
          add_zero, Nat.cast_add, Nat.cast_mul, ZMod.natCast_self, zero_mul,
          zero_add, ZMod.natCast_zmod_val] using hr
    · apply Sigma.ext
      · simp only [Nat.mul_add_div q.pos, Nat.div_eq_of_lt hrq, add_zero]
      · simp

theorem hasDensity_blockSet_iff (q : ℕ+) (F : ℕ → Finset (ZMod (q : ℕ))) (d : ℝ) :
    HasDensity (blockSet q F) d ↔ Tendsto
      (fun N => (∑ k ∈ Finset.range N, ((F k).card : ℝ)) / ((q : ℕ) * N : ℕ))
      atTop (𝓝 d) := by
  rw [hasDensity_iff_prefixCount_multiples _ q]
  simp only [prefixCount_blockSet, Nat.cast_sum]

def liftBlocks (q : ℕ+) (D : Set ℕ) : Set ℕ := {n | n / (q : ℕ) ∈ D}

theorem prefixCount_liftBlocks (q : ℕ+) (D : Set ℕ) (N : ℕ) :
    prefixCount (liftBlocks q D) ((q : ℕ) * N) = (q : ℕ) * prefixCount D N := by
  classical
  let F : ℕ → Finset (ZMod (q : ℕ)) := fun k => if k ∈ D then Finset.univ else ∅
  have heq : liftBlocks q D = blockSet q F := by
    ext n
    by_cases hn : n / (q : ℕ) ∈ D <;> simp [liftBlocks, blockSet, F, hn]
  rw [heq, prefixCount_blockSet]
  have hcard : ∀ k, (F k).card = if k ∈ D then (q : ℕ) else 0 := by
    intro k
    by_cases hk : k ∈ D <;> simp [F, hk, ZMod.card]
  simp only [hcard]
  rw [← Finset.sum_filter]
  simp [prefixCount, Nat.mul_comm]

theorem Negligible.liftBlocks {D : Set ℕ} (hD : Negligible D) (q : ℕ+) :
    Negligible (liftBlocks q D) := by
  apply (hasDensity_iff_prefixCount_multiples _ q 0).mpr
  have hd := (hasDensity_iff_prefixCount D 0).mp hD
  have hq0 : ((q : ℕ) : ℝ) ≠ 0 := by exact_mod_cast q.ne_zero
  apply hd.congr
  intro N
  rw [prefixCount_liftBlocks]
  simp only [Nat.cast_mul]
  by_cases hN : N = 0
  · simp [hN]
  · have hN0 : (N : ℝ) ≠ 0 := by exact_mod_cast hN
    field_simp

theorem prefixCount_arithmetic_preimage_le (D : Set ℕ) (q : ℕ+) {r : ℕ}
    (hr : r < (q : ℕ)) (N : ℕ) :
    prefixCount {k | (q : ℕ) * k + r ∈ D} N ≤ prefixCount D ((q : ℕ) * N) := by
  classical
  apply Finset.card_le_card_of_injOn (fun k => (q : ℕ) * k + r)
  · intro k hk
    obtain ⟨hk, hD⟩ := Finset.mem_filter.mp hk
    have hkN := Finset.mem_range.mp hk
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_range.mpr ?_, hD⟩
    nlinarith
  · intro i hi j hj hij
    exact Nat.eq_of_mul_eq_mul_left q.pos (Nat.add_right_cancel hij)

theorem Negligible.arithmetic_preimage {D : Set ℕ} (hD : Negligible D)
    (q : ℕ+) {r : ℕ} (hr : r < (q : ℕ)) : Negligible {k | (q : ℕ) * k + r ∈ D} := by
  apply (hasDensity_iff_prefixCount _ 0).mpr
  have hbase := (hasDensity_iff_prefixCount_multiples D q 0).mp hD
  have hbound : Tendsto
      (fun N => (q : ℝ) * ((prefixCount D ((q : ℕ) * N) : ℝ) / ((q : ℕ) * N : ℕ)))
      atTop (𝓝 0) := by simpa only [mul_zero] using hbase.const_mul (q : ℝ)
  apply squeeze_zero (fun N => by positivity) ?_ hbound
  intro N
  have hcard := prefixCount_arithmetic_preimage_le D q hr N
  have hle : (prefixCount {k | (q : ℕ) * k + r ∈ D} N : ℝ) / N ≤
      (prefixCount D ((q : ℕ) * N) : ℝ) / N :=
    div_le_div_of_nonneg_right (by exact_mod_cast hcard) (Nat.cast_nonneg N)
  apply hle.trans_eq
  have hq0 : ((q : ℕ) : ℝ) ≠ 0 := by exact_mod_cast q.ne_zero
  simp only [Nat.cast_mul]
  by_cases hN : N = 0
  · simp [hN]
  · have hN0 : (N : ℝ) ≠ 0 := by exact_mod_cast hN
    field_simp

theorem Negligible.add_preimage {D : Set ℕ} (hD : Negligible D) (d : ℕ) :
    Negligible {n | n + d ∈ D} := by
  apply (negligible_shift_iff _ d).mp
  apply hD.mono
  rintro n ⟨k, hk, rfl⟩
  exact hk

def transitionIndices {α : Type*} (f : ℕ → α) : Set ℕ := {k | f k ≠ f (k + 1)}

theorem eq_of_no_transition {α : Type*} (f : ℕ → α) (k d : ℕ)
    (h : ∀ i < d, f (k + i) = f (k + i + 1)) : f k = f (k + d) := by
  induction d with
  | zero => simp
  | succ d ih =>
      have hprev := ih (fun i hi => h i (by omega))
      simpa only [Nat.add_succ] using hprev.trans (h d (by omega))

theorem Negligible.forward_difference {α : Type*} {f : ℕ → α}
    (h : Negligible (transitionIndices f)) (d : ℕ) :
    Negligible {k | f k ≠ f (k + d)} := by
  classical
  have hfinite := negligible_finiteUnion (Finset.range d)
    (fun i => {k | k + i ∈ transitionIndices f})
    (fun i _ => h.add_preimage i)
  apply hfinite.mono
  intro k hk
  by_contra hout
  apply hk
  apply eq_of_no_transition
  intro i hi
  by_contra hne
  apply hout
  exact ⟨i, Finset.mem_range.mpr hi, hne⟩

theorem Negligible.backward_difference {α : Type*} {f : ℕ → α}
    (h : Negligible (transitionIndices f)) (d : ℕ) :
    Negligible {k | f (k - d) ≠ f k} := by
  have hsmall : Negligible {k : ℕ | k < d} :=
    Negligible.of_bounded d (by intro n hn; exact Nat.le_of_lt hn)
  apply (hsmall.union ((h.forward_difference d).shift d)).mono
  intro k hk
  change f (k - d) ≠ f k at hk
  by_cases hkd : k < d
  · exact Or.inl hkd
  · right
    have hd : d ≤ k := by omega
    refine ⟨k - d, ?_, Nat.sub_add_cancel hd⟩
    change f (k - d) ≠ f ((k - d) + d)
    simpa only [Nat.sub_add_cancel hd] using hk

end Erdos335
