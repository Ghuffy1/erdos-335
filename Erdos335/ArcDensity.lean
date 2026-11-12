import Erdos335.Upstream.NumStabilityAddCircle
import Erdos335.BlockCounting
import Erdos335.Specification
import Mathlib.Topology.Instances.AddCircle.DenseSubgroup

/-!
# Ordinary density of irrational arc pullbacks

The analytic input is the attributed circle-equidistribution theorem. These
bridges connect its probability-measure convention to the positive-integer
counts and closed arcs used in the full Erdős 335 target.
-/

set_option autoImplicit false

open Filter Topology
open scoped Pointwise

namespace Erdos335.Proposed

theorem irrational_addOrder {θ : ℝ} (hθ : Irrational θ) :
    addOrderOf (θ : AddCircle (1 : ℝ)) = 0 := by
  apply AddCircle.denseRange_zsmul_iff.mp
  apply AddCircle.denseRange_zsmul_coe_iff.mpr
  simpa only [div_one] using hθ

theorem fin_count_eq_prefixCount (a : AddCircle (1 : ℝ))
    (E : Set (AddCircle (1 : ℝ))) (N : ℕ) :
    ({i : Fin (N + 1) | i.val • a ∈ E}.ncard : ℕ) =
      prefixCount {n : ℕ | n • a ∈ E} (N + 1) := by
  classical
  have hset : {i : Fin (N + 1) | i.val • a ∈ E} =
      (↑(Finset.univ.filter (fun i : Fin (N + 1) => i.val • a ∈ E)) : Set (Fin (N + 1))) := by
    ext i
    simp
  rw [hset, Set.ncard_coe_finset]
  symm
  apply Finset.card_bij (fun n hn => (⟨n, Finset.mem_range.mp (Finset.mem_filter.mp hn).1⟩ : Fin (N + 1)))
  · intro n hn
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, (Finset.mem_filter.mp hn).2⟩
  · intro n hn m hm heq
    exact congrArg Fin.val heq
  · intro i hi
    refine ⟨i.val, Finset.mem_filter.mpr ⟨Finset.mem_range.mpr i.isLt, (Finset.mem_filter.mp hi).2⟩, ?_⟩
    exact Fin.ext rfl

theorem halfOpenOrbit_hasDensity (a : AddCircle (1 : ℝ)) (ha : addOrderOf a = 0)
    (lo hi : ℝ) (hlo : lo ≤ hi) (hlen : hi - lo ≤ 1) :
    HasDensity {n : ℕ | n • a ∈ NumStability.halfOpenArc lo hi} (hi - lo) := by
  have hfreq := NumStability.orbit_halfOpenArc_frequency_tendsto ha lo hi (by linarith) (by linarith)
  have hr := (ENNReal.tendsto_toReal (ENNReal.ofReal_ne_top)).comp hfreq
  have hlen0 : 0 ≤ hi - lo := by linarith
  simp only [Function.comp_def, ENNReal.toReal_div, ENNReal.toReal_natCast,
    ENNReal.toReal_ofReal hlen0, fin_count_eq_prefixCount] at hr
  apply (hasDensity_iff_prefixCount _ _).mpr
  exact (tendsto_add_atTop_iff_nat 1).mp hr

theorem negligible_of_subsingleton (E : Set ℕ) (hE : E.Subsingleton) : Negligible E := by
  classical
  by_cases hne : E.Nonempty
  · obtain ⟨n, hn⟩ := hne
    exact Negligible.of_bounded n (fun m hm => (hE hm hn).le)
  · have hemp : E = ∅ := Set.not_nonempty_iff_eq_empty.mp hne
    rw [hemp]
    exact hasDensity_empty

theorem irrational_orbitPoint_negligible {θ : ℝ} (hθ : Irrational θ)
    (c : AddCircle (1 : ℝ)) : Negligible {n : ℕ | n • (θ : AddCircle (1 : ℝ)) = c} := by
  apply negligible_of_subsingleton
  intro n hn m hm
  have hinj : Function.Injective (fun n : ℕ => n • (θ : AddCircle (1 : ℝ))) :=
    injective_nsmul_iff_not_isOfFinAddOrder.mpr (addOrderOf_eq_zero_iff.mp (irrational_addOrder hθ))
  exact hinj (hn.trans hm.symm)

theorem nsmul_coe_real (θ : ℝ) (n : ℕ) :
    n • (θ : AddCircle (1 : ℝ)) = (((n : ℝ) * θ : ℝ) : AddCircle (1 : ℝ)) := by
  rw [← AddCircle.coe_nsmul, nsmul_eq_mul]

theorem closedArcPullback_hasDensity {θ : ℝ} (hθ : Irrational θ)
    (start len : ℝ) (hlen0 : 0 < len) (hlen1 : len ≤ 1) :
    HasDensity (closedArcPullback θ start len) len := by
  let E : Set ℕ := {n | n • (θ : AddCircle (1 : ℝ)) ∈ NumStability.halfOpenArc start (start + len)}
  have hE : HasDensity E len := by
    have h := halfOpenOrbit_hasDensity (θ : AddCircle (1 : ℝ)) (irrational_addOrder hθ)
      start (start + len) (by linarith) (by linarith)
    simpa only [add_sub_cancel_left] using h
  have hpoint := irrational_orbitPoint_negligible hθ ((start + len : ℝ) : AddCircle (1 : ℝ))
  have hout : Negligible (closedArcPullback θ start len \ E) := by
    apply hpoint.mono
    rintro n ⟨hn, hnE⟩
    obtain ⟨hn0, k, hlo, hhi⟩ := hn
    have heq : (n : ℝ) * θ = start + len + k := by
      by_contra hneq
      have hlt : (n : ℝ) * θ < start + len + k := lt_of_le_of_ne hhi hneq
      apply hnE
      change n • (θ : AddCircle (1 : ℝ)) ∈ NumStability.halfOpenArc start (start + len)
      rw [nsmul_coe_real, NumStability.mem_halfOpenArc_coe_iff_exists_int_sub_mem_Ico
        (by linarith) (by linarith)]
      exact ⟨k, by constructor <;> linarith⟩
    change n • (θ : AddCircle (1 : ℝ)) = ((start + len : ℝ) : AddCircle (1 : ℝ))
    rw [nsmul_coe_real, NumStability.coe_eq_coe_iff_exists_int_sub_eq]
    exact ⟨k, by linarith⟩
  have hmissing : Negligible (E \ closedArcPullback θ start len) := by
    apply Negligible.of_bounded 0
    rintro n ⟨hn, hnC⟩
    by_contra hn0
    have hpos : 0 < n := by omega
    apply hnC
    have hn' : (((n : ℝ) * θ : ℝ) : AddCircle (1 : ℝ)) ∈
        NumStability.halfOpenArc start (start + len) := by
      change n • (θ : AddCircle (1 : ℝ)) ∈ NumStability.halfOpenArc start (start + len) at hn
      simpa only [nsmul_coe_real] using hn
    obtain ⟨k, hlo, hhi⟩ :=
      (NumStability.mem_halfOpenArc_coe_iff_exists_int_sub_mem_Ico
        (by linarith) (by linarith)).mp hn'
    exact ⟨hpos, k, by linarith, by linarith⟩
  exact (show DensityEquivalent E (closedArcPullback θ start len) from ⟨hmissing, hout⟩).hasDensity hE

theorem filled_closedArc_hasDensity {A : Set ℕ} {θ start len : ℝ}
    (hθ : Irrational θ) (hlen0 : 0 < len) (hlen1 : len ≤ 1)
    (hsub : A ⊆ closedArcPullback θ start len)
    (hmissing : Negligible (closedArcPullback θ start len \ A)) : HasDensity A len := by
  have hout : Negligible (A \ closedArcPullback θ start len) := by
    apply (show Negligible (∅ : Set ℕ) from hasDensity_empty).mono
    rintro n ⟨hn, hnot⟩
    exact (hnot (hsub hn)).elim
  have heq : DensityEquivalent A (closedArcPullback θ start len) := ⟨hout, hmissing⟩
  exact heq.symm.hasDensity (closedArcPullback_hasDensity hθ start len hlen0 hlen1)

theorem sum_closedArc_subset (θ startA startB lenA lenB : ℝ) :
    closedArcPullback θ startA lenA + closedArcPullback θ startB lenB ⊆
      closedArcPullback θ (startA + startB) (lenA + lenB) := by
  rintro n ⟨a, ⟨ha0, i, hai, hai'⟩, b, ⟨hb0, j, hbj, hbj'⟩, rfl⟩
  refine ⟨by change 0 < a + b; omega, i + j, ?_, ?_⟩
  · simp only [Nat.cast_add, Int.cast_add]
    nlinarith
  · simp only [Nat.cast_add, Int.cast_add]
    nlinarith

theorem closedArc_sum_upper_bound {A B : Set ℕ} {θ startA startB lenA lenB : ℝ}
    (hθ : Irrational θ) (hlen : 0 < lenA + lenB) (hlen1 : lenA + lenB ≤ 1)
    (hA : A ⊆ closedArcPullback θ startA lenA)
    (hB : B ⊆ closedArcPullback θ startB lenB) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ N : ℕ in atTop, (count (A + B) N : ℝ) / N ≤ lenA + lenB + ε := by
  have hsub : A + B ⊆ closedArcPullback θ (startA + startB) (lenA + lenB) :=
    (Set.add_subset_add hA hB).trans (sum_closedArc_subset θ startA startB lenA lenB)
  have hD := closedArcPullback_hasDensity hθ (startA + startB) (lenA + lenB) hlen hlen1
  have hbound : ∀ᶠ N : ℕ in atTop,
      (count (closedArcPullback θ (startA + startB) (lenA + lenB)) N : ℝ) / N <
        lenA + lenB + ε := hD (gt_mem_nhds (by linarith))
  filter_upwards [hbound] with N hN
  exact (div_le_div_of_nonneg_right (by exact_mod_cast count_mono hsub N) (Nat.cast_nonneg N)).trans hN.le

end Erdos335.Proposed
