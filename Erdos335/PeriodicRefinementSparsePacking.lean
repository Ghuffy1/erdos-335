import Erdos335.PeriodicRefinementSparseGcd
import Erdos335.FiniteSections
import Erdos335.PackingDensity

/-!
# Exact interval tests for growth of a sparse terminal

Private proof development. Verification status is recorded separately.
Runs and intervals are clipped to the first N zero-based indices. Source
runs come from each input separately and target runs come from V.
-/

set_option autoImplicit false

open Filter Set Topology
open scoped Pointwise

noncomputable section
attribute [local instance] Classical.propDecidable

namespace Erdos335.Proposed

private theorem unit_mask_mem (S : Set ℕ) (k : ℕ) :
    (0 : ZMod 1) ∈ mask S 1 k ↔ k ∈ S := by
  have h := (mem_mask (A := S) (q := (1 : ℕ+)) (k := k)
    (r := (0 : ZMod ((1 : ℕ+) : ℕ))))
  exact h.trans (by norm_num)

noncomputable def sparseEscapingIntervals (D V : Set ℕ) (N : ℕ) :
    Finset IntervalPacking.Interval := by
  classical
  exact (prefixRuns D D 1 N).biUnion fun I =>
    (prefixRuns V V 1 N).biUnion fun J =>
      (prefixRuns V V 1 N).biUnion fun K =>
        if (0 : ZMod 1) ∈ mask D 1 I.1 ∧
            (0 : ZMod 1) ∈ mask V 1 J.1 ∧ (0 : ZMod 1) ∉ mask V 1 K.1 then
          {clippedInterval 1 I J K 0 0}
        else ∅

def SparseEscapePacking (D V : Set ℕ) : Prop :=
  Tendsto (fun N =>
    (IntervalPacking.packingSize (sparseEscapingIntervals D V N) : ℝ) / N)
      atTop (𝓝 0)

theorem mem_sparse_escaping_intervals_iff (D V : Set ℕ) (N k : ℕ) :
    (k : ℤ) ∈ IntervalPacking.covered (sparseEscapingIntervals D V N) ↔
      k < N ∧ k ∈ D + V ∧ k ∉ V := by
  classical
  constructor
  · intro hk
    obtain ⟨L, hL, hkL⟩ := Finset.mem_biUnion.mp hk
    unfold sparseEscapingIntervals at hL
    obtain ⟨I, hI, hL⟩ := Finset.mem_biUnion.mp hL
    obtain ⟨J, hJ, hL⟩ := Finset.mem_biUnion.mp hL
    obtain ⟨K, hK, hL⟩ := Finset.mem_biUnion.mp hL
    split_ifs at hL with hoccupancy
    · obtain rfl := Finset.mem_singleton.mp hL
      obtain ⟨hkK, i, hi, j, hj, hsum⟩ :=
        (mem_clippedInterval_iff 1 I J K 0 0 k
          (prefixRun_bounds hI).1 (prefixRun_bounds hJ).1).mp hkL
      have hiD : i ∈ D := by
        have hm : (0 : ZMod 1) ∈ mask D 1 i := by
          rw [prefixRun_maskA hI hi]
          exact hoccupancy.1
        exact (unit_mask_mem D i).mp hm
      have hjV : j ∈ V := by
        have hm : (0 : ZMod 1) ∈ mask V 1 j := by
          rw [prefixRun_maskA hJ hj]
          exact hoccupancy.2.1
        exact (unit_mask_mem V j).mp hm
      have hkV : k ∉ V := by
        have hm : (0 : ZMod 1) ∉ mask V 1 k := by
          rw [prefixRun_maskA hK hkK]
          exact hoccupancy.2.2
        intro hk
        exact hm ((unit_mask_mem V k).mpr hk)
      refine ⟨(Finset.mem_Icc.mp hkK).2.trans_lt (prefixRun_bounds hK).2,
        ⟨i, hiD, j, hjV, ?_⟩, hkV⟩
      simpa only [carry, ZMod.val_zero, zero_add, Nat.zero_div, add_zero] using hsum
    · simpa using hL
  · rintro ⟨hkN, ⟨i, hiD, j, hjV, hij⟩, hkV⟩
    change i + j = k at hij
    have hiN : i < N := (show i ≤ k by omega).trans_lt hkN
    have hjN : j < N := (show j ≤ k by omega).trans_lt hkN
    obtain ⟨I, hI, hiI⟩ := prefixRun_exists D D 1 hiN
    obtain ⟨J, hJ, hjJ⟩ := prefixRun_exists V V 1 hjN
    obtain ⟨K, hK, hkK⟩ := prefixRun_exists V V 1 hkN
    have hDI : (0 : ZMod 1) ∈ mask D 1 I.1 := by
      rw [← prefixRun_maskA hI hiI]
      exact (unit_mask_mem D i).mpr hiD
    have hVJ : (0 : ZMod 1) ∈ mask V 1 J.1 := by
      rw [← prefixRun_maskA hJ hjJ]
      exact (unit_mask_mem V j).mpr hjV
    have hVK : (0 : ZMod 1) ∉ mask V 1 K.1 := by
      rw [← prefixRun_maskA hK hkK]
      intro hm
      exact hkV ((unit_mask_mem V k).mp hm)
    apply Finset.mem_biUnion.mpr
    refine ⟨clippedInterval 1 I J K 0 0, ?_, ?_⟩
    · unfold sparseEscapingIntervals
      apply Finset.mem_biUnion.mpr
      refine ⟨I, hI, Finset.mem_biUnion.mpr ⟨J, hJ,
        Finset.mem_biUnion.mpr ⟨K, hK, ?_⟩⟩⟩
      rw [if_pos ⟨hDI, hVJ, hVK⟩]
      exact Finset.mem_singleton_self _
    · apply (mem_clippedInterval_iff 1 I J K 0 0 k
        (prefixRun_bounds hI).1 (prefixRun_bounds hJ).1).mpr
      exact ⟨hkK, i, hiI, j, hjJ,
        by simpa only [carry, ZMod.val_zero, zero_add, Nat.zero_div, add_zero] using hij⟩

theorem sparse_escaping_intervals_bounds (D V : Set ℕ) (N : ℕ) (z : ℤ)
    (hz : z ∈ IntervalPacking.covered (sparseEscapingIntervals D V N)) :
    0 ≤ z ∧ z < N := by
  classical
  obtain ⟨L, hL, hzL⟩ := Finset.mem_biUnion.mp hz
  unfold sparseEscapingIntervals at hL
  obtain ⟨I, hI, hL⟩ := Finset.mem_biUnion.mp hL
  obtain ⟨J, hJ, hL⟩ := Finset.mem_biUnion.mp hL
  obtain ⟨K, hK, hL⟩ := Finset.mem_biUnion.mp hL
  split_ifs at hL with hoccupancy
  · obtain rfl := Finset.mem_singleton.mp hL
    have hKbound := prefixRun_bounds hK
    simp only [IntervalPacking.points, clippedInterval, Finset.mem_Icc,
      max_le_iff, le_min_iff] at hzL
    constructor <;> omega
  · simpa using hL

theorem sparse_escaping_intervals_eq_image (D V : Set ℕ) (N : ℕ) :
    IntervalPacking.covered (sparseEscapingIntervals D V N) =
      (((Finset.range N).filter (fun k => k ∈ (D + V) \ V)).image (fun k : ℕ => (k : ℤ))) := by
  classical
  ext z
  constructor
  · intro hz
    have hbound := sparse_escaping_intervals_bounds D V N z hz
    have hzcast : (z.toNat : ℤ) = z := Int.toNat_of_nonneg hbound.1
    rw [← hzcast] at hz
    have hnat := (mem_sparse_escaping_intervals_iff D V N z.toNat).mp hz
    apply Finset.mem_image.mpr
    refine ⟨z.toNat, ?_, hzcast⟩
    simpa only [Finset.mem_filter, Finset.mem_range, Set.mem_sdiff] using hnat
  · intro hz
    obtain ⟨k, hk, rfl⟩ := Finset.mem_image.mp hz
    apply (mem_sparse_escaping_intervals_iff D V N k).mpr
    simpa only [Finset.mem_filter, Finset.mem_range, Set.mem_sdiff] using hk

theorem sparse_escaping_intervals_card (D V : Set ℕ) (N : ℕ) :
    (IntervalPacking.covered (sparseEscapingIntervals D V N)).card =
      prefixCount ((D + V) \ V) N := by
  classical
  rw [sparse_escaping_intervals_eq_image]
  have hinjective : Function.Injective (fun k : ℕ => (k : ℤ)) := by
    intro a b hab
    change (a : ℤ) = (b : ℤ) at hab
    exact_mod_cast hab
  calc
    _ = ((Finset.range N).filter (fun k => k ∈ (D + V) \ V)).card :=
      Finset.card_image_of_injective _ hinjective
    _ = prefixCount ((D + V) \ V) N := by
      unfold prefixCount
      congr 1
      ext k
      simp only [Finset.mem_filter, Finset.mem_range]

theorem sparse_escape_packing_iff (D V : Set ℕ) :
    SparseEscapePacking D V ↔ Negligible ((D + V) \ V) := by
  change Tendsto (fun N =>
    (IntervalPacking.packingSize (sparseEscapingIntervals D V N) : ℝ) / N)
      atTop (𝓝 0) ↔ HasDensity ((D + V) \ V) 0
  rw [hasDensity_iff_prefixCount]
  simpa only [sparse_escaping_intervals_card] using
    IntervalPacking.packing_vanishes_iff_covered_vanishes
      (fun N => sparseEscapingIntervals D V N)

theorem negligible_iff_zero_sections (E : Set ℕ) (g : ℕ+) :
    Negligible E ↔ ∀ r : ZMod (g : ℕ), Negligible (zeroSection E g r) := by
  classical
  constructor
  · intro hE r
    exact hE.arithmetic_preimage g r.val_lt
  · intro hsections
    have hzero := negligible_finiteUnion (Finset.univ : Finset (ZMod (g : ℕ)))
      (fun r => zeroSection E g r) (fun r hr => hsections r)
    apply (hzero.liftBlocks g).mono
    intro n hn
    refine ⟨(n : ZMod (g : ℕ)), Finset.mem_univ _, ?_⟩
    change (g : ℕ) * (n / (g : ℕ)) + (n : ZMod (g : ℕ)).val ∈ E
    have hdecomp : (g : ℕ) * (n / (g : ℕ)) + (n : ZMod (g : ℕ)).val = n := by
      simpa only [ZMod.val_natCast, Nat.add_comm] using Nat.mod_add_div n (g : ℕ)
    simpa only [hdecomp] using hn

theorem zero_section_sum_of_multiples (D V : Set ℕ) (g : ℕ+)
    (hD : ∀ d ∈ D, (g : ℕ) ∣ d) (r : ZMod (g : ℕ)) :
    zeroSection (D + V) g r = zeroSection D g 0 + zeroSection V g r := by
  ext k
  constructor
  · rintro ⟨d, hd, v, hv, heq⟩
    obtain ⟨i, rfl⟩ := hD d hd
    have hres : (v : ZMod (g : ℕ)) = r := by
      have he := congrArg (fun n : ℕ => (n : ZMod (g : ℕ))) heq
      simpa only [Nat.cast_add, Nat.cast_mul, ZMod.natCast_self, zero_mul,
        zero_add, ZMod.natCast_zmod_val] using he
    have hvmod : v % (g : ℕ) = r.val := by
      simpa only [ZMod.val_natCast] using congrArg ZMod.val hres
    have hvdecomp : (g : ℕ) * (v / (g : ℕ)) + r.val = v := by
      simpa only [hvmod, Nat.add_comm] using Nat.mod_add_div v (g : ℕ)
    refine ⟨i, ?_, v / (g : ℕ), ?_, ?_⟩
    · simpa only [zeroSection, Set.mem_setOf_eq, ZMod.val_zero, add_zero] using hd
    · change (g : ℕ) * (v / (g : ℕ)) + r.val ∈ V
      simpa only [hvdecomp] using hv
    · apply Nat.eq_of_mul_eq_mul_left g.pos
      nlinarith
  · rintro ⟨i, hi, j, hj, rfl⟩
    refine ⟨(g : ℕ) * i, ?_, (g : ℕ) * j + r.val, hj, ?_⟩
    · simpa only [zeroSection, Set.mem_setOf_eq, ZMod.val_zero, add_zero] using hi
    · change (g : ℕ) * i + ((g : ℕ) * j + r.val) = (g : ℕ) * (i + j) + r.val
      ring

theorem zero_section_sdiff (A B : Set ℕ) (g : ℕ+) (r : ZMod (g : ℕ)) :
    zeroSection (A \ B) g r = zeroSection A g r \ zeroSection B g r := by
  ext k
  rfl

def SparseResiduePacking (D V : Set ℕ) (g : ℕ+) : Prop :=
  ∀ r : ZMod (g : ℕ), SparseEscapePacking (zeroSection D g 0) (zeroSection V g r)

theorem sparse_residue_packing_iff (D V : Set ℕ) (g : ℕ+)
    (hD : ∀ d ∈ D, (g : ℕ) ∣ d) :
    SparseResiduePacking D V g ↔ Negligible ((D + V) \ V) := by
  rw [negligible_iff_zero_sections _ g]
  constructor
  · intro h r
    have hr := (sparse_escape_packing_iff (zeroSection D g 0) (zeroSection V g r)).mp (h r)
    simpa only [zero_section_sdiff, zero_section_sum_of_multiples D V g hD r] using hr
  · intro h r
    apply (sparse_escape_packing_iff (zeroSection D g 0) (zeroSection V g r)).mpr
    simpa only [zero_section_sdiff, zero_section_sum_of_multiples D V g hD r] using h r

end Erdos335.Proposed

end
