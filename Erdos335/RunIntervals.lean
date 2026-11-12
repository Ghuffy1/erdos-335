import Erdos335.Specification

/-!
# Literal clipped-run correspondence

The runs and carries here are the ones in the full proposed statement. Every
literal representation below a block cutoff is represented by a clipped
interval, including representations using singleton runs and initial blocks.
-/

set_option autoImplicit false

open Filter Topology
open scoped Pointwise

namespace Erdos335.Proposed

theorem prefixRun_exists (A B : Set ℕ) (q : ℕ+) {N k : ℕ} (hk : k < N) :
    ∃ I ∈ prefixRuns A B q N, k ∈ Finset.Icc I.1 I.2 := by
  classical
  let candidates := ((Finset.range N).product (Finset.range N)).filter
    (fun I => I.1 ≤ k ∧ k ≤ I.2 ∧
      ∀ j ∈ Finset.Icc I.1 I.2, pairedMask A B q j = pairedMask A B q k)
  have hkk : (k, k) ∈ candidates := by
    apply Finset.mem_filter.mpr
    refine ⟨by simp [hk], le_rfl, le_rfl, ?_⟩
    intro j hj
    change j ∈ Finset.Icc k k at hj
    have hjk : j = k := le_antisymm (Finset.mem_Icc.mp hj).2 (Finset.mem_Icc.mp hj).1
    rw [hjk]
  obtain ⟨I, hI, hmax⟩ := Finset.exists_max_image candidates
    (fun J => J.2 - J.1) ⟨(k, k), hkk⟩
  obtain ⟨hIN, hIk, hkI, hconstant⟩ := Finset.mem_filter.mp hI
  obtain ⟨hloN, hhiN⟩ := Finset.mem_product.mp hIN
  have hlo : I.1 < N := Finset.mem_range.mp hloN
  have hhi : I.2 < N := Finset.mem_range.mp hhiN
  have hhead : pairedMask A B q I.1 = pairedMask A B q k :=
    hconstant I.1 (Finset.mem_Icc.mpr ⟨le_rfl, hIk.trans hkI⟩)
  have hleft : I.1 = 0 ∨ pairedMask A B q (I.1 - 1) ≠ pairedMask A B q I.1 := by
    by_cases hz : I.1 = 0
    · exact Or.inl hz
    · right
      intro heq
      have hprev : (I.1 - 1, I.2) ∈ candidates := by
        apply Finset.mem_filter.mpr
        refine ⟨Finset.mem_product.mpr ⟨Finset.mem_range.mpr (by omega), hhiN⟩,
          by omega, hkI, ?_⟩
        intro j hj
        obtain ⟨hjl, hjr⟩ := Finset.mem_Icc.mp hj
        by_cases hjprev : j = I.1 - 1
        · simpa only [hjprev] using heq.trans hhead
        · exact hconstant j (Finset.mem_Icc.mpr ⟨by omega, hjr⟩)
      have hbound := hmax (I.1 - 1, I.2) hprev
      dsimp at hbound
      omega
  have hright : I.2 + 1 = N ∨
      pairedMask A B q (I.2 + 1) ≠ pairedMask A B q I.1 := by
    by_cases hz : I.2 + 1 = N
    · exact Or.inl hz
    · right
      intro heq
      have hnext : (I.1, I.2 + 1) ∈ candidates := by
        apply Finset.mem_filter.mpr
        refine ⟨Finset.mem_product.mpr ⟨hloN, Finset.mem_range.mpr (by omega)⟩,
          hIk, by omega, ?_⟩
        intro j hj
        obtain ⟨hjl, hjr⟩ := Finset.mem_Icc.mp hj
        by_cases hjnext : j = I.2 + 1
        · simpa only [hjnext] using heq.trans hhead
        · exact hconstant j (Finset.mem_Icc.mpr ⟨hjl, by omega⟩)
      have hbound := hmax (I.1, I.2 + 1) hnext
      dsimp at hbound
      omega
  refine ⟨I, Finset.mem_filter.mpr ⟨hIN, ?_⟩, Finset.mem_Icc.mpr ⟨hIk, hkI⟩⟩
  refine ⟨hIk.trans hkI, hhi, ?_, hleft, hright⟩
  intro j hj
  exact (hconstant j hj).trans hhead.symm

theorem prefixRun_constant {A B : Set ℕ} {q : ℕ+} {N : ℕ} {I : ℕ × ℕ}
    (hI : I ∈ prefixRuns A B q N) {k : ℕ} (hk : k ∈ Finset.Icc I.1 I.2) :
    pairedMask A B q k = pairedMask A B q I.1 := by
  classical
  exact (Finset.mem_filter.mp hI).2.2.2.1 k hk

theorem prefixRun_bounds {A B : Set ℕ} {q : ℕ+} {N : ℕ} {I : ℕ × ℕ}
    (hI : I ∈ prefixRuns A B q N) : I.1 ≤ I.2 ∧ I.2 < N := by
  classical
  exact ⟨(Finset.mem_filter.mp hI).2.1, (Finset.mem_filter.mp hI).2.2.1⟩

theorem prefixRun_maskA {A B : Set ℕ} {q : ℕ+} {N : ℕ} {I : ℕ × ℕ}
    (hI : I ∈ prefixRuns A B q N) {k : ℕ} (hk : k ∈ Finset.Icc I.1 I.2) :
    mask A q k = mask A q I.1 :=
  congrArg Prod.fst (prefixRun_constant hI hk)

theorem prefixRun_maskB {A B : Set ℕ} {q : ℕ+} {N : ℕ} {I : ℕ × ℕ}
    (hI : I ∈ prefixRuns A B q N) {k : ℕ} (hk : k ∈ Finset.Icc I.1 I.2) :
    mask B q k = mask B q I.1 :=
  congrArg Prod.snd (prefixRun_constant hI hk)

theorem prefixRun_outputMask {A B : Set ℕ} {q : ℕ+} {N : ℕ} {I : ℕ × ℕ}
    (hI : I ∈ prefixRuns A B q N) {k : ℕ} (hk : k ∈ Finset.Icc I.1 I.2) :
    outputMask A B q k = outputMask A B q I.1 := by
  simp only [outputMask, prefixRun_maskA hI hk, prefixRun_maskB hI hk]

@[simp] theorem mem_mask {A : Set ℕ} {q : ℕ+} {k : ℕ} {r : ZMod (q : ℕ)} :
    r ∈ mask A q k ↔ (q : ℕ) * k + r.val ∈ A := by
  classical
  simp [mask]

theorem block_value_add (q : ℕ+) (r t : ZMod (q : ℕ)) (i j : ℕ) :
    ((q : ℕ) * i + r.val) + ((q : ℕ) * j + t.val) =
      (q : ℕ) * (i + j + carry q r t) + (r + t).val := by
  have h := Nat.mod_add_div (r.val + t.val) (q : ℕ)
  rw [ZMod.val_add]
  dsimp [carry]
  nlinarith

theorem mem_clippedInterval_iff (q : ℕ+) (I J K : ℕ × ℕ)
    (r t : ZMod (q : ℕ)) (k : ℕ) (hI : I.1 ≤ I.2) (hJ : J.1 ≤ J.2) :
    (k : ℤ) ∈ IntervalPacking.points (clippedInterval q I J K r t) ↔
      k ∈ Finset.Icc K.1 K.2 ∧
        ∃ i ∈ Finset.Icc I.1 I.2, ∃ j ∈ Finset.Icc J.1 J.2,
          i + j + carry q r t = k := by
  classical
  simp only [IntervalPacking.points, clippedInterval, Finset.mem_Icc,
    max_le_iff, le_min_iff]
  constructor
  · rintro ⟨⟨hlo, hkl⟩, hhi, hkr⟩
    have hsum : (k : ℤ) - carry q r t ∈
        Finset.Icc ((I.1 : ℤ) + J.1) ((I.2 : ℤ) + J.2) := by
      simp only [Finset.mem_Icc]
      constructor <;> omega
    obtain ⟨i, hi, j, hj, hsum⟩ :=
      (IntervalPacking.mem_sum_interval_iff I.1 I.2 J.1 J.2
        ((k : ℤ) - carry q r t) (by exact_mod_cast hI) (by exact_mod_cast hJ)).mpr hsum
    simp only [Finset.mem_Icc] at hi hj
    refine ⟨⟨by omega, by omega⟩, i.toNat, ⟨by omega, by omega⟩,
      j.toNat, ⟨by omega, by omega⟩, ?_⟩
    omega
  · rintro ⟨⟨hkl, hkr⟩, i, ⟨hil, hir⟩, j, ⟨hjl, hjr⟩, rfl⟩
    constructor
    · constructor <;> omega
    · constructor <;> omega

theorem mem_covered_escapingIntervals_iff (A B : Set ℕ) (q : ℕ+)
    (N k : ℕ) (w : ZMod (q : ℕ)) :
    (k : ℤ) ∈ IntervalPacking.covered (escapingIntervals A B q N w) ↔
      k < N ∧ (q : ℕ) * k + w.val ∈ A + B ∧ w ∉ outputMask A B q k := by
  classical
  constructor
  · intro hk
    obtain ⟨L, hL, hkL⟩ := Finset.mem_biUnion.mp hk
    obtain ⟨I, hI, hL⟩ := Finset.mem_biUnion.mp hL
    obtain ⟨J, hJ, hL⟩ := Finset.mem_biUnion.mp hL
    obtain ⟨K, hK, hL⟩ := Finset.mem_biUnion.mp hL
    obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp hL
    obtain ⟨hp, hw, hmissing⟩ := Finset.mem_filter.mp hp
    obtain ⟨hr, ht⟩ := Finset.mem_product.mp hp
    obtain ⟨hkK, i, hi, j, hj, hsum⟩ :=
      (mem_clippedInterval_iff q I J K p.1 p.2 k
        (prefixRun_bounds hI).1 (prefixRun_bounds hJ).1).mp hkL
    have hki : k < N := (Finset.mem_Icc.mp hkK).2.trans_lt (prefixRun_bounds hK).2
    have ha : (q : ℕ) * i + p.1.val ∈ A := by
      apply mem_mask.mp
      rw [prefixRun_maskA hI hi]
      exact hr
    have hb : (q : ℕ) * j + p.2.val ∈ B := by
      apply mem_mask.mp
      rw [prefixRun_maskB hJ hj]
      exact ht
    refine ⟨hki, ?_, ?_⟩
    · refine ⟨(q : ℕ) * i + p.1.val, ha, (q : ℕ) * j + p.2.val, hb, ?_⟩
      simpa only [hsum, hw] using block_value_add q p.1 p.2 i j
    · rw [prefixRun_outputMask hK hkK]
      exact hmissing
  · rintro ⟨hkN, hc, hmissing⟩
    obtain ⟨a, ha, b, hb, hab⟩ := hc
    change a + b = (q : ℕ) * k + w.val at hab
    let i := a / (q : ℕ)
    let j := b / (q : ℕ)
    let r : ZMod (q : ℕ) := a
    let t : ZMod (q : ℕ) := b
    have har : (q : ℕ) * i + r.val = a := by
      simpa only [i, r, ZMod.val_natCast, Nat.add_comm] using Nat.mod_add_div a (q : ℕ)
    have hbt : (q : ℕ) * j + t.val = b := by
      simpa only [j, t, ZMod.val_natCast, Nat.add_comm] using Nat.mod_add_div b (q : ℕ)
    have hrw : r + t = w := by
      change (a : ZMod (q : ℕ)) + (b : ZMod (q : ℕ)) = w
      rw [← Nat.cast_add, hab]
      simp
    have hindices : i + j + carry q r t = k := by
      have hv := block_value_add q r t i j
      rw [har, hbt, hrw, hab] at hv
      have hmul : (q : ℕ) * (i + j + carry q r t) = (q : ℕ) * k := by omega
      exact Nat.eq_of_mul_eq_mul_left q.pos hmul
    have hik : i ≤ k := by
      rw [← hindices]
      exact (Nat.le_add_right i j).trans (Nat.le_add_right (i + j) (carry q r t))
    have hjk : j ≤ k := by
      rw [← hindices]
      exact (Nat.le_add_left j i).trans (Nat.le_add_right (i + j) (carry q r t))
    have hiN : i < N := hik.trans_lt hkN
    have hjN : j < N := hjk.trans_lt hkN
    obtain ⟨I, hI, hiI⟩ := prefixRun_exists A B q hiN
    obtain ⟨J, hJ, hjJ⟩ := prefixRun_exists A B q hjN
    obtain ⟨K, hK, hkK⟩ := prefixRun_exists A B q hkN
    have hr : r ∈ mask A q I.1 := by
      rw [← prefixRun_maskA hI hiI]
      exact mem_mask.mpr (har ▸ ha)
    have ht : t ∈ mask B q J.1 := by
      rw [← prefixRun_maskB hJ hjJ]
      exact mem_mask.mpr (hbt ▸ hb)
    have hm : w ∉ outputMask A B q K.1 := by
      rw [← prefixRun_outputMask hK hkK]
      exact hmissing
    refine Finset.mem_biUnion.mpr ⟨clippedInterval q I J K r t, ?_, ?_⟩
    · refine Finset.mem_biUnion.mpr ⟨I, hI, Finset.mem_biUnion.mpr ⟨J, hJ,
        Finset.mem_biUnion.mpr ⟨K, hK, ?_⟩⟩⟩
      exact Finset.mem_image.mpr ⟨(r, t),
        Finset.mem_filter.mpr ⟨Finset.mem_product.mpr ⟨hr, ht⟩, hrw, hm⟩, rfl⟩
    · exact (mem_clippedInterval_iff q I J K r t k
        (prefixRun_bounds hI).1 (prefixRun_bounds hJ).1).mpr ⟨hkK, i, hiI, j, hjJ, hindices⟩

theorem covered_escapingIntervals_bounds {A B : Set ℕ} {q : ℕ+}
    {N : ℕ} {w : ZMod (q : ℕ)} {z : ℤ}
    (hz : z ∈ IntervalPacking.covered (escapingIntervals A B q N w)) :
    0 ≤ z ∧ z < N := by
  classical
  obtain ⟨L, hL, hzL⟩ := Finset.mem_biUnion.mp hz
  obtain ⟨I, hI, hL⟩ := Finset.mem_biUnion.mp hL
  obtain ⟨J, hJ, hL⟩ := Finset.mem_biUnion.mp hL
  obtain ⟨K, hK, hL⟩ := Finset.mem_biUnion.mp hL
  obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp hL
  have hKbound := prefixRun_bounds hK
  simp only [IntervalPacking.points, clippedInterval, Finset.mem_Icc,
    max_le_iff, le_min_iff] at hzL
  constructor <;> omega

noncomputable def escapingIndices (A B : Set ℕ) (q : ℕ+) (N : ℕ)
    (w : ZMod (q : ℕ)) : Finset ℕ := by
  classical
  exact (Finset.range N).filter (fun k =>
    (q : ℕ) * k + w.val ∈ A + B ∧ w ∉ outputMask A B q k)

theorem covered_escapingIntervals_eq_image (A B : Set ℕ) (q : ℕ+)
    (N : ℕ) (w : ZMod (q : ℕ)) :
    IntervalPacking.covered (escapingIntervals A B q N w) =
      (escapingIndices A B q N w).image (fun k : ℕ => (k : ℤ)) := by
  classical
  ext z
  constructor
  · intro hz
    have hbound := covered_escapingIntervals_bounds hz
    have hzcast : (z.toNat : ℤ) = z := Int.toNat_of_nonneg hbound.1
    rw [← hzcast] at hz
    have hnat := (mem_covered_escapingIntervals_iff A B q N z.toNat w).mp hz
    apply Finset.mem_image.mpr
    refine ⟨z.toNat, ?_, hzcast⟩
    simpa only [escapingIndices, Finset.mem_filter, Finset.mem_range] using hnat
  · intro hz
    obtain ⟨k, hk, rfl⟩ := Finset.mem_image.mp hz
    apply (mem_covered_escapingIntervals_iff A B q N k w).mpr
    simpa only [escapingIndices, Finset.mem_filter, Finset.mem_range] using hk

theorem card_escapingIndices (A B : Set ℕ) (q : ℕ+) (N : ℕ) (w : ZMod (q : ℕ)) :
    (escapingIndices A B q N w).card =
      (IntervalPacking.covered (escapingIntervals A B q N w)).card := by
  classical
  rw [covered_escapingIntervals_eq_image]
  exact (Finset.card_image_of_injective _ Int.ofNat_injective).symm

theorem escapingPackingVanishes_iff (A B : Set ℕ) (q : ℕ+) :
    EscapingPackingVanishes A B q ↔
      ∀ w : ZMod (q : ℕ), Tendsto
        (fun N => ((escapingIndices A B q N w).card : ℝ) / N) atTop (𝓝 0) := by
  constructor
  · intro h w
    have hw := (IntervalPacking.packing_vanishes_iff_covered_vanishes
      (fun N => escapingIntervals A B q N w)).mp (h w)
    simpa only [card_escapingIndices] using hw
  · intro h w
    apply (IntervalPacking.packing_vanishes_iff_covered_vanishes
      (fun N => escapingIntervals A B q N w)).mpr
    simpa only [card_escapingIndices] using h w

end Erdos335.Proposed
