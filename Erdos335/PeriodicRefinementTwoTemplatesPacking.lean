import Erdos335.FiniteSections
import Erdos335.PackingDensity

/-!
# Literal fringe-sum intervals outside a fixed periodic template

Private proof development. Verification status is recorded separately.
The source masks retain every literal fringe element. The carry is the
canonical carry of the two residue representatives.
-/

set_option autoImplicit false

open Filter Set Topology
open scoped Pointwise

noncomputable section
attribute [local instance] Classical.propDecidable

namespace Erdos335.Proposed

noncomputable def residueSumIntervals (E F : Set ℕ) (q : ℕ+) (N : ℕ)
    (w : ZMod (q : ℕ)) : Finset IntervalPacking.Interval := by
  classical
  let runs := prefixRuns E F q N
  exact runs.biUnion fun I => runs.biUnion fun J =>
    (((mask E q I.1).product (mask F q J.1)).filter
      (fun p => p.1 + p.2 = w)).image
        (fun p => clippedInterval q I J (0, N - 1) p.1 p.2)

def ResidueSumPacking (E F : Set ℕ) (q : ℕ+) (W : Finset (ZMod (q : ℕ))) : Prop :=
  ∀ w ∉ W, Tendsto (fun N =>
    (IntervalPacking.packingSize (residueSumIntervals E F q N w) : ℝ) / N)
      atTop (𝓝 0)

theorem mem_residue_sum_intervals_iff (E F : Set ℕ) (q : ℕ+) (N k : ℕ)
    (w : ZMod (q : ℕ)) :
    (k : ℤ) ∈ IntervalPacking.covered (residueSumIntervals E F q N w) ↔
      k < N ∧ (q : ℕ) * k + w.val ∈ E + F := by
  classical
  constructor
  · intro hk
    obtain ⟨L, hL, hkL⟩ := Finset.mem_biUnion.mp hk
    unfold residueSumIntervals at hL
    obtain ⟨I, hI, hL⟩ := Finset.mem_biUnion.mp hL
    obtain ⟨J, hJ, hL⟩ := Finset.mem_biUnion.mp hL
    obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp hL
    obtain ⟨hp, hw⟩ := Finset.mem_filter.mp hp
    obtain ⟨hr, ht⟩ := Finset.mem_product.mp hp
    have hN : 0 < N := by
      have hb := prefixRun_bounds hI
      omega
    obtain ⟨hkK, i, hi, j, hj, hsum⟩ :=
      (mem_clippedInterval_iff q I J (0, N - 1) p.1 p.2 k
        (prefixRun_bounds hI).1 (prefixRun_bounds hJ).1).mp hkL
    have hkN : k < N := by
      have hb := Finset.mem_Icc.mp hkK
      omega
    have hiE : (q : ℕ) * i + p.1.val ∈ E := by
      apply mem_mask.mp
      rw [prefixRun_maskA hI hi]
      exact hr
    have hjF : (q : ℕ) * j + p.2.val ∈ F := by
      apply mem_mask.mp
      rw [prefixRun_maskB hJ hj]
      exact ht
    refine ⟨hkN, ⟨(q : ℕ) * i + p.1.val, hiE,
      (q : ℕ) * j + p.2.val, hjF, ?_⟩⟩
    simpa only [hsum, hw] using block_value_add q p.1 p.2 i j
  · rintro ⟨hkN, a, ha, b, hb, hab⟩
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
    have hiN : i < N := lt_of_le_of_lt
      ((Nat.le_add_right i j).trans ((Nat.le_add_right (i + j) (carry q r t)).trans_eq hindices)) hkN
    have hjN : j < N := lt_of_le_of_lt
      ((Nat.le_add_left j i).trans ((Nat.le_add_right (i + j) (carry q r t)).trans_eq hindices)) hkN
    obtain ⟨I, hI, hiI⟩ := prefixRun_exists E F q hiN
    obtain ⟨J, hJ, hjJ⟩ := prefixRun_exists E F q hjN
    have hr : r ∈ mask E q I.1 := by
      rw [← prefixRun_maskA hI hiI]
      exact mem_mask.mpr (har ▸ ha)
    have ht : t ∈ mask F q J.1 := by
      rw [← prefixRun_maskB hJ hjJ]
      exact mem_mask.mpr (hbt ▸ hb)
    apply Finset.mem_biUnion.mpr
    refine ⟨clippedInterval q I J (0, N - 1) r t, ?_, ?_⟩
    · unfold residueSumIntervals
      apply Finset.mem_biUnion.mpr
      refine ⟨I, hI, Finset.mem_biUnion.mpr ⟨J, hJ, ?_⟩⟩
      exact Finset.mem_image.mpr ⟨(r, t),
        Finset.mem_filter.mpr ⟨Finset.mem_product.mpr ⟨hr, ht⟩, hrw⟩, rfl⟩
    · apply (mem_clippedInterval_iff q I J (0, N - 1) r t k
        (prefixRun_bounds hI).1 (prefixRun_bounds hJ).1).mpr
      exact ⟨Finset.mem_Icc.mpr (by omega), i, hiI, j, hjJ, hindices⟩

theorem residue_sum_intervals_bounds (E F : Set ℕ) (q : ℕ+) (N : ℕ)
    (w : ZMod (q : ℕ)) (z : ℤ)
    (hz : z ∈ IntervalPacking.covered (residueSumIntervals E F q N w)) :
    0 ≤ z ∧ z < N := by
  classical
  obtain ⟨L, hL, hzL⟩ := Finset.mem_biUnion.mp hz
  unfold residueSumIntervals at hL
  obtain ⟨I, hI, hL⟩ := Finset.mem_biUnion.mp hL
  obtain ⟨J, hJ, hL⟩ := Finset.mem_biUnion.mp hL
  obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp hL
  have hIbound := prefixRun_bounds hI
  simp only [IntervalPacking.points, clippedInterval, Finset.mem_Icc,
    max_le_iff, le_min_iff] at hzL
  constructor <;> omega

theorem residue_sum_intervals_eq_image (E F : Set ℕ) (q : ℕ+) (N : ℕ)
    (w : ZMod (q : ℕ)) :
    IntervalPacking.covered (residueSumIntervals E F q N w) =
      (((Finset.range N).filter (fun k => k ∈ zeroSection (E + F) q w)).image
        (fun k : ℕ => (k : ℤ))) := by
  classical
  ext z
  constructor
  · intro hz
    have hbound := residue_sum_intervals_bounds E F q N w z hz
    have hzcast : (z.toNat : ℤ) = z := Int.toNat_of_nonneg hbound.1
    rw [← hzcast] at hz
    have hnat := (mem_residue_sum_intervals_iff E F q N z.toNat w).mp hz
    apply Finset.mem_image.mpr
    refine ⟨z.toNat, ?_, hzcast⟩
    simpa only [Finset.mem_filter, Finset.mem_range, zeroSection, Set.mem_setOf_eq] using hnat
  · intro hz
    obtain ⟨k, hk, rfl⟩ := Finset.mem_image.mp hz
    apply (mem_residue_sum_intervals_iff E F q N k w).mpr
    simpa only [Finset.mem_filter, Finset.mem_range, zeroSection, Set.mem_setOf_eq] using hk

theorem residue_sum_intervals_card (E F : Set ℕ) (q : ℕ+) (N : ℕ)
    (w : ZMod (q : ℕ)) :
    (IntervalPacking.covered (residueSumIntervals E F q N w)).card =
      prefixCount (zeroSection (E + F) q w) N := by
  classical
  rw [residue_sum_intervals_eq_image]
  exact Finset.card_image_of_injective _ Int.ofNat_injective

theorem residue_sum_packing_at_iff (E F : Set ℕ) (q : ℕ+) (w : ZMod (q : ℕ)) :
    Tendsto (fun N =>
      (IntervalPacking.packingSize (residueSumIntervals E F q N w) : ℝ) / N)
        atTop (𝓝 0) ↔ Negligible (zeroSection (E + F) q w) := by
  change Tendsto (fun N =>
    (IntervalPacking.packingSize (residueSumIntervals E F q N w) : ℝ) / N)
      atTop (𝓝 0) ↔ HasDensity (zeroSection (E + F) q w) 0
  rw [hasDensity_iff_prefixCount]
  simpa only [residue_sum_intervals_card] using
    IntervalPacking.packing_vanishes_iff_covered_vanishes
      (fun N => residueSumIntervals E F q N w)

theorem residue_sum_packing_comm (E F : Set ℕ) (q : ℕ+)
    (W : Finset (ZMod (q : ℕ))) :
    ResidueSumPacking E F q W ↔ ResidueSumPacking F E q W := by
  constructor
  · intro h w hw
    apply (residue_sum_packing_at_iff F E q w).mpr
    simpa only [add_comm E F] using (residue_sum_packing_at_iff E F q w).mp (h w hw)
  · intro h w hw
    apply (residue_sum_packing_at_iff E F q w).mpr
    simpa only [add_comm F E] using (residue_sum_packing_at_iff F E q w).mp (h w hw)

theorem residue_sum_packing_iff (E F : Set ℕ) (q : ℕ+)
    (W : Finset (ZMod (q : ℕ))) (hE : E ⊆ Ioi 0) (hF : F ⊆ Ioi 0) :
    ResidueSumPacking E F q W ↔ Negligible ((E + F) \ periodicSet W) := by
  classical
  constructor
  · intro h
    let R : Finset (ZMod (q : ℕ)) := Finset.univ \ W
    have hsections : ∀ w ∈ R, Negligible (zeroSection (E + F) q w) := by
      intro w hw
      exact (residue_sum_packing_at_iff E F q w).mp (h w (Finset.mem_sdiff.mp hw).2)
    have hzero := negligible_finiteUnion R (fun w => zeroSection (E + F) q w) hsections
    apply (hzero.liftBlocks q).mono
    rintro n ⟨hn, hout⟩
    have hw : (n : ZMod (q : ℕ)) ∉ W := by
      intro hmem
      exact hout ⟨sumset_positive hE hF hn, hmem⟩
    refine ⟨(n : ZMod (q : ℕ)), Finset.mem_sdiff.mpr ⟨Finset.mem_univ _, hw⟩, ?_⟩
    change (q : ℕ) * (n / (q : ℕ)) + (n : ZMod (q : ℕ)).val ∈ E + F
    have hdecomp : (q : ℕ) * (n / (q : ℕ)) + (n : ZMod (q : ℕ)).val = n := by
      simpa only [ZMod.val_natCast, Nat.add_comm] using Nat.mod_add_div n (q : ℕ)
    simpa only [hdecomp] using hn
  · intro h w hw
    apply (residue_sum_packing_at_iff E F q w).mpr
    apply (h.arithmetic_preimage q w.val_lt).mono
    intro k hk
    refine ⟨hk, ?_⟩
    intro hmem
    apply hw
    simpa only [Nat.cast_add, Nat.cast_mul, ZMod.natCast_self, zero_mul,
      zero_add, ZMod.natCast_zmod_val] using hmem.2

end Erdos335.Proposed

end
