import Erdos335.FrequencyThresholdProfiles

/-!
# Bounding intermediate frequency bands by two threshold profiles
-/

set_option autoImplicit false

open Filter Topology Finset
open scoped Classical

namespace Erdos335.IntermediateScale

noncomputable def frequencyBandDensity (N W C : ℕ) (v : ℕ → ℝ) : ℝ :=
  (((range N).filter (fun n => 1 / ((C : ℝ) * W) < |v n| ∧ |v n| < (C : ℝ) / W)).card : ℝ) / N

theorem frequencyBandDensity_le_threshold_difference (N A B W C : ℕ)
    (hW : 0 < W) (hC : 0 < C) (hAB : A ≤ B)
    (hsmall : A * C ≤ W) (hlarge : C * W ≤ B) (v : ℕ → ℝ) :
    frequencyBandDensity N W C v ≤
      frequencyThresholdAverage N A v - frequencyThresholdAverage N B v := by
  let S := (range N).filter (fun n => (A : ℝ) * |v n| ≤ 1)
  let T := (range N).filter (fun n => (B : ℝ) * |v n| ≤ 1)
  let E := (range N).filter (fun n => 1 / ((C : ℝ) * W) < |v n| ∧ |v n| < (C : ℝ) / W)
  have hWr : (0 : ℝ) < W := by exact_mod_cast hW
  have hCr : (0 : ℝ) < C := by exact_mod_cast hC
  have hsmallR : (A : ℝ) * C ≤ W := by exact_mod_cast hsmall
  have hlargeR : (C : ℝ) * W ≤ B := by exact_mod_cast hlarge
  have hES : E ⊆ S := by
    intro n hn
    obtain ⟨hn, _hlow, hhigh⟩ := mem_filter.mp hn
    apply mem_filter.mpr ⟨hn, ?_⟩
    calc
      (A : ℝ) * |v n| ≤ A * ((C : ℝ) / W) :=
        mul_le_mul_of_nonneg_left hhigh.le (Nat.cast_nonneg _)
      _ = ((A : ℝ) * C) / W := by ring
      _ ≤ 1 := (div_le_one hWr).mpr hsmallR
  have hTS : T ⊆ S := by
    intro n hn
    obtain ⟨hn, hb⟩ := mem_filter.mp hn
    exact mem_filter.mpr ⟨hn,
      (mul_le_mul_of_nonneg_right (by exact_mod_cast hAB) (abs_nonneg _)).trans hb⟩
  have hET : Disjoint E T := by
    apply disjoint_left.mpr
    intro n hn ht
    have hl := (mem_filter.mp hn).2.1
    have hb := (mem_filter.mp ht).2
    have hm : 1 < |v n| * ((C : ℝ) * W) := (div_lt_iff₀ (mul_pos hCr hWr)).mp hl
    have hbound := mul_le_mul_of_nonneg_left hlargeR (abs_nonneg (v n))
    nlinarith
  have hcardNat : E.card + T.card ≤ S.card := by
    rw [← card_union_of_disjoint hET]
    exact Finset.card_le_card (union_subset hES hTS)
  have hcard : (E.card : ℝ) + T.card ≤ S.card := by exact_mod_cast hcardNat
  have hd := div_le_div_of_nonneg_right hcard (Nat.cast_nonneg N : (0 : ℝ) ≤ N)
  rw [add_div] at hd
  change (E.card : ℝ) / N ≤ (S.card : ℝ) / N - (T.card : ℝ) / N
  linarith

theorem frequencyBandDensity_tendsto_zero (N A B W : ℕ → ℕ) (v : ℕ → ℕ → ℝ)
    (hW : ∀ᶠ s in atTop, 0 < W s) (hB : ∀ s, 0 < B s)
    (hAB : ∀ᶠ s in atTop, A s ≤ B s)
    (hAW : Tendsto (fun s => (A s : ℝ) / W s) atTop (𝓝 0))
    (hWB : Tendsto (fun s => (W s : ℝ) / B s) atTop (𝓝 0))
    (hprofile : Tendsto (fun s => frequencyThresholdAverage (N s) (A s) (v s) -
      frequencyThresholdAverage (N s) (B s) (v s)) atTop (𝓝 0))
    (C : ℕ) (hC : 0 < C) :
    Tendsto (fun s => frequencyBandDensity (N s) (W s) C (v s)) atTop (𝓝 0) := by
  have hsmallLimit : Tendsto (fun s => (C : ℝ) * ((A s : ℝ) / W s)) atTop (𝓝 0) := by
    simpa only [mul_zero] using hAW.const_mul (C : ℝ)
  have hlargeLimit : Tendsto (fun s => (C : ℝ) * ((W s : ℝ) / B s)) atTop (𝓝 0) := by
    simpa only [mul_zero] using hWB.const_mul (C : ℝ)
  have hsmall := hsmallLimit.eventually (eventually_lt_nhds (show (0 : ℝ) < 1 by norm_num))
  have hlarge := hlargeLimit.eventually (eventually_lt_nhds (show (0 : ℝ) < 1 by norm_num))
  apply squeeze_zero' (Eventually.of_forall fun s => by unfold frequencyBandDensity; positivity) ?_ hprofile
  filter_upwards [hW, hAB, hsmall, hlarge] with s hs hABs hsmallS hlargeS
  have hWr : (0 : ℝ) < W s := by exact_mod_cast hs
  have hBr : (0 : ℝ) < B s := by exact_mod_cast hB s
  have hsmallNat : A s * C ≤ W s := by
    have hreal : (A s : ℝ) * C < W s := by
      apply (div_lt_one hWr).mp
      have heq : (C : ℝ) * ((A s : ℝ) / W s) = ((A s : ℝ) * C) / W s := by ring
      simpa only [heq] using hsmallS
    exact_mod_cast hreal.le
  have hlargeNat : C * W s ≤ B s := by
    have hreal : (C : ℝ) * W s < B s := (div_lt_one hBr).mp (by
      simpa only [mul_div_assoc] using hlargeS)
    exact_mod_cast hreal.le
  exact frequencyBandDensity_le_threshold_difference (N s) (A s) (B s) (W s) C hs hC hABs
    hsmallNat hlargeNat (v s)

end Erdos335.IntermediateScale
