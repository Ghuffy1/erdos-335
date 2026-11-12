import Erdos335.NearbyPrefixAverages

/-!
# Agreement of profiles at the two selected window lengths
-/

set_option autoImplicit false

open Filter Topology

namespace Erdos335.IntermediateScale

theorem selected_length_excess_tendsto_zero (H : ℕ → ℕ) (q : ℕ → ℕ+)
    (hH : ∀ s, 0 < H s) (hHq : ∀ s, H s ≤ (q s : ℕ))
    (hgap : Tendsto (fun s => (((q s : ℕ) - H s : ℕ) : ℝ) / (q s : ℕ)) atTop (𝓝 0)) :
    Tendsto (fun s => (((q s : ℕ) - H s : ℕ) : ℝ) / H s) atTop (𝓝 0) := by
  have hsmall : ∀ᶠ s in atTop, (q s : ℕ) ≤ 2 * H s := by
    filter_upwards [hgap.eventually (gt_mem_nhds (by norm_num : (0 : ℝ) < 1 / 2))] with s hs
    rw [Nat.cast_sub (hHq s)] at hs
    have hqr : (0 : ℝ) < (q s : ℕ) := by positivity
    have ht := (div_lt_iff₀ hqr).mp hs
    have hr : ((q s : ℕ) : ℝ) ≤ 2 * H s := by linarith
    exact_mod_cast hr
  have hlimit : Tendsto (fun s => 2 * ((((q s : ℕ) - H s : ℕ) : ℝ) / (q s : ℕ)))
      atTop (𝓝 0) := by simpa only [mul_zero] using hgap.const_mul 2
  apply squeeze_zero' (Eventually.of_forall fun s => by positivity) ?_ hlimit
  filter_upwards [hsmall] with s hs
  have hHr : (0 : ℝ) < H s := by exact_mod_cast hH s
  have hqr : (0 : ℝ) < (q s : ℕ) := by positivity
  have hfactor : ((q s : ℕ) : ℝ) / H s ≤ 2 := by
    apply (div_le_iff₀ hHr).mpr
    exact_mod_cast hs
  have hprod := mul_le_mul_of_nonneg_left hfactor
    (show (0 : ℝ) ≤ (((q s : ℕ) - H s : ℕ) : ℝ) / (q s : ℕ) by positivity)
  have heq : (((q s : ℕ) - H s : ℕ) : ℝ) / (q s : ℕ) * (((q s : ℕ) : ℝ) / H s) =
      (((q s : ℕ) - H s : ℕ) : ℝ) / H s := by field_simp
  rw [heq] at hprod
  simpa only [mul_comm] using hprod

theorem selected_lengths_tendsto_near (H : ℕ → ℕ) (p q : ℕ → ℕ+)
    (hH : ∀ s, 0 < H s) (hHp : ∀ s, H s ≤ (p s : ℕ)) (hHq : ∀ s, H s ≤ (q s : ℕ))
    (hp : Tendsto (fun s => (((p s : ℕ) - H s : ℕ) : ℝ) / (p s : ℕ)) atTop (𝓝 0))
    (hq : Tendsto (fun s => (((q s : ℕ) - H s : ℕ) : ℝ) / (q s : ℕ)) atTop (𝓝 0)) :
    Tendsto (fun s => |((p s : ℕ) : ℝ) - (q s : ℕ)| / H s) atTop (𝓝 0) := by
  have ht := (selected_length_excess_tendsto_zero H p hH hHp hp).add
    (selected_length_excess_tendsto_zero H q hH hHq hq)
  simp only [add_zero] at ht
  apply squeeze_zero (fun s => by positivity) (fun s => ?_) ht
  rw [← add_div]
  apply div_le_div_of_nonneg_right _ (by positivity)
  rw [Nat.cast_sub (hHp s), Nat.cast_sub (hHq s)]
  have hpR : (H s : ℝ) ≤ (p s : ℕ) := by exact_mod_cast hHp s
  have hqR : (H s : ℝ) ≤ (q s : ℕ) := by exact_mod_cast hHq s
  rw [abs_le]
  constructor <;> linarith

theorem selected_cyclic_profiles_agree (A : ℕ → Set ℕ) (start H : ℕ → ℕ) (p q : ℕ → ℕ+)
    (hH : ∀ s, 0 < H s) (hHp : ∀ s, H s ≤ (p s : ℕ)) (hHq : ∀ s, H s ≤ (q s : ℕ))
    (hp : Tendsto (fun s => (((p s : ℕ) - H s : ℕ) : ℝ) / (p s : ℕ)) atTop (𝓝 0))
    (hq : Tendsto (fun s => (((q s : ℕ) - H s : ℕ) : ℝ) / (q s : ℕ)) atTop (𝓝 0)) :
    Tendsto (fun s => ((cyclicWindow (A s) (start s) (p s : ℕ)).card : ℝ) / (p s : ℕ) -
      ((cyclicWindow (A s) (start s) (q s : ℕ)).card : ℝ) / (q s : ℕ)) atTop (𝓝 0) :=
  cyclic_window_length_comparison A start H p q hH hHp hHq
    (selected_lengths_tendsto_near H p q hH hHp hHq hp hq)

end Erdos335.IntermediateScale
