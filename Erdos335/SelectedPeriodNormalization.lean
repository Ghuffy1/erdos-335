import Erdos335.SelectedConvolutionWindows

/-!
# Positive selected periods and common interior starts
-/

set_option autoImplicit false

open Filter Topology

namespace Erdos335.IntermediateScale

theorem exists_normalized_selected_period (N H n : ℕ → ℕ)
    (hHpos : ∀ s, 0 < H s) (hH : Tendsto H atTop atTop)
    (hinside : ∀ᶠ s in atTop, n s + 6 * H s ≤ N s)
    (Q : ℕ → ℕ → ℕ) (ε : ℕ → ℝ)
    (hε : ∀ s, 0 ≤ ε s) (hεlim : Tendsto ε atTop (𝓝 0))
    (hQ : ∀ᶠ s in atTop, ∀ t, H s ≤ Q s t ∧ (Q s t : ℝ) ≤ (1 + ε s) * H s)
    (hdiv : ∀ M : ℕ, 0 < M → ∀ᶠ s in atTop, ∀ t, M ∣ Q s t) :
    ∃ q : ℕ → ℕ+,
      (∀ s, H s ≤ (q s : ℕ)) ∧ Tendsto (fun s => (q s : ℕ)) atTop atTop ∧
      Tendsto (fun s => (((q s : ℕ) - H s : ℕ) : ℝ) / (q s : ℕ)) atTop (𝓝 0) ∧
      (∀ M : ℕ, 0 < M → ∀ᶠ s in atTop, M ∣ (q s : ℕ)) ∧
      (∀ᶠ s in atTop, n s + 3 * H s + (q s : ℕ) ≤ N s) ∧
      (∀ᶠ s in atTop, (q s : ℕ) = Q s (n s) ∧ 2 * (q s : ℕ) ≤ 3 * H s) := by
  classical
  let q : ℕ → ℕ+ := fun s => ⟨max (H s) (Q s (n s)), (hHpos s).trans_le (le_max_left _ _)⟩
  have hqH (s : ℕ) : H s ≤ (q s : ℕ) := le_max_left _ _
  have heq : ∀ᶠ s in atTop, (q s : ℕ) = Q s (n s) := by
    filter_upwards [hQ] with s hs
    exact max_eq_right (hs (n s)).1
  have hhalf : ∀ᶠ s in atTop, 2 * (q s : ℕ) ≤ 3 * H s := by
    filter_upwards [hQ, heq,
      hεlim.eventually (gt_mem_nhds (by norm_num : (0 : ℝ) < 1 / 2))] with s hs hqs heps
    have hb := (hs (n s)).2
    rw [← hqs] at hb
    have hHr : (0 : ℝ) ≤ H s := by positivity
    have hreal : (2 : ℝ) * (q s : ℕ) ≤ 3 * H s := by nlinarith
    exact_mod_cast hreal
  have hqtop : Tendsto (fun s => (q s : ℕ)) atTop atTop := by
    apply tendsto_atTop.mpr
    intro b
    filter_upwards [hH.eventually (eventually_ge_atTop b)] with s hs
    exact hs.trans (hqH s)
  have hqgap : Tendsto (fun s => (((q s : ℕ) - H s : ℕ) : ℝ) / (q s : ℕ)) atTop (𝓝 0) := by
    apply squeeze_zero' (Eventually.of_forall fun s => by positivity) ?_ hεlim
    filter_upwards [heq, hQ] with s hqs hs
    rw [Nat.cast_sub (hqH s)]
    apply (div_le_iff₀ (show (0 : ℝ) < (q s : ℕ) by exact_mod_cast (q s).pos)).mpr
    have hb := (hs (n s)).2
    rw [← hqs] at hb
    have hlo : (H s : ℝ) ≤ (q s : ℕ) := by exact_mod_cast hqH s
    nlinarith [mul_nonneg (hε s) (sub_nonneg.mpr hlo)]
  refine ⟨q, hqH, hqtop, hqgap, ?_, ?_, heq.and hhalf⟩
  · intro M hM
    filter_upwards [heq, hdiv M hM] with s hqs hs
    simpa only [hqs] using hs (n s)
  · filter_upwards [hinside, hhalf] with s hs hqs
    omega

end Erdos335.IntermediateScale
