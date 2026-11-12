import Erdos335.SelectedConvolutionWindows
import Erdos335.DenseCyclicRemoval
import Erdos335.IntermediateConvolutionPeriods
import Erdos335.PositiveIntermediateScales

/-!
# Constructing density-preserving cyclic models on intermediate scales
-/

set_option autoImplicit false

open Filter Topology Set
open scoped BigOperators Pointwise

namespace Erdos335.IntermediateScale

theorem exists_intermediate_cyclic_models
    (N : ℕ → ℕ) [∀ s, NeZero (N s)]
    (hN : Tendsto N atTop atTop) (hmono : Monotone N)
    (hprev : Tendsto (fun s => (N (s - 1) : ℝ) / N s) atTop (𝓝 0))
    (lower upper : ℕ → ℕ)
    (hlower : Tendsto lower atTop atTop) (hupper : Tendsto upper atTop atTop)
    (hgap : Tendsto (fun s => (upper s : ℝ) / lower s) atTop atTop)
    (hupperN : ∀ᶠ s in atTop, upper s ≤ N s)
    (Aset Bset : Set ℕ) (a b c₀ : ℝ) (hB : HasDensity Bset b)
    (hAerror : Tendsto (fun s => prefixError Aset a (N s) / lower s) atTop (𝓝 0))
    (hCerror : Tendsto (fun s => prefixError (Aset + Bset) c₀ (N s) / lower s) atTop (𝓝 0))
    (U : Ultrafilter ℕ) (hU : (U : Filter ℕ) ≤ atTop) :
    ∃ (τ : ℕ → ℕ) (q : ℕ → ℕ+) (start : ℕ → ℕ)
      (A' B' : ∀ s, Finset (ZMod (q s : ℕ))),
      StrictMono τ ∧ Tendsto (fun s => (q s : ℕ)) atTop atTop ∧
      Tendsto (fun s => ((q s : ℕ) : ℝ) / N (τ s)) atTop (𝓝 0) ∧
      Tendsto (fun s => (lower (τ s) : ℝ) / (q s : ℕ)) atTop (𝓝 0) ∧
      (∀ M : ℕ, 0 < M → ∀ᶠ s in atTop, M ∣ (q s : ℕ)) ∧
      (∀ᶠ s in atTop, start s + (q s : ℕ) ≤ N (τ s)) ∧
      (∀ s, A' s ⊆ cyclicWindow Aset (start s) (q s : ℕ) ∧
        B' s ⊆ cyclicWindow Bset 0 (q s : ℕ)) ∧
      (∀ v ∈ Bset, ∀ᶠ s in atTop, (v : ZMod (q s : ℕ)) ∈ B' s) ∧
      Tendsto (fun s => ((A' s).card : ℝ) / (q s : ℕ)) atTop (𝓝 a) ∧
      Tendsto (fun s => ((B' s).card : ℝ) / (q s : ℕ)) atTop (𝓝 b) ∧
      Tendsto (fun s => ((cyclicWindow (Aset + Bset) (start s) (q s : ℕ)).card : ℝ) / (q s : ℕ))
        atTop (𝓝 c₀) ∧
      Tendsto (fun s => (((A' s + B' s) \ cyclicWindow (Aset + Bset) (start s) (q s : ℕ)).card : ℝ) /
        (q s : ℕ)) atTop (𝓝 0) := by
  classical
  let F : ℕ → ℝ := Aset.indicator (fun _ => 1)
  have hF (n : ℕ) : F n ∈ Icc (0 : ℝ) 1 := by
    by_cases hn : n ∈ Aset <;> simp [F, hn]
  obtain ⟨τ, A, B, w, d, c, α, hτ, hprev', hAB, hA, hlo, hABlim, hhi,
    hd, hc, hw, horth, hmean, happrox, hcontrol⟩ :=
    exists_intermediate_fourier_decomposition N hN hmono hprev lower upper hlower hupper hgap hupperN F hF U hU
  have hBtop := scale_tendsto_atTop_of_smaller A B hA (fun s => (hAB s).2) hABlim
  have hBA := reciprocal_scale_ratio_tendsto_atTop A B (fun s => (hAB s).1) (fun s => (hAB s).2) hABlim
  let H := positiveIntermediateScale A B (1 / 2) 0
  have hHpos : ∀ s, 0 < H s := positiveIntermediateScale_pos A B _ _
  have hHtop : Tendsto H atTop atTop := positiveIntermediateScale_atTop A B hA hBA _ _ (by norm_num)
  have hAH : Tendsto (fun s => (A s : ℝ) / H s) atTop (𝓝 0) :=
    positiveIntermediateScale_lower_ratio A B hA hBA _ _ (by norm_num)
  have hHB : Tendsto (fun s => (H s : ℝ) / B s) atTop (𝓝 0) :=
    positiveIntermediateScale_ambient_ratio A B B hA hBtop hBA
      (Eventually.of_forall fun _ => le_rfl) _ _ (by norm_num) (by norm_num)
  have hNpos (s : ℕ) : 0 < N (τ s) := NeZero.pos _
  have hBN : Tendsto (fun s => (B s : ℝ) / N (τ s)) atTop (𝓝 0) := by
    apply squeeze_zero' (Eventually.of_forall fun s => by positivity) ?_ hhi
    filter_upwards [hτ.tendsto_atTop.eventually hupperN,
      (hupper.comp hτ.tendsto_atTop).eventually (eventually_gt_atTop 0)] with s hs hp
    exact div_le_div_of_nonneg_left (by positivity) (by exact_mod_cast hp) (by exact_mod_cast hs)
  have hHN : Tendsto (fun s => (H s : ℝ) / N (τ s)) atTop (𝓝 0) := by
    have heq (s : ℕ) : (H s : ℝ) / B s * ((B s : ℝ) / N (τ s)) = (H s : ℝ) / N (τ s) := by
      have hb : (B s : ℝ) ≠ 0 := by exact_mod_cast (hAB s).2.ne'
      field_simp
    simpa only [heq, mul_zero] using hHB.mul hBN
  have hscaled (K : ℕ) (hK : 0 < K) := by
    have hAK : Tendsto (fun s => (A s : ℝ) / (K * H s : ℕ)) atTop (𝓝 0) := by
      have heq : (fun s => (A s : ℝ) / (K * H s : ℕ)) = fun s => ((A s : ℝ) / H s) / K := by
        funext s
        push_cast
        ring
      rw [heq]
      simpa only [zero_div] using hAH.div_const (K : ℝ)
    have hKB : Tendsto (fun s => ((K * H s : ℕ) : ℝ) / B s) atTop (𝓝 0) := by
      simpa only [Nat.cast_mul, mul_div_assoc, mul_zero] using hHB.const_mul (K : ℝ)
    exact hcontrol (fun s => K * H s) (Eventually.of_forall fun s => Nat.mul_pos hK (hHpos s)) hAK hKB
  obtain ⟨_, Q, ε, hεpos, hεlim, hQ, hdiv, hperiod⟩ :=
    intermediate_fourier_convolution_and_periods 6 (by decide) F w hF hw d c α hc
      (N ∘ τ) A B hNpos happrox
      (fun W hW hAW hWB => hcontrol W (Eventually.of_forall hW) hAW hWB)
      H hHpos hHtop hAH hHB hHN
  obtain ⟨q, start, hHq, hqtop, hqgap, hqdiv, hstart, hinside, hcount⟩ :=
    exists_selected_convolution_windows Aset Bset w (N ∘ τ) H hNpos hHpos hHtop hHN Q ε
      (fun s => (hεpos s).le) hεlim hQ hdiv (hscaled 6 (by decide)).1 hperiod
  have hloH : Tendsto (fun s => (lower (τ s) : ℝ) / H s) atTop (𝓝 0) :=
    window_ratio_tendsto_zero_of_intermediate H A (lower ∘ τ) (fun s => (hAB s).1) hlo hAH
  have herrorH (S : Set ℕ) (x : ℝ)
      (he : Tendsto (fun s => prefixError S x (N s) / lower s) atTop (𝓝 0)) :
      Tendsto (fun s => prefixError S x (N (τ s)) / H s) atTop (𝓝 0) := by
    have ht := (he.comp hτ.tendsto_atTop).mul hloH
    simp only [mul_zero] at ht
    apply ht.congr'
    filter_upwards [(hlower.comp hτ.tendsto_atTop).eventually (eventually_gt_atTop 0)] with s hs
    have hlow : (lower (τ s) : ℝ) ≠ 0 := by exact_mod_cast hs.ne'
    dsimp only [Function.comp_def]
    field_simp
  obtain ⟨A', B', hsub, hexhaust, hAd, hBd, hCd, hAloss, hBloss, hsum⟩ :=
    exists_dense_cyclic_removal Aset Bset a b c₀ hB (N ∘ τ) H (fun s => (q s : ℕ)) start
      hHpos hHq hqtop (Eventually.of_forall hstart) hinside
      (herrorH Aset a hAerror) (herrorH (Aset + Bset) c₀ hCerror) hcount
  have hqsmall : ∀ᶠ s in atTop, (q s : ℕ) ≤ 2 * H s := by
    filter_upwards [hqgap.eventually (gt_mem_nhds (by norm_num : (0 : ℝ) < 1 / 2))] with s hs
    rw [Nat.cast_sub (hHq s)] at hs
    have hqr : (0 : ℝ) < (q s : ℕ) := by positivity
    have ht := (div_lt_iff₀ hqr).mp hs
    have hr : ((q s : ℕ) : ℝ) ≤ 2 * H s := by linarith
    exact_mod_cast hr
  have hqN : Tendsto (fun s => ((q s : ℕ) : ℝ) / N (τ s)) atTop (𝓝 0) := by
    have hu : Tendsto (fun s => (2 : ℝ) * (H s : ℝ) / N (τ s)) atTop (𝓝 0) := by
      simpa only [mul_div_assoc, mul_zero] using hHN.const_mul 2
    apply squeeze_zero' (Eventually.of_forall fun s => by positivity) ?_
      hu
    filter_upwards [hqsmall] with s hs
    exact div_le_div_of_nonneg_right (show ((q s : ℕ) : ℝ) ≤ 2 * (H s : ℝ) by exact_mod_cast hs)
      (show (0 : ℝ) ≤ N (τ s) by positivity)
  have hloq : Tendsto (fun s => (lower (τ s) : ℝ) / (q s : ℕ)) atTop (𝓝 0) := by
    apply squeeze_zero (fun s => by positivity) (fun s => ?_) hloH
    exact div_le_div_of_nonneg_left (by positivity) (by exact_mod_cast hHpos s) (by exact_mod_cast hHq s)
  exact ⟨τ, q, start, A', B', hτ, hqtop, hqN, hloq, hqdiv, hinside, hsub, hexhaust, hAd, hBd, hCd, hsum⟩

end Erdos335.IntermediateScale
