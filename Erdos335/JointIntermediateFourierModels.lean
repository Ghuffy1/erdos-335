import Erdos335.IntermediateFourierModel

/-!
# Two ordinary Fourier models on common intermediate scales
-/

set_option autoImplicit false

open Filter Set Topology

namespace Erdos335.IntermediateScale

theorem exists_joint_intermediate_fourier_models
    (N : ℕ → ℕ) [∀ s, NeZero (N s)]
    (hN : Tendsto N atTop atTop) (hmono : Monotone N)
    (hprev : Tendsto (fun s => (N (s - 1) : ℝ) / N s) atTop (𝓝 0))
    (lower upper : ℕ → ℕ)
    (hlower : Tendsto lower atTop atTop) (hupper : Tendsto upper atTop atTop)
    (hgap : Tendsto (fun s => (upper s : ℝ) / lower s) atTop atTop)
    (hupperN : ∀ᶠ s in atTop, upper s ≤ N s)
    (F G : ℕ → ℝ) (hF : ∀ n, F n ∈ Icc (0 : ℝ) 1)
    (hG : ∀ n, G n ∈ Icc (0 : ℝ) 1)
    (U : Ultrafilter ℕ) (hU : (U : Filter ℕ) ≤ atTop) :
    ∃ τ A B : ℕ → ℕ,
      StrictMono τ ∧ Tendsto (fun s => (N (τ (s - 1)) : ℝ) / N (τ s)) atTop (𝓝 0) ∧
      (∀ s, 0 < A s ∧ 0 < B s) ∧ Tendsto A atTop atTop ∧
      Tendsto (fun s => (lower (τ s) : ℝ) / A s) atTop (𝓝 0) ∧
      Tendsto (fun s => (A s : ℝ) / B s) atTop (𝓝 0) ∧
      Tendsto (fun s => (B s : ℝ) / upper (τ s)) atTop (𝓝 0) ∧
      Nonempty (IntermediateFourierModel F (N ∘ τ) A B) ∧
      Nonempty (IntermediateFourierModel G (N ∘ τ) A B) := by
  obtain ⟨ρ, A₀, B₀, hρ, hprev₀, hpos₀, hA₀, hlo₀, hsep₀, hhi₀, ⟨mF⟩⟩ :=
    exists_intermediate_fourier_model N hN hmono hprev lower upper hlower hupper hgap
      hupperN F hF U hU
  have hB₀ : Tendsto B₀ atTop atTop :=
    scale_tendsto_atTop_of_smaller A₀ B₀ hA₀ (fun s => (hpos₀ s).2) hsep₀
  have hgap₀ : Tendsto (fun s => (B₀ s : ℝ) / A₀ s) atTop atTop :=
    reciprocal_scale_ratio_tendsto_atTop A₀ B₀ (fun s => (hpos₀ s).1)
      (fun s => (hpos₀ s).2) hsep₀
  have hB₀N : Tendsto (fun s => (B₀ s : ℝ) / N (ρ s)) atTop (𝓝 0) := by
    apply squeeze_zero' (Eventually.of_forall fun s => by positivity) ?_ hhi₀
    filter_upwards [hρ.tendsto_atTop.eventually hupperN,
      (hupper.comp hρ.tendsto_atTop).eventually (eventually_gt_atTop 0)] with s hs hp
    exact div_le_div_of_nonneg_left (by positivity) (by exact_mod_cast hp) (by exact_mod_cast hs)
  letI : ∀ s, NeZero ((N ∘ ρ) s) := fun s => inferInstanceAs (NeZero (N (ρ s)))
  have hB₀inside : ∀ᶠ s in atTop, B₀ s ≤ (N ∘ ρ) s :=
    eventually_scale_le_of_ratio_zero B₀ (N ∘ ρ) (fun s => NeZero.pos _) hB₀N
  obtain ⟨σ, A, B, hσ, hprev₁, hpos, hA, hlo₁, hsep, hhi₁, ⟨mG⟩⟩ :=
    exists_intermediate_fourier_model (N ∘ ρ) (hN.comp hρ.tendsto_atTop)
      (hmono.comp hρ.monotone) hprev₀ A₀ B₀ hA₀ hB₀ hgap₀ hB₀inside G hG U hU
  let τ := ρ ∘ σ
  have hτ : StrictMono τ := hρ.comp hσ
  have hlo : Tendsto (fun s => (lower (τ s) : ℝ) / A s) atTop (𝓝 0) :=
    window_ratio_tendsto_zero_of_intermediate A (A₀ ∘ σ) (lower ∘ τ)
      (fun s => (hpos₀ (σ s)).1) (hlo₀.comp hσ.tendsto_atTop) hlo₁
  have hhi : Tendsto (fun s => (B s : ℝ) / upper (τ s)) atTop (𝓝 0) :=
    window_ratio_tendsto_zero_of_intermediate (upper ∘ τ) (B₀ ∘ σ) B
      (fun s => (hpos₀ (σ s)).2) hhi₁ (hhi₀.comp hσ.tendsto_atTop)
  refine ⟨τ, A, B, hτ, sparse_prefix_ratio_subsequence N hmono hprev τ hτ,
    hpos, hA, hlo, hsep, hhi, ?_, ?_⟩
  · exact ⟨mF.restrict (fun s => (hpos₀ s).1) (fun s => (hpos₀ s).2) hA₀ hsep₀
      σ hσ A B (fun s => (hpos s).1) (fun s => (hpos s).2) hlo₁ hhi₁⟩
  · exact ⟨mG⟩

end Erdos335.IntermediateScale
