import Erdos335.JointIntermediateFourierModels
import Erdos335.DensityWindowScales
import Erdos335.JointFourierWindows
import Erdos335.CyclicWindowDensityGeneral

/-!
# Retaining the Fourier witnesses before selecting window starts
-/

set_option autoImplicit false

open Filter Set Topology
open scoped Pointwise

namespace Erdos335.IntermediateScale

theorem exists_fixed_scale_fourier_models_of_density
    (N : ℕ → ℕ) [∀ s, NeZero (N s)]
    (hN : Tendsto N atTop atTop) (hmono : Monotone N)
    (hprev : Tendsto (fun s => (N (s - 1) : ℝ) / N s) atTop (𝓝 0))
    (A B : Set ℕ) (a b c : ℝ)
    (hA : HasDensity A a) (hB : HasDensity B b) (hC : HasDensity (A + B) c)
    (U : Ultrafilter ℕ) (hU : (U : Filter ℕ) ≤ atTop) :
    ∃ τ L V H : ℕ → ℕ,
      StrictMono τ ∧
      Tendsto (fun s => (N (τ (s - 1)) : ℝ) / N (τ s)) atTop (𝓝 0) ∧
      (∀ s, 0 < L s ∧ 0 < V s) ∧ (∀ s, 0 < H s) ∧
      Tendsto L atTop atTop ∧ Tendsto H atTop atTop ∧
      Tendsto (fun s => (L s : ℝ) / V s) atTop (𝓝 0) ∧
      Tendsto (fun s => (L s : ℝ) / H s) atTop (𝓝 0) ∧
      Tendsto (fun s => (H s : ℝ) / V s) atTop (𝓝 0) ∧
      Tendsto (fun s => (H s : ℝ) / N (τ s)) atTop (𝓝 0) ∧
      Tendsto (fun s => prefixError A a (N (τ s)) / H s) atTop (𝓝 0) ∧
      Tendsto (fun s => prefixError B b (N (τ s)) / H s) atTop (𝓝 0) ∧
      Tendsto (fun s => prefixError (A + B) c (N (τ s)) / H s) atTop (𝓝 0) ∧
      Nonempty (IntermediateFourierModel (A.indicator (fun _ => (1 : ℝ))) (N ∘ τ) L V) ∧
      Nonempty (IntermediateFourierModel (B.indicator (fun _ => (1 : ℝ))) (N ∘ τ) L V) := by
  classical
  obtain ⟨K, hKpos, hK, _, hNK, hAe, hBe, hCe⟩ :=
    exists_density_window_scales A B (A + B) a b c hA hB hC N hN (fun s => NeZero.pos _)
  have hFa (n : ℕ) : A.indicator (fun _ => (1 : ℝ)) n ∈ Icc (0 : ℝ) 1 := by
    by_cases hn : n ∈ A <;> simp [hn]
  have hFb (n : ℕ) : B.indicator (fun _ => (1 : ℝ)) n ∈ Icc (0 : ℝ) 1 := by
    by_cases hn : n ∈ B <;> simp [hn]
  obtain ⟨τ, L, V, hτ, hprev', hpos, hL, hKL, hLV, hVN, ⟨mA⟩, ⟨mB⟩⟩ :=
    exists_joint_intermediate_fourier_models N hN hmono hprev K N hK hN hNK
      (Eventually.of_forall fun _ => le_rfl)
      (A.indicator (fun _ => (1 : ℝ))) (B.indicator (fun _ => (1 : ℝ))) hFa hFb U hU
  let H := positiveIntermediateScale L V (1 / 2) 0
  have hHpos : ∀ s, 0 < H s := positiveIntermediateScale_pos L V _ _
  have hV := scale_tendsto_atTop_of_smaller L V hL (fun s => (hpos s).2) hLV
  have hVL := reciprocal_scale_ratio_tendsto_atTop L V (fun s => (hpos s).1)
    (fun s => (hpos s).2) hLV
  have hH : Tendsto H atTop atTop := positiveIntermediateScale_atTop L V hL hVL _ _ (by norm_num)
  have hLH : Tendsto (fun s => (L s : ℝ) / H s) atTop (𝓝 0) :=
    positiveIntermediateScale_lower_ratio L V hL hVL _ _ (by norm_num)
  have hHV : Tendsto (fun s => (H s : ℝ) / V s) atTop (𝓝 0) :=
    positiveIntermediateScale_ambient_ratio L V V hL hV hVL
      (Eventually.of_forall fun _ => le_rfl) _ _ (by norm_num) (by norm_num)
  have hHN : Tendsto (fun s => (H s : ℝ) / N (τ s)) atTop (𝓝 0) :=
    window_ratio_tendsto_zero_of_intermediate (N ∘ τ) V H (fun s => (hpos s).2) hHV hVN
  have transfer (S : Set ℕ) (d : ℝ)
      (he : Tendsto (fun s => prefixError S d (N s) / K s) atTop (𝓝 0)) :
      Tendsto (fun s => prefixError S d (N (τ s)) / H s) atTop (𝓝 0) := by
    have herrorL := prefix_error_control_of_scale_domination S d (N ∘ τ) (K ∘ τ) L
      (fun s => hKpos (τ s)) (he.comp hτ.tendsto_atTop) hKL
    exact prefix_error_control_of_scale_domination S d (N ∘ τ) L H
      (fun s => (hpos s).1) herrorL hLH
  exact ⟨τ, L, V, H, hτ, hprev', hpos, hHpos, hL, hH, hLV, hLH, hHV, hHN,
    transfer A a hAe, transfer B b hBe, transfer (A + B) c hCe, ⟨mA⟩, ⟨mB⟩⟩

end Erdos335.IntermediateScale
