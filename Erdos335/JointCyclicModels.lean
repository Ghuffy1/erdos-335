import Erdos335.JointFourierWindows
import Erdos335.DenseCyclicRemoval

/-!
# Density-preserving cyclic models on common-start windows
-/

set_option autoImplicit false

open Filter Set Topology
open scoped Pointwise

namespace Erdos335.IntermediateScale

theorem exists_joint_cyclic_models {I : Type*} [Fintype I]
    (A B : I → Set ℕ) (a b c : I → ℝ) (hB : ∀ i, HasDensity (B i) (b i))
    (N L U : ℕ → ℕ) (hN : ∀ s, 0 < N s)
    (hLpos : ∀ s, 0 < L s) (hUpos : ∀ s, 0 < U s) (hL : Tendsto L atTop atTop)
    (hLU : Tendsto (fun s => (L s : ℝ) / U s) atTop (𝓝 0))
    (hUN : Tendsto (fun s => (U s : ℝ) / N s) atTop (𝓝 0))
    (m : ∀ i, IntermediateFourierModel ((A i).indicator (fun _ => (1 : ℝ))) N L U)
    (hAerror : ∀ i, Tendsto (fun s => prefixError (A i) (a i) (N s) / L s) atTop (𝓝 0))
    (hCerror : ∀ i, Tendsto (fun s => prefixError (A i + B i) (c i) (N s) / L s) atTop (𝓝 0)) :
    ∃ (H start : ℕ → ℕ) (q : I → ℕ → ℕ+),
      (∀ s, 0 < H s) ∧ Tendsto H atTop atTop ∧
      Tendsto (fun s => (H s : ℝ) / N s) atTop (𝓝 0) ∧ (∀ s, 0 < start s) ∧ ∀ i,
      (∀ s, H s ≤ (q i s : ℕ)) ∧ Tendsto (fun s => (q i s : ℕ)) atTop atTop ∧
      Tendsto (fun s => (((q i s : ℕ) - H s : ℕ) : ℝ) / (q i s : ℕ)) atTop (𝓝 0) ∧
      Tendsto (fun s => ((q i s : ℕ) : ℝ) / N s) atTop (𝓝 0) ∧
      Tendsto (fun s => (L s : ℝ) / (q i s : ℕ)) atTop (𝓝 0) ∧
      (∀ M : ℕ, 0 < M → ∀ᶠ s in atTop, M ∣ (q i s : ℕ)) ∧
      (∀ᶠ s in atTop, start s + (q i s : ℕ) ≤ N s) ∧
      ∃ D E : ∀ s, Finset (ZMod (q i s : ℕ)),
        (∀ s, D s ⊆ cyclicWindow (A i) (start s) (q i s : ℕ) ∧
          E s ⊆ cyclicWindow (B i) 0 (q i s : ℕ)) ∧
        (∀ v ∈ B i, ∀ᶠ s in atTop, (v : ZMod (q i s : ℕ)) ∈ E s) ∧
        Tendsto (fun s => ((D s).card : ℝ) / (q i s : ℕ)) atTop (𝓝 (a i)) ∧
        Tendsto (fun s => ((E s).card : ℝ) / (q i s : ℕ)) atTop (𝓝 (b i)) ∧
        Tendsto (fun s => ((cyclicWindow (A i + B i) (start s) (q i s : ℕ)).card : ℝ) /
          (q i s : ℕ)) atTop (𝓝 (c i)) ∧
        Tendsto (fun s => (((D s + E s) \ cyclicWindow (A i + B i) (start s) (q i s : ℕ)).card : ℝ) /
          (q i s : ℕ)) atTop (𝓝 0) := by
  obtain ⟨H, start, q, hHpos, hHtop, hLH, hHU, hHN, hstart, hq⟩ :=
    exists_joint_fourier_convolution_windows A B N L U hN hLpos hUpos hL hLU hUN m
  refine ⟨H, start, q, hHpos, hHtop, hHN, hstart, ?_⟩
  intro i
  obtain ⟨hHq, hqtop, hqgap, hqdiv, hinside, hcount⟩ := hq i
  have hqsmall : ∀ᶠ s in atTop, (q i s : ℕ) ≤ 2 * H s := by
    filter_upwards [hqgap.eventually (gt_mem_nhds (by norm_num : (0 : ℝ) < 1 / 2))] with s hs
    rw [Nat.cast_sub (hHq s)] at hs
    have hqr : (0 : ℝ) < (q i s : ℕ) := by positivity
    have ht := (div_lt_iff₀ hqr).mp hs
    have hr : ((q i s : ℕ) : ℝ) ≤ 2 * H s := by linarith
    exact_mod_cast hr
  have hqN : Tendsto (fun s => ((q i s : ℕ) : ℝ) / N s) atTop (𝓝 0) := by
    have hu : Tendsto (fun s => (2 : ℝ) * (H s : ℝ) / N s) atTop (𝓝 0) := by
      simpa only [mul_div_assoc, mul_zero] using hHN.const_mul 2
    apply squeeze_zero' (Eventually.of_forall fun s => by positivity) ?_ hu
    filter_upwards [hqsmall] with s hs
    exact div_le_div_of_nonneg_right (show ((q i s : ℕ) : ℝ) ≤ 2 * (H s : ℝ) by exact_mod_cast hs)
      (show (0 : ℝ) ≤ N s by positivity)
  have hLq : Tendsto (fun s => (L s : ℝ) / (q i s : ℕ)) atTop (𝓝 0) := by
    apply squeeze_zero (fun s => by positivity) (fun s => ?_) hLH
    exact div_le_div_of_nonneg_left (by positivity) (by exact_mod_cast hHpos s) (by exact_mod_cast hHq s)
  have hAe := prefix_error_control_of_scale_domination (A i) (a i) N L H hLpos (hAerror i) hLH
  have hCe := prefix_error_control_of_scale_domination (A i + B i) (c i) N L H hLpos (hCerror i) hLH
  obtain ⟨D, E, hsub, hexhaust, hD, hE, hC, hDloss, hEloss, hsum⟩ :=
    exists_dense_cyclic_removal (A i) (B i) (a i) (b i) (c i) (hB i)
      N H (fun s => (q i s : ℕ)) start hHpos hHq hqtop
      (Eventually.of_forall hstart) hinside hAe hCe hcount
  exact ⟨hHq, hqtop, hqgap, hqN, hLq, hqdiv, hinside, D, E, hsub, hexhaust, hD, hE, hC, hsum⟩

end Erdos335.IntermediateScale
