import Erdos335.ConstrainedFourierWindows
import Erdos335.DenseCyclicRemoval

/-!
# Density-preserving cyclic models at prescribed dense starts
-/

set_option autoImplicit false

open Filter Set Topology
open scoped Pointwise

namespace Erdos335.IntermediateScale

theorem exists_constrained_cyclic_models {I : Type*} [Fintype I]
    (A B : I → Set ℕ) (a b c : I → ℝ) (hB : ∀ i, HasDensity (B i) (b i))
    (N L V H : ℕ → ℕ) (hN : ∀ s, 0 < N s)
    (hHpos : ∀ s, 0 < H s) (hH : Tendsto H atTop atTop)
    (hLH : Tendsto (fun s => (L s : ℝ) / H s) atTop (𝓝 0))
    (hHV : Tendsto (fun s => (H s : ℝ) / V s) atTop (𝓝 0))
    (hHN : Tendsto (fun s => (H s : ℝ) / N s) atTop (𝓝 0))
    (m : ∀ i, IntermediateFourierModel ((A i).indicator (fun _ => (1 : ℝ))) N L V)
    (hAe : ∀ i, Tendsto (fun s => prefixError (A i) (a i) (N s) / H s) atTop (𝓝 0))
    (hCe : ∀ i, Tendsto (fun s => prefixError (A i + B i) (c i) (N s) / H s) atTop (𝓝 0))
    (S : ℕ → Finset ℕ) (hS : ∀ s, S s ⊆ Finset.range (N s))
    (δ : ℝ) (hδ : 0 < δ) (hcard : ∀ᶠ s in atTop, δ ≤ ((S s).card : ℝ) / N s) :
    ∃ (n : ℕ → ℕ) (q : I → ℕ → ℕ+),
      (∀ s, n s < N s) ∧ (∀ᶠ s in atTop, n s ∈ S s) ∧ ∀ i,
      (∀ s, H s ≤ (q i s : ℕ)) ∧ Tendsto (fun s => (q i s : ℕ)) atTop atTop ∧
      Tendsto (fun s => (((q i s : ℕ) - H s : ℕ) : ℝ) / (q i s : ℕ)) atTop (𝓝 0) ∧
      (∀ M : ℕ, 0 < M → ∀ᶠ s in atTop, M ∣ (q i s : ℕ)) ∧
      (∀ᶠ s in atTop, n s + 3 * H s + (q i s : ℕ) ≤ N s) ∧
      ∃ D E : ∀ s, Finset (ZMod (q i s : ℕ)),
        (∀ s, D s ⊆ cyclicWindow (A i) (n s + 3 * H s) (q i s : ℕ) ∧
          E s ⊆ cyclicWindow (B i) 0 (q i s : ℕ)) ∧
        (∀ v ∈ B i, ∀ᶠ s in atTop, (v : ZMod (q i s : ℕ)) ∈ E s) ∧
        Tendsto (fun s => ((D s).card : ℝ) / (q i s : ℕ)) atTop (𝓝 (a i)) ∧
        Tendsto (fun s => ((E s).card : ℝ) / (q i s : ℕ)) atTop (𝓝 (b i)) ∧
        Tendsto (fun s => ((cyclicWindow (A i + B i) (n s + 3 * H s) (q i s : ℕ)).card : ℝ) /
          (q i s : ℕ)) atTop (𝓝 (c i)) ∧
        Tendsto (fun s => (((D s + E s) \
          cyclicWindow (A i + B i) (n s + 3 * H s) (q i s : ℕ)).card : ℝ) /
          (q i s : ℕ)) atTop (𝓝 0) := by
  obtain ⟨n, q, hn, hinsideS, hq⟩ := exists_constrained_fourier_windows A B N L V H hN
    hHpos hH hLH hHV hHN m S hS δ hδ hcard
  refine ⟨n, q, hn, hinsideS, ?_⟩
  intro i
  obtain ⟨hHq, hqtop, hqgap, hqdiv, hinside, hcount⟩ := hq i
  have hstart : ∀ᶠ s in atTop, 0 < n s + 3 * H s := by
    apply Eventually.of_forall
    intro s
    have hp := hHpos s
    omega
  obtain ⟨D, E, hsub, hexhaust, hD, hE, hC, hDloss, hEloss, hsum⟩ :=
    exists_dense_cyclic_removal (A i) (B i) (a i) (b i) (c i) (hB i) N H
      (fun s => (q i s : ℕ)) (fun s => n s + 3 * H s) hHpos hHq hqtop hstart
      hinside (hAe i) (hCe i) hcount
  exact ⟨hHq, hqtop, hqgap, hqdiv, hinside, D, E, hsub, hexhaust, hD, hE, hC, hsum⟩

end Erdos335.IntermediateScale
