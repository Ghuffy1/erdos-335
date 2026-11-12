import Erdos335.DensityWindowScales
import Erdos335.TwoOrientationCyclicModels

/-!
# Two-orientation cyclic models from ordinary density assumptions
-/

set_option autoImplicit false

open Filter Set Topology
open scoped Pointwise

namespace Erdos335.IntermediateScale

theorem exists_two_orientation_models_of_density
    (N : ℕ → ℕ) [∀ s, NeZero (N s)]
    (hN : Tendsto N atTop atTop) (hmono : Monotone N)
    (hprev : Tendsto (fun s => (N (s - 1) : ℝ) / N s) atTop (𝓝 0))
    (A B : Set ℕ) (a b c : ℝ)
    (hA : HasDensity A a) (hB : HasDensity B b) (hC : HasDensity (A + B) c)
    (U : Ultrafilter ℕ) (hU : (U : Filter ℕ) ≤ atTop) :
    ∃ (τ H start : ℕ → ℕ) (q : Bool → ℕ → ℕ+),
      StrictMono τ ∧ (∀ s, 0 < H s) ∧ Tendsto H atTop atTop ∧
      Tendsto (fun s => (H s : ℝ) / N (τ s)) atTop (𝓝 0) ∧
      (∀ s, 0 < start s) ∧ ∀ i : Bool,
      (∀ s, H s ≤ (q i s : ℕ)) ∧ Tendsto (fun s => (q i s : ℕ)) atTop atTop ∧
      Tendsto (fun s => (((q i s : ℕ) - H s : ℕ) : ℝ) / (q i s : ℕ)) atTop (𝓝 0) ∧
      Tendsto (fun s => ((q i s : ℕ) : ℝ) / N (τ s)) atTop (𝓝 0) ∧
      Tendsto (fun s => prefixError A a (N (τ s)) / (q i s : ℕ)) atTop (𝓝 0) ∧
      Tendsto (fun s => prefixError B b (N (τ s)) / (q i s : ℕ)) atTop (𝓝 0) ∧
      Tendsto (fun s => prefixError (A + B) c (N (τ s)) / (q i s : ℕ)) atTop (𝓝 0) ∧
      (∀ M : ℕ, 0 < M → ∀ᶠ s in atTop, M ∣ (q i s : ℕ)) ∧
      (∀ᶠ s in atTop, start s + (q i s : ℕ) ≤ N (τ s)) ∧
      ∃ D E : ∀ s, Finset (ZMod (q i s : ℕ)),
        (∀ s, D s ⊆ cyclicWindow (cond i B A) (start s) (q i s : ℕ) ∧
          E s ⊆ cyclicWindow (cond i A B) 0 (q i s : ℕ)) ∧
        (∀ v ∈ cond i A B, ∀ᶠ s in atTop, (v : ZMod (q i s : ℕ)) ∈ E s) ∧
        Tendsto (fun s => ((D s).card : ℝ) / (q i s : ℕ)) atTop (𝓝 (cond i b a)) ∧
        Tendsto (fun s => ((E s).card : ℝ) / (q i s : ℕ)) atTop (𝓝 (cond i a b)) ∧
        Tendsto (fun s => ((cyclicWindow (A + B) (start s) (q i s : ℕ)).card : ℝ) /
          (q i s : ℕ)) atTop (𝓝 c) ∧
        Tendsto (fun s => (((D s + E s) \ cyclicWindow (A + B) (start s) (q i s : ℕ)).card : ℝ) /
          (q i s : ℕ)) atTop (𝓝 0) := by
  obtain ⟨L, hLpos, hL, hLN, hNL, hAe, hBe, hCe⟩ :=
    exists_density_window_scales A B (A + B) a b c hA hB hC N hN (fun s => NeZero.pos _)
  obtain ⟨τ, H, start, q, hτ, hHpos, hHtop, hHN, hstart, hq⟩ :=
    exists_two_orientation_cyclic_models N hN hmono hprev L N hL hN hNL
      (Eventually.of_forall fun _ => le_rfl) A B a b c hA hB hAe hBe hCe U hU
  refine ⟨τ, H, start, q, hτ, hHpos, hHtop, hHN, hstart, ?_⟩
  intro i
  obtain ⟨hHq, hqtop, hqgap, hqN, hLq, hqdiv, hinside, D, E, hsub,
    hexhaust, hD, hE, hC, hsum⟩ := hq i
  have transfer (S : Set ℕ) (d : ℝ)
      (he : Tendsto (fun s => prefixError S d (N s) / L s) atTop (𝓝 0)) :
      Tendsto (fun s => prefixError S d (N (τ s)) / (q i s : ℕ)) atTop (𝓝 0) :=
    prefix_error_control_of_scale_domination S d (N ∘ τ) (L ∘ τ) (fun s => (q i s : ℕ))
      (fun s => hLpos (τ s)) (he.comp hτ.tendsto_atTop) hLq
  exact ⟨hHq, hqtop, hqgap, hqN, transfer A a hAe, transfer B b hBe, transfer (A + B) c hCe,
    hqdiv, hinside, D, E, hsub, hexhaust, hD, hE, hC, hsum⟩

end Erdos335.IntermediateScale
