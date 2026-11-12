import Mathlib.Order.Filter.AtTopBot.Basic
import Mathlib.Topology.Defs.Filter

/-!
# Extending data from a strict subsequence
-/

set_option autoImplicit false

open Filter Topology

namespace Erdos335.IntermediateScale

noncomputable def strictSubsequenceExtension {X : Type*} (σ : ℕ → ℕ)
    (f g : ℕ → X) (n : ℕ) : X := by
  classical
  exact if h : ∃ i, σ i = n then f h.choose else g n

theorem strictSubsequenceExtension_on {X : Type*} (σ : ℕ → ℕ) (hσ : StrictMono σ)
    (f g : ℕ → X) (i : ℕ) : strictSubsequenceExtension σ f g (σ i) = f i := by
  classical
  have h : ∃ j, σ j = σ i := ⟨i, rfl⟩
  have hi : h.choose = i := hσ.injective h.choose_spec
  simp only [strictSubsequenceExtension, dif_pos h, hi]

theorem eventually_strictSubsequenceExtension {X : Type*} (σ : ℕ → ℕ) (hσ : StrictMono σ)
    (f g : ℕ → X) (P : ℕ → X → Prop)
    (hf : ∀ᶠ i in atTop, P (σ i) (f i)) (hg : ∀ᶠ n in atTop, P n (g n)) :
    ∀ᶠ n in atTop, P n (strictSubsequenceExtension σ f g n) := by
  classical
  obtain ⟨K, hK⟩ := eventually_atTop.mp hf
  obtain ⟨L, hL⟩ := eventually_atTop.mp hg
  filter_upwards [eventually_ge_atTop (max (σ K) L)] with n hn
  by_cases h : ∃ i, σ i = n
  · have hKi : K ≤ h.choose := by
      by_contra hlt
      have hstrict := hσ (lt_of_not_ge hlt)
      have hlow : σ K ≤ n := (le_max_left _ _).trans hn
      rw [h.choose_spec] at hstrict
      omega
    simpa only [strictSubsequenceExtension, dif_pos h, h.choose_spec] using hK h.choose hKi
  · simpa only [strictSubsequenceExtension, dif_neg h] using hL n ((le_max_right _ _).trans hn)

theorem tendsto_strictSubsequenceExtension {X Y : Type*} [TopologicalSpace Y]
    (σ : ℕ → ℕ) (hσ : StrictMono σ) (f g : ℕ → X) (v : ℕ → X → Y) (y : Y)
    (hf : Tendsto (fun i => v (σ i) (f i)) atTop (𝓝 y))
    (hg : Tendsto (fun n => v n (g n)) atTop (𝓝 y)) :
    Tendsto (fun n => v n (strictSubsequenceExtension σ f g n)) atTop (𝓝 y) := by
  apply tendsto_def.mpr
  intro S hS
  exact eventually_strictSubsequenceExtension σ hσ f g (fun n x => v n x ∈ S)
    (hf.eventually hS) (hg.eventually hS)

end Erdos335.IntermediateScale
