import Erdos335.IntermediateScale
import Erdos335.ReciprocalScaleRatios

/-!
# Admissible intermediate scales from ordinary densities
-/

set_option autoImplicit false

open Filter Topology

namespace Erdos335.IntermediateScale

theorem prefixError_mono (S : Set ℕ) (a : ℝ) {m n : ℕ} (hmn : m ≤ n) :
    prefixError S a m ≤ prefixError S a n := by
  apply Finset.sup'_le
  intro j hj
  apply count_error_le_prefixError S a
  have hjm : j ≤ m := by have := Finset.mem_range.mp hj; omega
  exact hjm.trans hmn

theorem exists_density_window_scales (A B C : Set ℕ) (a b c : ℝ)
    (hA : HasDensity A a) (hB : HasDensity B b) (hC : HasDensity C c)
    (N : ℕ → ℕ) (hN : Tendsto N atTop atTop) (hNpos : ∀ s, 0 < N s) :
    ∃ L : ℕ → ℕ,
      (∀ s, 0 < L s) ∧ Tendsto L atTop atTop ∧
      Tendsto (fun s => (L s : ℝ) / N s) atTop (𝓝 0) ∧
      Tendsto (fun s => (N s : ℝ) / L s) atTop atTop ∧
      Tendsto (fun s => prefixError A a (N s) / L s) atTop (𝓝 0) ∧
      Tendsto (fun s => prefixError B b (N s) / L s) atTop (𝓝 0) ∧
      Tendsto (fun s => prefixError C c (N s) / L s) atTop (𝓝 0) := by
  obtain ⟨H, hHpos, hHtop, hHN, hAe, hBe, hCe⟩ :=
    exists_common_error_dominating_scale A B C a b c hA hB hC
  let L := H ∘ N
  have hLpos (s : ℕ) : 0 < L s := hHpos (N s)
  have hLN : Tendsto (fun s => (L s : ℝ) / N s) atTop (𝓝 0) := hHN.comp hN
  have transfer (S : Set ℕ) (d : ℝ)
      (he : Tendsto (fun n => prefixError S d (2 * n) / H n) atTop (𝓝 0)) :
      Tendsto (fun s => prefixError S d (N s) / L s) atTop (𝓝 0) := by
    apply squeeze_zero (fun s => div_nonneg (prefixError_nonneg S d (N s)) (by positivity))
      (fun s => ?_) (he.comp hN)
    exact div_le_div_of_nonneg_right (prefixError_mono S d (by omega)) (by positivity)
  exact ⟨L, hLpos, hHtop.comp hN, hLN,
    reciprocal_scale_ratio_tendsto_atTop L N hLpos hNpos hLN,
    transfer A a hAe, transfer B b hBe, transfer C c hCe⟩

end Erdos335.IntermediateScale
