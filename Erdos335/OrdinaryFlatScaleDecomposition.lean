import Erdos335.LoebFlatScaleFamily
import Erdos335.OrdinaryLoebRealization

/-!
# An ordinary bounded decomposition at the endpoints of a flat scale fiber
-/

set_option autoImplicit false

open Filter Set Topology MeasureTheory
open scoped InnerProductSpace

namespace Erdos335.IntermediateScale

open Erdos335.Loeb

theorem exists_ordinary_flat_scale_decomposition
    (N : ℕ → ℕ) [∀ s, NeZero (N s)]
    (hN : Tendsto N atTop atTop) (hmono : Monotone N)
    (hprev : Tendsto (fun s => (N (s - 1) : ℝ) / N s) atTop (𝓝 0))
    (lower upper : ℕ → ℕ)
    (hlower : Tendsto lower atTop atTop) (hupper : Tendsto upper atTop atTop)
    (hgap : Tendsto (fun s => (upper s : ℝ) / lower s) atTop atTop)
    (hupperN : ∀ᶠ s in atTop, upper s ≤ N s)
    (F : ℕ → ℝ) (hF : ∀ n, F n ∈ Icc (0 : ℝ) 1)
    (U : Ultrafilter ℕ) (hU : (U : Filter ℕ) ≤ atTop) :
    ∃ (ε : ℕ → ℝ) (L : ℕ → ℕ)
      (m : ∀ (p : BlockScaleParameter) (k s : ℕ),
        BlockRegularModel F (blockScaleFamily lower upper p s) (L k) (ε k))
      (x : unitInterval) (ρ : ℕ → ℕ) (w : ℕ → ℝ),
      (x : ℝ) ∈ Ioo (0 : ℝ) 1 ∧
      (∀ k, 0 < ε k ∧ ε k ≤ 1 ∧ 0 < L k) ∧
      Tendsto ε atTop (𝓝 0) ∧ StrictMono ρ ∧
      (∀ n, w n ∈ Icc (0 : ℝ) 1) ∧
      (∀ δ > 0, ∃ K : ℕ, ∀ k ≥ K, ∀ᶠ s in atTop,
        prefixEnergy (fun n => w n - stitchedBlockValue N hN (m (toLex (x, 0)) k) n) (N (ρ s)) ≤ δ) ∧
      (∀ δ > 0, ∃ K : ℕ, ∀ k ≥ K, ∀ᶠ s in atTop,
        prefixEnergy (fun n => w n - stitchedBlockValue N hN (m (toLex (x, 1)) k) n) (N (ρ s)) ≤ δ) ∧
      Tendsto (fun s => prefixCorrelation w (fun n => F n - w n) (N (ρ s))) atTop (𝓝 0) ∧
      Tendsto (fun s => prefixCorrelation (fun n => F n - w n) (fun _ => 1) (N (ρ s))) atTop (𝓝 0) := by
  obtain ⟨ε, L, m, g, x, hx, hpos, hε, hbudget, hlim, _hnorm, _hown, _hcross, hflat⟩ :=
    exists_loeb_flat_scale_family N hN hmono hprev lower upper hlower hupper hgap hupperN F hF U hU
  let p : BlockScaleParameter := toLex (x, 0)
  let q : BlockScaleParameter := toLex (x, 1)
  let f := fun k => stitchedBlockValue N hN (m p k)
  let f' := fun k => stitchedBlockValue N hN (m q k)
  have hf (k n : ℕ) : f k n ∈ Icc (0 : ℝ) 1 := stitchedBlockValue_mem N hN (m p k) n
  have hf' (k n : ℕ) : f' k n ∈ Icc (0 : ℝ) 1 := stitchedBlockValue_mem N hN (m q k) n
  have hH := blockScaleFamily_pos lower upper p
  have hHN := blockScaleFamily_ambient_ratio lower upper N hlower hupper hgap hupperN p
  have hown (k : ℕ) : ⟪prefixLoebVector N U hU (f k) (hf k),
      prefixLoebVector N U hU F hF - prefixLoebVector N U hU (f k) (hf k)⟫_ℝ = 0 := by
    exact tendsto_nhds_unique
      (tendsto_prefixLoebVector_residual_correlation N U hU F (f k) (f k) hF (hf k) (hf k))
      ((stitchedBlock_orthogonality N hN hmono hprev hHN hH (m p k) hF).mono_left hU)
  have hcross (k l : ℕ) (hkl : k ≤ l) : |⟪prefixLoebVector N U hU (f k) (hf k),
      prefixLoebVector N U hU F hF - prefixLoebVector N U hU (f l) (hf l)⟫_ℝ| ≤ 2 * ε k := by
    rcases hkl.eq_or_lt with heq | hlt
    · subst l
      simpa only [hown, abs_zero] using mul_nonneg (by norm_num : (0 : ℝ) ≤ 2) (hpos k).1.le
    · obtain ⟨e, he, hb⟩ := stitched_models_correlation_bound N hN hmono hprev hF
        (m p k) (m p l) hH hH (hpos k).1.le (hpos l).1.le (hpos l).2.1 (Or.inl rfl) hHN
      have ht := (tendsto_prefixLoebVector_residual_correlation N U hU F (f k) (f l)
        hF (hf k) (hf l)).abs.sub (he.mono_left hU)
      simp only [sub_zero] at ht
      apply le_of_tendsto ht
      filter_upwards [hb.filter_mono hU] with s hs
      linarith [hbudget k l hlt]
  have hmean (k : ℕ) : Tendsto (fun s => prefixCorrelation (fun n => F n - f k n) (fun _ => 1) (N s))
      (U : Filter ℕ) (𝓝 0) :=
    (stitchedBlock_mean_preservation N hN hmono hprev hHN hH (m p k) hF).mono_left hU
  have hlim' : Tendsto (fun k => prefixLoebVector N U hU (f' k) (hf' k)) atTop (𝓝 (g p)) := by
    have ht := hlim q
    have hgp : g q = g p := hflat 1
    rw [hgp] at ht
    exact ht
  obtain ⟨ρ, w, hρ, hw, happrox, happrox', horth, hzero⟩ :=
    exists_ordinary_realization_of_equal_loeb_limits N hN U hU F f f' hF hf hf' (g p)
      (hlim p) hlim' (fun k => 2 * ε k) (by simpa only [mul_zero] using hε.const_mul 2)
      hown hcross hmean
  exact ⟨ε, L, m, x, ρ, w, hx, hpos, hε, hρ, hw, happrox, happrox', horth, hzero⟩

end Erdos335.IntermediateScale
