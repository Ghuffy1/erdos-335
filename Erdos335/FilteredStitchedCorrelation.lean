import Erdos335.SparseCrossCorrelation

/-!
# Passing local correlation bounds through sparse stitching and filtering
-/

set_option autoImplicit false

open Filter Topology

namespace Erdos335.IntermediateScale

theorem filtered_stitched_correlation_bound
    (U : Filter ℕ) [NeBot U] (hU : U ≤ atTop)
    (N : ℕ → ℕ) (hN : Tendsto N atTop atTop) (hmono : Monotone N)
    (hratio : Tendsto (fun s => (N (s - 1) : ℝ) / N s) atTop (𝓝 0))
    (F : ℕ → ℝ) (f g : ℕ → ℕ → ℝ)
    (hF : ∀ n, F n ∈ Set.Icc (0 : ℝ) 1)
    (hf : ∀ s n, f s n ∈ Set.Icc (0 : ℝ) 1)
    (hg : ∀ s n, g s n ∈ Set.Icc (0 : ℝ) 1)
    (C ℓ : ℝ) (e : ℕ → ℝ) (he : Tendsto e atTop (𝓝 0))
    (hbound : ∀ᶠ s in atTop, |prefixCorrelation (f s) (fun n => F n - g s n) (N s)| ≤ C + e s)
    (hlimit : Tendsto (fun s => prefixCorrelation (prefixStitch N hN f id)
      (fun n => F n - prefixStitch N hN g id n) (N s)) U (𝓝 ℓ)) : |ℓ| ≤ C := by
  have hpatch := (sparse_stitch_cross_correlation N hN hmono hratio F f g hF hf hg).mono_left hU
  have hcurrent : Tendsto (fun s => prefixCorrelation (f s) (fun n => F n - g s n) (N s)) U (𝓝 ℓ) := by
    have h := hlimit.sub hpatch
    simp only [sub_zero] at h
    apply h.congr
    intro s
    ring
  have herror := he.mono_left hU
  have h := hcurrent.abs.sub herror
  simp only [sub_zero] at h
  apply le_of_tendsto h
  exact (hbound.filter_mono hU).mono fun s hs => by linarith

end Erdos335.IntermediateScale
