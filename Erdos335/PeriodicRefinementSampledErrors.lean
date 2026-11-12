import Erdos335.PeriodicRefinementGoodPoints
import Erdos335.PeriodicRefinementFourierErrors
import Mathlib.Data.Nat.Pairing

/-!
# Almost-everywhere sampling of averaged Fourier errors

This file supplies the bad-set caller for the positive-floor sampling bridge.
Every threshold set is restricted to its actual enlarged ambient range.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1500000

open Filter Topology Set MeasureTheory Finset
open Erdos335.IntermediateScale
open scoped BigOperators ENNReal

noncomputable section

namespace Erdos335.PeriodicRefinement

/-- The threshold estimate only needs eventual positivity of its ambient size. -/
theorem threshold_fraction_tendsto_zero_of_eventually_pos
    (e : ℕ → ℕ → ℝ) (N : ℕ → ℕ) (hN : ∀ᶠ n in atTop, 0 < N n)
    (he : ∀ n s, 0 ≤ e n s)
    (hmean : Tendsto (fun n => (∑ s ∈ range (N n), e n s) / N n) atTop (𝓝 0))
    (ε : ℝ) (hε : 0 < ε) :
    Tendsto (fun n => (((range (N n)).filter (fun s => ε ≤ e n s)).card : ℝ) / N n)
      atTop (𝓝 0) := by
  let P := fun n => max 1 (N n)
  have hPpos (n : ℕ) : 0 < P n := by dsimp only [P]; omega
  have hPN : P =ᶠ[atTop] N := by
    filter_upwards [hN] with n hn
    dsimp only [P]
    exact max_eq_right (by omega)
  have hmeanP : Tendsto (fun n => (∑ s ∈ range (P n), e n s) / P n)
      atTop (𝓝 0) := by
    apply hmean.congr'
    filter_upwards [hPN] with n hn
    simp only [hn]
  apply (threshold_fraction_tendsto_zero e P hPpos he hmeanP ε hε).congr'
  filter_upwards [hPN] with n hn
  simp only [hn]

/-- Positive parameters below the fixed enlargement sample its actual range. -/
theorem floor_mul_mem_enlarged_range
    (N m : ℕ) (hN : 0 < N) (t : ℝ) (ht : 0 < t) (htm : t < m) :
    ⌊t * (N : ℝ)⌋₊ ∈ range (m * N) := by
  have hNr : (0 : ℝ) < N := by exact_mod_cast hN
  apply Finset.mem_range.mpr
  apply (Nat.floor_lt (mul_pos ht hNr).le).mpr
  simpa only [Nat.cast_mul] using mul_lt_mul_of_pos_right htm hNr

/-- One strict subsequence makes every fixed enlarged-range error vanish at
almost every interior positive macroscopic parameter. -/
theorem exists_ae_sampled_error_subsequence
    (N : ℕ → ℕ) (hN : Tendsto N atTop atTop)
    (m : ℕ → ℕ) (e : ℕ → ℕ → ℕ → ℝ)
    (he : ∀ j n s, 0 ≤ e j n s)
    (hmean : ∀ j, Tendsto (fun n =>
      (∑ s ∈ range (m j * N n), e j n s) / (m j * N n : ℕ)) atTop (𝓝 0)) :
    ∃ σ : ℕ → ℕ, StrictMono σ ∧ (∀ n, 0 < N (σ n)) ∧
      ∀ᵐ t : ℝ ∂volume, 0 < t → ∀ j, t < m j →
        Tendsto (fun n => e j (σ n) ⌊t * (N (σ n) : ℝ)⌋₊) atTop (𝓝 0) := by
  classical
  let bad : ℕ → ℕ → Finset ℕ := fun c n =>
    (range (m (Nat.unpair c).1 * N n)).filter fun s =>
      1 / (((Nat.unpair c).2 + 1 : ℕ) : ℝ) ≤ e (Nat.unpair c).1 n s
  have hNpos : ∀ᶠ n in atTop, 0 < N n :=
    (hN.eventually (eventually_ge_atTop 1)).mono fun n hn => by omega
  have hbad (c : ℕ) : Tendsto (fun n => ((bad c n).card : ℝ) / N n)
      atTop (𝓝 0) := by
    let j := (Nat.unpair c).1
    let k := (Nat.unpair c).2
    change Tendsto (fun n =>
      (((range (m j * N n)).filter (fun s => 1 / ((k + 1 : ℕ) : ℝ) ≤ e j n s)).card : ℝ) /
        N n) atTop (𝓝 0)
    by_cases hm : m j = 0
    · simpa [hm] using
        (tendsto_const_nhds : Tendsto (fun _ : ℕ => (0 : ℝ)) atTop (𝓝 0))
    · have hmpos : 0 < m j := Nat.pos_of_ne_zero hm
      have hMpos : ∀ᶠ n in atTop, 0 < m j * N n :=
        hNpos.mono fun n hn => Nat.mul_pos hmpos hn
      have hthin := threshold_fraction_tendsto_zero_of_eventually_pos (e j)
        (fun n => m j * N n) hMpos (he j) (hmean j)
        (1 / ((k + 1 : ℕ) : ℝ)) (by positivity)
      have hscaled := hthin.mul_const (m j : ℝ)
      simp only [zero_mul] at hscaled
      apply hscaled.congr'
      filter_upwards [hNpos] with n hn
      have hmr : (m j : ℝ) ≠ 0 := by exact_mod_cast hm
      have hNr : (N n : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hn)
      simp only [Nat.cast_mul]
      field_simp [hmr, hNr] <;> ring
  obtain ⟨σ, hσ, hNσ, hae⟩ := exists_ae_good_floor_subsequence N hN bad hbad
  refine ⟨σ, hσ, hNσ, ?_⟩
  have hthreshold : Tendsto (fun k : ℕ => 1 / ((k + 1 : ℕ) : ℝ)) atTop (𝓝 0) :=
    (tendsto_const_div_atTop_nhds_zero_nat 1).comp (tendsto_add_atTop_nat 1)
  filter_upwards [hae] with t ht
  intro htpos j htj
  have hinside (n : ℕ) : ⌊t * (N (σ n) : ℝ)⌋₊ ∈ range (m j * N (σ n)) :=
    floor_mul_mem_enlarged_range (N (σ n)) (m j) (hNσ n) t htpos htj
  refine tendsto_order.mpr ⟨?_, ?_⟩
  · intro a ha
    exact Eventually.of_forall fun n => ha.trans_le (he j (σ n) _)
  · intro b hb
    obtain ⟨k, hk⟩ := (hthreshold.eventually (eventually_lt_nhds hb)).exists
    have havoid := ht htpos (Nat.pair j k)
    filter_upwards [havoid] with n hn
    have hnotmem : ⌊t * (N (σ n) : ℝ)⌋₊ ∉
        (range (m j * N (σ n))).filter
          (fun s => 1 / ((k + 1 : ℕ) : ℝ) ≤ e j (σ n) s) := by
      simpa only [bad, Nat.unpair_pair] using hn
    have hsmall : e j (σ n) ⌊t * (N (σ n) : ℝ)⌋₊ < 1 / ((k + 1 : ℕ) : ℝ) := by
      apply lt_of_not_ge
      intro hlarge
      exact hnotmem (mem_filter.mpr ⟨hinside n, hlarge⟩)
    exact hsmall.trans hk

/-- Actual Fourier-model errors satisfy the sampled conclusion on one
subsequence, with all prescribed-period bounds preserved after reindexing. -/
theorem exists_ae_prescribed_window_error_data
    (A B : ℕ → Set ℕ) (N L V H : ℕ → ℕ) (m : ℕ → ℕ+)
    (hNpos : ∀ n, 0 < N n) (hN : Tendsto N atTop atTop)
    (hHpos : ∀ n, 0 < H n) (hH : Tendsto H atTop atTop)
    (hLH : Tendsto (fun n => (L n : ℝ) / H n) atTop (𝓝 0))
    (hHV : Tendsto (fun n => (H n : ℝ) / V n) atTop (𝓝 0))
    (hHN : Tendsto (fun n => (H n : ℝ) / N n) atTop (𝓝 0))
    (model : ∀ j, IntermediateFourierModel ((A j).indicator (fun _ => (1 : ℝ)))
      (fun n => (m j : ℕ) * N n) L V) :
    ∃ (σ : ℕ → ℕ) (Q : ℕ → ℕ → ℕ → ℕ) (ε : ℕ → ℕ → ℝ),
      StrictMono σ ∧ (∀ j n, 0 < ε j n) ∧
      (∀ j, Tendsto (ε j) atTop (𝓝 0)) ∧
      (∀ j, ∀ᶠ n in atTop, ∀ s,
        H (σ n) ≤ Q j n s ∧ (Q j n s : ℝ) ≤ (1 + ε j n) * H (σ n)) ∧
      (∀ j d, 0 < d → ∀ᶠ n in atTop, ∀ s, d ∣ Q j n s) ∧
      ∀ᵐ t : ℝ ∂volume, 0 < t → ∀ j, t < (m j : ℕ) →
        Tendsto (fun n => linearConvolutionPeriodError
          ((A j).indicator (fun _ => (1 : ℝ)))
          ((B j).indicator (fun _ => (1 : ℂ)))
          (Q j n ⌊t * (N (σ n) : ℝ)⌋₊)
          (⌊t * (N (σ n) : ℝ)⌋₊ + 3 * H (σ n))) atTop (𝓝 0) := by
  classical
  have hMN (j n : ℕ) : 0 < (m j : ℕ) * N n := Nat.mul_pos (m j).property (hNpos n)
  have hHM (j : ℕ) : Tendsto (fun n => (H n : ℝ) / ((m j : ℕ) * N n : ℕ))
      atTop (𝓝 0) := by
    have hmr : ((m j : ℕ) : ℝ) ≠ 0 := by exact_mod_cast (m j).property.ne'
    have heq : (fun n => (H n : ℝ) / ((m j : ℕ) * N n : ℕ)) =
        (fun n => ((H n : ℝ) / N n) / ((m j : ℕ) : ℝ)) := by
      funext n
      have hNr : (N n : ℝ) ≠ 0 := by exact_mod_cast (hNpos n).ne'
      simp only [Nat.cast_mul]
      field_simp [hmr, hNr] <;> ring
    rw [heq]
    simpa only [zero_div] using hHN.div_const ((m j : ℕ) : ℝ)
  obtain ⟨Q₀, ε₀, hεpos, hεlim, hQ, hdiv, hmean⟩ :=
    exists_prescribed_window_error_data A B (fun j n => (m j : ℕ) * N n) L V H
      hMN hHpos hH hLH hHV hHM model
  let e : ℕ → ℕ → ℕ → ℝ := fun j n s => linearConvolutionPeriodError
    ((A j).indicator (fun _ => (1 : ℝ))) ((B j).indicator (fun _ => (1 : ℂ)))
      (Q₀ j n s) (s + 3 * H n)
  have he (j n s : ℕ) : 0 ≤ e j n s := by
    unfold e linearConvolutionPeriodError
    positivity
  obtain ⟨σ, hσ, _, hsample⟩ := exists_ae_sampled_error_subsequence N hN
    (fun j => (m j : ℕ)) e he hmean
  let Q := fun j n s => Q₀ j (σ n) s
  let ε := fun j n => ε₀ j (σ n)
  refine ⟨σ, Q, ε, hσ, (fun j n => hεpos j (σ n)),
    (fun j => (hεlim j).comp hσ.tendsto_atTop), ?_, ?_, ?_⟩
  · intro j
    exact hσ.tendsto_atTop.eventually (hQ j)
  · intro j d hd
    exact hσ.tendsto_atTop.eventually (hdiv j d hd)
  · exact hsample

end Erdos335.PeriodicRefinement

end
