import Erdos335.PeriodicRefinementSampledErrors

/-!
# Actual convolution windows at almost every sampled macroscopic point

The ambient margin absorbs the fixed six-window buffer. The canonical
selected-error normalization then supplies positive integer periods.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1500000

open Filter Topology Set MeasureTheory
open Erdos335.IntermediateScale
open scoped ENNReal

noncomputable section

namespace Erdos335.PeriodicRefinement

/-- A fixed interior macroscopic point eventually has room for six sublinear
windows inside the fixed ambient enlargement. -/
theorem sampled_start_add_six_windows_le
    (N H : ℕ → ℕ) (hNpos : ∀ n, 0 < N n)
    (hHN : Tendsto (fun n => (H n : ℝ) / N n) atTop (𝓝 0))
    (m : ℕ) (t : ℝ) (ht : 0 < t) (htm : t < m) :
    ∀ᶠ n in atTop, ⌊t * (N n : ℝ)⌋₊ + 6 * H n ≤ m * N n := by
  have hmargin : 0 < ((m : ℝ) - t) / 6 := by linarith
  filter_upwards [hHN.eventually (eventually_lt_nhds hmargin)] with n hn
  have hNr : (0 : ℝ) < N n := by exact_mod_cast hNpos n
  have hfloor := Nat.floor_le (mul_pos ht hNr).le
  have hwindow : (H n : ℝ) < (((m : ℝ) - t) / 6) * (N n : ℝ) :=
    (div_lt_iff₀ hNr).mp hn
  have hreal : (⌊t * (N n : ℝ)⌋₊ : ℝ) + 6 * (H n : ℝ) ≤ (m : ℝ) * N n := by
    nlinarith
  exact_mod_cast hreal

/-- For each interior good macroscopic point, the actual Fourier models
produce normalized convolution windows. The period may depend on the point
and on the fixed member of the countable family. -/
theorem exists_ae_sampled_convolution_windows
    (A B : ℕ → Set ℕ) (N L V H : ℕ → ℕ) (m : ℕ → ℕ+)
    (hNpos : ∀ n, 0 < N n) (hN : Tendsto N atTop atTop)
    (hHpos : ∀ n, 0 < H n) (hH : Tendsto H atTop atTop)
    (hLH : Tendsto (fun n => (L n : ℝ) / H n) atTop (𝓝 0))
    (hHV : Tendsto (fun n => (H n : ℝ) / V n) atTop (𝓝 0))
    (hHN : Tendsto (fun n => (H n : ℝ) / N n) atTop (𝓝 0))
    (model : ∀ j, IntermediateFourierModel ((A j).indicator (fun _ => (1 : ℝ)))
      (fun n => (m j : ℕ) * N n) L V) :
    ∃ σ : ℕ → ℕ, StrictMono σ ∧
      ∀ᵐ t : ℝ ∂volume, 0 < t → ∀ j, t < (m j : ℕ) →
        ∃ q : ℕ → ℕ+,
          (∀ n, H (σ n) ≤ (q n : ℕ)) ∧
          Tendsto (fun n => (q n : ℕ)) atTop atTop ∧
          Tendsto (fun n => (((q n : ℕ) - H (σ n) : ℕ) : ℝ) / (q n : ℕ))
            atTop (𝓝 0) ∧
          (∀ d : ℕ, 0 < d → ∀ᶠ n in atTop, d ∣ (q n : ℕ)) ∧
          (∀ᶠ n in atTop,
            ⌊t * (N (σ n) : ℝ)⌋₊ + 3 * H (σ n) + (q n : ℕ) ≤
              (m j : ℕ) * N (σ n)) ∧
          Tendsto (fun n => convolutionTranslationError (A j) (B j)
            (⌊t * (N (σ n) : ℝ)⌋₊ + 3 * H (σ n)) (q n : ℕ) /
            ((q n : ℕ) : ℝ) ^ 2) atTop (𝓝 0) := by
  classical
  obtain ⟨σ, Q, ε, hσ, hεpos, hεlim, hQ, hdiv, hsample⟩ :=
    exists_ae_prescribed_window_error_data A B N L V H m hNpos hN hHpos hH
      hLH hHV hHN model
  refine ⟨σ, hσ, ?_⟩
  have hHNσ : Tendsto (fun n => (H (σ n) : ℝ) / N (σ n)) atTop (𝓝 0) :=
    hHN.comp hσ.tendsto_atTop
  filter_upwards [hsample] with t ht
  intro htpos j htj
  let start := fun n => ⌊t * (N (σ n) : ℝ)⌋₊
  have hinside : ∀ᶠ n in atTop, start n + 6 * H (σ n) ≤ (m j : ℕ) * N (σ n) :=
    sampled_start_add_six_windows_le (N ∘ σ) (H ∘ σ) (fun n => hNpos (σ n))
      hHNσ (m j : ℕ) t htpos htj
  obtain ⟨q, hq⟩ := joint_convolution_windows_from_selected_errors
    (fun _ : Unit => A j) (fun _ : Unit => B j)
    (fun n => (m j : ℕ) * N (σ n)) (H ∘ σ) start
    (fun n => hHpos (σ n)) (hH.comp hσ.tendsto_atTop) hinside
    (fun _ : Unit => Q j) (fun _ : Unit => ε j)
    (fun _ n => (hεpos j n).le) (fun _ => hεlim j)
    (fun _ => hQ j) (fun _ => hdiv j) (fun _ => ht htpos j htj)
  exact ⟨q (), hq ()⟩

end Erdos335.PeriodicRefinement

end
