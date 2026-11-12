import Erdos335.AsymptoticPolynomialPeriods

/-!
# Asymptotic periods with vanishing relative error and eventual divisibility
-/

set_option autoImplicit false

open Filter Topology Finset
open scoped BigOperators

namespace Erdos335.IntermediateScale

theorem exists_asymptotic_structured_periods
    (R : ℕ) (hR : 0 < R) (w : ℕ → ℝ) (hw : ∀ n, w n ∈ Set.Icc (0 : ℝ) 1)
    (d : ℕ → ℕ) (c : ∀ k, ℕ → Fin (d k) → ℂ) (α : ∀ k, ℕ → Fin (d k) → ℝ)
    (hc : ∀ k n i, ‖c k n i‖ ≤ 1)
    (N H : ℕ → ℕ) (hN : ∀ s, 0 < N s) (hH : Tendsto H atTop atTop)
    (hscale : Tendsto (fun s => (H s : ℝ) / N s) atTop (𝓝 0))
    (happrox : ∀ δ > 0, ∃ k : ℕ, ∀ᶠ s in atTop,
      (∑ n ∈ range (N s), ‖(w n : ℂ) - variableFrequencyPolynomial (c k) (α k) n‖ ^ 2) /
        N s ≤ δ ^ 2)
    (hparameters : ∀ k, Tendsto (fun s =>
      ((varyingPolynomialParameters (N s) (3 * (R * H s)) (c k) (α k)).card : ℝ) / N s) atTop (𝓝 0))
    (hfrequency : ∀ k K : ℕ, 0 < K → Tendsto (fun s =>
      ((badFrequencyCombinationWindows (N s) (H s) K (α k)).card : ℝ) / N s) atTop (𝓝 0)) :
    ∃ (Q : ℕ → ℕ → ℕ) (ε : ℕ → ℝ),
      (∀ s, 0 < ε s) ∧ Tendsto ε atTop (𝓝 0) ∧
      (∀ᶠ s in atTop, ∀ n, H s ≤ Q s n ∧ (Q s n : ℝ) ≤ (1 + ε s) * H s) ∧
      (∀ M : ℕ, 0 < M → ∀ᶠ s in atTop, ∀ n, M ∣ Q s n) ∧
      Tendsto (fun s => averagedWindowTranslationError (fun n => (w n : ℂ))
        (Q s) (N s) (R * H s)) atTop (𝓝 0) := by
  classical
  let e : ℕ → ℝ := fun k => 1 / ((k : ℝ) + 1)
  have hepos (k : ℕ) : 0 < e k := by dsimp [e]; positivity
  have hele (k : ℕ) : e k ≤ 1 := by
    dsimp [e]
    apply (div_le_one (by positivity : (0 : ℝ) < (k : ℝ) + 1)).mpr
    linarith [Nat.cast_nonneg (α := ℝ) k]
  let P : ℕ → ℕ → Prop := fun k s => ∃ Q : ℕ → ℕ,
    (∀ n, Nat.factorial (k + 1) ∣ Q n ∧ H s ≤ Q n ∧ (Q n : ℝ) < (1 + e k) * H s) ∧
    averagedWindowTranslationError (fun n => (w n : ℂ)) Q (N s) (R * H s) < e k
  have hP (k : ℕ) : ∀ᶠ s in atTop, P k s :=
    eventually_exists_structured_periods R hR w hw d c α hc N H hN hH hscale happrox hparameters
      hfrequency (Nat.factorial (k + 1)) (Nat.factorial_pos _) (e k) (e k)
      (hepos k) (hele k) (hepos k)
  obtain ⟨k, hk, hkle, hslow⟩ := exists_slow_index_for_eventual_property P hP
  let Q : ℕ → ℕ → ℕ := fun s => if hs : P (k s) s then hs.choose else fun _ => H s
  have hQ : ∀ᶠ s in atTop,
      (∀ n, Nat.factorial (k s + 1) ∣ Q s n ∧ H s ≤ Q s n ∧
        (Q s n : ℝ) < (1 + e (k s)) * H s) ∧
      averagedWindowTranslationError (fun n => (w n : ℂ)) (Q s) (N s) (R * H s) < e (k s) := by
    filter_upwards [hslow] with s hs
    simpa only [Q, dif_pos hs] using hs.choose_spec
  have he : Tendsto (fun s => e (k s)) atTop (𝓝 0) :=
    tendsto_one_div_add_atTop_nhds_zero_nat.comp hk
  refine ⟨Q, fun s => e (k s), fun s => hepos (k s), he, ?_, ?_, ?_⟩
  · filter_upwards [hQ] with s hs
    exact fun n => ⟨(hs.1 n).2.1, (hs.1 n).2.2.le⟩
  · intro M hM
    filter_upwards [hQ, hk.eventually (eventually_ge_atTop M)] with s hs hMk
    intro n
    exact (Nat.dvd_factorial hM (by omega)).trans (hs.1 n).1
  · apply squeeze_zero' (Eventually.of_forall fun s => by
      unfold averagedWindowTranslationError
      positivity) (hQ.mono fun s hs => hs.2.le) he

end Erdos335.IntermediateScale
