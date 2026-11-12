import Erdos335.PeriodicRefinementCumulative
import Erdos335.PeriodicRefinementDerivativeWindows
import Erdos335.CyclicWindowDensities

/-!
# Actual counting windows near a differentiability point

Private proof development. Verification status is recorded separately.
The cumulative approximation error is measured relative to H/N.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Filter Set Topology Asymptotics
open Erdos335.IntermediateScale

noncomputable section

namespace Erdos335.PeriodicRefinement

structure UniformCumulativeApproximation
    (S : Set ℕ) (F : ℝ → ℝ) (N H : ℕ → ℕ) (L : ℝ) where
  cumulative : ℝ → ℝ
  agreesOnNaturals : ∀ k : ℕ, cumulative k = prefixCount S k
  error : ℕ → ℝ
  error_small : Tendsto (fun n => error n * (N n : ℝ) / H n) atTop (𝓝 0)
  bound : ∀ᶠ n in atTop, ∀ t ∈ Icc (0 : ℝ) L,
    |cumulative (t * N n) / N n - F t| ≤ error n

theorem macro_start_normalized_bound
    (N H start : ℕ → ℕ) (hN : ∀ n, 0 < N n)
    (x K : ℝ)
    (hstart : ∀ᶠ n in atTop, |(start n : ℝ) - x * N n| ≤ K * H n) :
    ∀ᶠ n in atTop,
      |(start n : ℝ) / N n - x| ≤ K * ((H n : ℝ) / N n) := by
  filter_upwards [hstart] with n hn
  have hNr : (0 : ℝ) < N n := by exact_mod_cast hN n
  have heq : (start n : ℝ) / N n - x = ((start n : ℝ) - x * N n) / N n := by
    field_simp [hNr.ne']
  rw [heq, abs_div, abs_of_pos hNr]
  simpa only [mul_div_assoc] using div_le_div_of_nonneg_right hn hNr.le

theorem actual_macro_window_density
    (S : Set ℕ) (F : ℝ → ℝ) (N H start : ℕ → ℕ) (L x d K : ℝ)
    (hN : ∀ n, 0 < N n) (hH : ∀ n, 0 < H n)
    (hscale : Tendsto (fun n => (H n : ℝ) / N n) atTop (𝓝 0))
    (happrox : UniformCumulativeApproximation S F N H L)
    (hx : 0 < x) (hxL : x < L) (hderiv : HasDerivAt F d x)
    (hstart : ∀ᶠ n in atTop, |(start n : ℝ) - x * N n| ≤ K * H n) :
    Tendsto (fun n =>
      ((@cyclicWindow S (start n) (H n) ⟨(hH n).ne'⟩).card : ℝ) / H n)
      atTop (𝓝 d) := by
  letI (n : ℕ) : NeZero (H n) := ⟨(hH n).ne'⟩
  let u := fun n => (start n : ℝ) / N n
  let v := fun n => ((start n + H n : ℕ) : ℝ) / N n
  let h := fun n => (H n : ℝ) / N n
  let G := fun n t => happrox.cumulative (t * N n) / N n
  have hhpos (n : ℕ) : 0 < h n := by
    exact div_pos (by exact_mod_cast hH n) (by exact_mod_cast hN n)
  have hboundu : ∀ᶠ n in atTop, |u n - x| ≤ K * h n :=
    macro_start_normalized_bound N H start hN x K hstart
  have hgap (n : ℕ) : v n - u n = h n := by
    dsimp only [u, v, h]
    rw [Nat.cast_add]
    ring
  have hboundv : ∀ᶠ n in atTop, |v n - x| ≤ (K + 1) * h n := by
    filter_upwards [hboundu] with n hn
    have heq : v n - x = (u n - x) + h n := by linarith [hgap n]
    rw [heq]
    calc
      |u n - x + h n| ≤ |u n - x| + |h n| := abs_add_le _ _
      _ ≤ K * h n + h n := by rw [abs_of_pos (hhpos n)]; linarith
      _ = (K + 1) * h n := by ring
  have huO : (fun n => u n - x) =O[atTop] h := by
    apply IsBigO.of_bound K
    filter_upwards [hboundu] with n hn
    simpa only [Real.norm_eq_abs, abs_of_pos (hhpos n)] using hn
  have hvO : (fun n => v n - x) =O[atTop] h := by
    apply IsBigO.of_bound (K + 1)
    filter_upwards [hboundv] with n hn
    simpa only [Real.norm_eq_abs, abs_of_pos (hhpos n)] using hn
  have hu : Tendsto u atTop (𝓝 x) := by
    have hlim := (huO.trans_tendsto hscale).add_const x
    simpa only [sub_add_cancel, zero_add] using hlim
  have hv : Tendsto v atTop (𝓝 x) := by
    have hlim := (hvO.trans_tendsto hscale).add_const x
    simpa only [sub_add_cancel, zero_add] using hlim
  have huinside : ∀ᶠ n in atTop, u n ∈ Icc (0 : ℝ) L := by
    filter_upwards [hu.eventually (lt_mem_nhds hx), hu.eventually (gt_mem_nhds hxL)]
      with n hn0 hnL
    exact ⟨hn0.le, hnL.le⟩
  have hvinside : ∀ᶠ n in atTop, v n ∈ Icc (0 : ℝ) L := by
    filter_upwards [hv.eventually (lt_mem_nhds hx), hv.eventually (gt_mem_nhds hxL)]
      with n hn0 hnL
    exact ⟨hn0.le, hnL.le⟩
  have endpoint_error (z : ℕ → ℝ) (hz : ∀ᶠ n in atTop, z n ∈ Icc (0 : ℝ) L) :
      Tendsto (fun n => (G n (z n) - F (z n)) / h n) atTop (𝓝 0) := by
    have habs : Tendsto (fun n => |(G n (z n) - F (z n)) / h n|) atTop (𝓝 0) := by
      apply squeeze_zero' (Eventually.of_forall fun _ => abs_nonneg _) ?_ happrox.error_small
      filter_upwards [hz, happrox.bound] with n hn hbound
      rw [abs_div, abs_of_pos (hhpos n)]
      have he := div_le_div_of_nonneg_right (hbound (z n) hn) (hhpos n).le
      have hNr : (N n : ℝ) ≠ 0 := by exact_mod_cast (hN n).ne'
      have hHr : (H n : ℝ) ≠ 0 := by exact_mod_cast (hH n).ne'
      convert he using 1 <;> dsimp only [G, h] <;> field_simp [hNr, hHr] <;> ring
    apply (tendsto_zero_iff_norm_tendsto_zero).mpr
    simpa only [Real.norm_eq_abs] using habs
  have hlim := moving_approximate_derivative_window_tendsto hderiv G u v h
    hu hv huO hvO (Eventually.of_forall hgap)
    (Eventually.of_forall fun n => (hhpos n).ne')
    (endpoint_error u huinside) (endpoint_error v hvinside)
  apply hlim.congr
  intro n
  have hNr : (N n : ℝ) ≠ 0 := by exact_mod_cast (hN n).ne'
  have hHr : (H n : ℝ) ≠ 0 := by exact_mod_cast (hH n).ne'
  dsimp only [G, u, v, h]
  rw [div_mul_cancel₀ _ hNr, div_mul_cancel₀ _ hNr,
    happrox.agreesOnNaturals, happrox.agreesOnNaturals,
    prefixCount_add_tailShift, Nat.cast_add, cyclicWindow_card_eq_prefixCount]
  field_simp [hNr, hHr] <;> ring

theorem macro_floor_shift_bound
    (N H start : ℕ → ℕ) (hH : ∀ n, 0 < H n) (x K : ℝ) (hx : 0 ≤ x)
    (hshift : ∀ᶠ n in atTop,
      |(start n : ℝ) - (Nat.floor (x * N n) : ℝ)| ≤ K * H n) :
    ∀ᶠ n in atTop,
      |(start n : ℝ) - x * N n| ≤ (K + 1) * H n := by
  filter_upwards [hshift] with n hn
  have hfloor : |(Nat.floor (x * N n) : ℝ) - x * N n| ≤ 1 := by
    have hlo := Nat.floor_le (mul_nonneg hx (Nat.cast_nonneg (N n)))
    have hhi := Nat.lt_floor_add_one (x * N n)
    rw [abs_of_nonpos (sub_nonpos.mpr hlo)]
    linarith
  have hHone : (1 : ℝ) ≤ H n := by exact_mod_cast hH n
  calc
    |(start n : ℝ) - x * N n| =
        |((start n : ℝ) - (Nat.floor (x * N n) : ℝ)) +
          ((Nat.floor (x * N n) : ℝ) - x * N n)| := by congr 1; ring
    _ ≤ |(start n : ℝ) - (Nat.floor (x * N n) : ℝ)| +
        |(Nat.floor (x * N n) : ℝ) - x * N n| := abs_add_le _ _
    _ ≤ (K + 1) * H n := by nlinarith

theorem actual_macro_floor_window_density
    (S : Set ℕ) (F : ℝ → ℝ) (N H start : ℕ → ℕ) (L x d K : ℝ)
    (hN : ∀ n, 0 < N n) (hH : ∀ n, 0 < H n)
    (hscale : Tendsto (fun n => (H n : ℝ) / N n) atTop (𝓝 0))
    (happrox : UniformCumulativeApproximation S F N H L)
    (hx : 0 < x) (hxL : x < L) (hderiv : HasDerivAt F d x)
    (hshift : ∀ᶠ n in atTop,
      |(start n : ℝ) - (Nat.floor (x * N n) : ℝ)| ≤ K * H n) :
    Tendsto (fun n =>
      ((@cyclicWindow S (start n) (H n) ⟨(hH n).ne'⟩).card : ℝ) / H n)
      atTop (𝓝 d) :=
  actual_macro_window_density S F N H start L x d (K + 1) hN hH hscale happrox
    hx hxL hderiv (macro_floor_shift_bound N H start hH x K hx.le hshift)

theorem actual_macro_floor_density
    (S : Set ℕ) (F : ℝ → ℝ) (N H : ℕ → ℕ) (L x d : ℝ)
    (hN : ∀ n, 0 < N n) (hH : ∀ n, 0 < H n)
    (hscale : Tendsto (fun n => (H n : ℝ) / N n) atTop (𝓝 0))
    (happrox : UniformCumulativeApproximation S F N H L)
    (hx : 0 < x) (hxL : x < L) (hderiv : HasDerivAt F d x) :
    Tendsto (fun n =>
      ((@cyclicWindow S (Nat.floor (x * N n)) (H n) ⟨(hH n).ne'⟩).card : ℝ) / H n)
      atTop (𝓝 d) := by
  apply actual_macro_floor_window_density S F N H (fun n => Nat.floor (x * N n))
    L x d 0 hN hH hscale happrox hx hxL hderiv
  exact Eventually.of_forall fun n => by simp

theorem macro_cross_start_bound
    (N H b : ℕ → ℕ) (hH : ∀ n, 0 < H n) (t u : ℝ)
    (ht : 0 ≤ t) (hu : 0 ≤ u)
    (hb : ∀ᶠ n in atTop, Nat.floor (u * N n) ≤ b n ∧
      b n < Nat.floor (u * N n) + H n) :
    ∀ᶠ n in atTop,
      |((Nat.floor (t * N n) + b n : ℕ) : ℝ) - (t + u) * N n| ≤ 3 * H n := by
  filter_upwards [hb] with n hn
  have htlo := Nat.floor_le (mul_nonneg ht (Nat.cast_nonneg (N n)))
  have hthi := Nat.lt_floor_add_one (t * N n)
  have hulo := Nat.floor_le (mul_nonneg hu (Nat.cast_nonneg (N n)))
  have huhi := Nat.lt_floor_add_one (u * N n)
  have hbLo : (Nat.floor (u * N n) : ℝ) ≤ b n := by exact_mod_cast hn.1
  have hbHi : (b n : ℝ) < (Nat.floor (u * N n) : ℝ) + H n := by exact_mod_cast hn.2
  have hHone : (1 : ℝ) ≤ H n := by exact_mod_cast hH n
  rw [Nat.cast_add, abs_le]
  constructor <;> nlinarith

end Erdos335.PeriodicRefinement

end
