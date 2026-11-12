import Erdos335.PeriodicRefinementActualMacroWindows
import Erdos335.PeriodicRefinementCrossWindows

/-!
# Cross inequalities for actual derivative profiles

Private proof development. Verification status is recorded separately.
Positive window mass supplies the actual translating element at each scale.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Filter Set Topology
open Erdos335.IntermediateScale
open scoped Pointwise

noncomputable section

namespace Erdos335.PeriodicRefinement

theorem exists_literal_residue_window_sequence
    (B : Set ℕ) (m : ℕ+) (v : ZMod (m : ℕ))
    (q : ℕ → ℕ+) (start : ℕ → ℕ) (b : ℝ) (hb : 0 < b)
    (hcount : Tendsto (fun n =>
      ((cyclicWindow {k : ℕ | k ∈ B ∧ (k : ZMod (m : ℕ)) = v}
        (start n) (q n : ℕ)).card : ℝ) / (q n : ℕ)) atTop (𝓝 b)) :
    ∃ point : ℕ → ℕ, ∀ᶠ n in atTop,
      point n ∈ B ∧ (point n : ZMod (m : ℕ)) = v ∧
      start n ≤ point n ∧ point n < start n + (q n : ℕ) := by
  classical
  have hpositive : ∀ᶠ n in atTop, 0 <
      (cyclicWindow {k : ℕ | k ∈ B ∧ (k : ZMod (m : ℕ)) = v}
        (start n) (q n : ℕ)).card := by
    filter_upwards [hcount.eventually (lt_mem_nhds hb)] with n hn
    by_contra h
    have hz : (cyclicWindow {k : ℕ | k ∈ B ∧ (k : ZMod (m : ℕ)) = v}
        (start n) (q n : ℕ)).card = 0 := by omega
    rw [hz, Nat.cast_zero, zero_div] at hn
    exact (lt_irrefl (0 : ℝ)) hn
  let point : ℕ → ℕ := fun n =>
    if hn : 0 < (cyclicWindow {k : ℕ | k ∈ B ∧ (k : ZMod (m : ℕ)) = v}
        (start n) (q n : ℕ)).card then
      Classical.choose (exists_literal_window_element B m (q n) v (start n) hn)
    else 0
  refine ⟨point, ?_⟩
  filter_upwards [hpositive] with n hn
  simpa only [point, dif_pos hn] using
    Classical.choose_spec (exists_literal_window_element B m (q n) v (start n) hn)

theorem derivative_residue_cross_le
    (A B : Set ℕ) (m : ℕ+) (r v : ZMod (m : ℕ))
    (FA FB FC : ℝ → ℝ) (N H : ℕ → ℕ) (L t u a b c : ℝ)
    (hN : ∀ n, 0 < N n) (hH : ∀ n, 0 < H n)
    (hscale : Tendsto (fun n => (H n : ℝ) / N n) atTop (𝓝 0))
    (happroxA : UniformCumulativeApproximation
      {k : ℕ | k ∈ A ∧ (k : ZMod (m : ℕ)) = r} FA N H L)
    (happroxB : UniformCumulativeApproximation
      {k : ℕ | k ∈ B ∧ (k : ZMod (m : ℕ)) = v} FB N H L)
    (happroxC : UniformCumulativeApproximation
      {k : ℕ | k ∈ A + B ∧ (k : ZMod (m : ℕ)) = r + v} FC N H L)
    (ht : 0 < t) (hu : 0 < u) (htu : t + u < L)
    (hFA : HasDerivAt FA a t) (hFB : HasDerivAt FB b u)
    (hFC : HasDerivAt FC c (t + u)) (hb : 0 < b) :
    a ≤ c := by
  classical
  letI (n : ℕ) : NeZero (H n) := ⟨(hH n).ne'⟩
  let q : ℕ → ℕ+ := fun n => ⟨H n, hH n⟩
  let startA : ℕ → ℕ := fun n => Nat.floor (t * N n)
  let startB : ℕ → ℕ := fun n => Nat.floor (u * N n)
  have hAcount := actual_macro_floor_density
    {k : ℕ | k ∈ A ∧ (k : ZMod (m : ℕ)) = r} FA N H L t a
      hN hH hscale happroxA ht (by linarith) hFA
  have hBcount := actual_macro_floor_density
    {k : ℕ | k ∈ B ∧ (k : ZMod (m : ℕ)) = v} FB N H L u b
      hN hH hscale happroxB hu (by linarith) hFB
  have hBq : Tendsto (fun n =>
      ((cyclicWindow {k : ℕ | k ∈ B ∧ (k : ZMod (m : ℕ)) = v}
        (startB n) (q n : ℕ)).card : ℝ) / (q n : ℕ)) atTop (𝓝 b) := by
    change Tendsto (fun n =>
      ((cyclicWindow {k : ℕ | k ∈ B ∧ (k : ZMod (m : ℕ)) = v}
        (Nat.floor (u * N n)) (H n)).card : ℝ) / H n) atTop (𝓝 b)
    exact hBcount
  obtain ⟨point, hpoint⟩ := exists_literal_residue_window_sequence B m v q startB b hb hBq
  have hpointBounds : ∀ᶠ n in atTop,
      Nat.floor (u * N n) ≤ point n ∧ point n < Nat.floor (u * N n) + H n := by
    filter_upwards [hpoint] with n hn
    exact ⟨hn.2.2.1, hn.2.2.2⟩
  have htargetStart := macro_cross_start_bound N H point hH t u ht.le hu.le hpointBounds
  have hCcount := actual_macro_window_density
    {k : ℕ | k ∈ A + B ∧ (k : ZMod (m : ℕ)) = r + v} FC N H
      (fun n => startA n + point n) L (t + u) c 3 hN hH hscale happroxC
        (by linarith) htu hFC htargetStart
  have hAprofile : Tendsto (fun n => ((m : ℕ) : ℝ) *
      ((cyclicWindow {k : ℕ | k ∈ A ∧ (k : ZMod (m : ℕ)) = r}
        (startA n) (q n : ℕ)).card : ℝ) / (q n : ℕ))
      atTop (𝓝 (((m : ℕ) : ℝ) * a)) := by
    change Tendsto (fun n => ((m : ℕ) : ℝ) *
      ((cyclicWindow {k : ℕ | k ∈ A ∧ (k : ZMod (m : ℕ)) = r}
        (Nat.floor (t * N n)) (H n)).card : ℝ) / H n)
      atTop (𝓝 (((m : ℕ) : ℝ) * a))
    simpa only [mul_div_assoc] using hAcount.const_mul ((m : ℕ) : ℝ)
  have hCprofile : Tendsto (fun n => ((m : ℕ) : ℝ) *
      ((cyclicWindow {k : ℕ | k ∈ A + B ∧ (k : ZMod (m : ℕ)) = r + v}
        (startA n + point n) (q n : ℕ)).card : ℝ) / (q n : ℕ))
      atTop (𝓝 (((m : ℕ) : ℝ) * c)) := by
    change Tendsto (fun n => ((m : ℕ) : ℝ) *
      ((cyclicWindow {k : ℕ | k ∈ A + B ∧ (k : ZMod (m : ℕ)) = r + v}
        (startA n + point n) (H n)).card : ℝ) / H n)
      atTop (𝓝 (((m : ℕ) : ℝ) * c))
    simpa only [mul_div_assoc] using hCcount.const_mul ((m : ℕ) : ℝ)
  have hcross := residue_cross_profile_le A B m q r v startA point
    (((m : ℕ) : ℝ) * a) (((m : ℕ) : ℝ) * c)
    (hpoint.mono fun n hn => ⟨hn.1, hn.2.1⟩) hAprofile hCprofile
  exact le_of_mul_le_mul_left hcross (by exact_mod_cast m.pos)

theorem derivative_residue_cross_max
    (A B : Set ℕ) (m : ℕ+) (r v : ZMod (m : ℕ))
    (FA FB FC : ℝ → ℝ) (N H : ℕ → ℕ) (L t u a b c : ℝ)
    (hN : ∀ n, 0 < N n) (hH : ∀ n, 0 < H n)
    (hscale : Tendsto (fun n => (H n : ℝ) / N n) atTop (𝓝 0))
    (happroxA : UniformCumulativeApproximation
      {k : ℕ | k ∈ A ∧ (k : ZMod (m : ℕ)) = r} FA N H L)
    (happroxB : UniformCumulativeApproximation
      {k : ℕ | k ∈ B ∧ (k : ZMod (m : ℕ)) = v} FB N H L)
    (happroxC : UniformCumulativeApproximation
      {k : ℕ | k ∈ A + B ∧ (k : ZMod (m : ℕ)) = r + v} FC N H L)
    (ht : 0 < t) (hu : 0 < u) (htu : t + u < L)
    (hFA : HasDerivAt FA a t) (hFB : HasDerivAt FB b u)
    (hFC : HasDerivAt FC c (t + u)) (ha : 0 < a) (hb : 0 < b) :
    max a b ≤ c := by
  have hleft := derivative_residue_cross_le A B m r v FA FB FC N H L t u a b c
    hN hH hscale happroxA happroxB happroxC ht hu htu hFA hFB hFC hb
  have hright := derivative_residue_cross_le B A m v r FB FA FC N H L u t b a c
    hN hH hscale happroxB happroxA
    (by simpa only [add_comm B A, add_comm v r] using happroxC)
    hu ht (by simpa only [add_comm u t] using htu) hFB hFA
    (by simpa only [add_comm u t] using hFC) ha
  exact max_le hleft hright

end Erdos335.PeriodicRefinement

end
