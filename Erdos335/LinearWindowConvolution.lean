import Erdos335.CyclicWindowFourier

/-!
# Embedding a linear window convolution in a finite cyclic group
-/

set_option autoImplicit false

open Finset
open scoped BigOperators

namespace Erdos335.IntermediateScale

noncomputable def linearWindowConvolution (r : ℕ → ℝ) (g : ℕ → ℂ) (H n : ℕ) : ℂ :=
  (∑ m ∈ range H, (r (n - m) : ℂ) * g m) / (H : ℂ)

noncomputable def cyclicInput (g : ℕ → ℂ) (H M : ℕ) (x : ZMod M) : ℂ :=
  if x.val < H then g x.val else 0

theorem cyclicInput_norm_le (g : ℕ → ℂ) (H M : ℕ) (hg : ∀ m, ‖g m‖ ≤ 1)
    (x : ZMod M) : ‖cyclicInput g H M x‖ ≤ 1 := by
  unfold cyclicInput
  split_ifs
  · exact hg _
  · simp

theorem linearWindowConvolution_cyclic (r : ℕ → ℝ) (g : ℕ → ℂ)
    (n H i : ℕ) (hH : 0 < H) (hi : i < H) :
    letI : NeZero (4 * H) := ⟨by omega⟩
    linearWindowConvolution r g H (n + H + i) =
      4 * Erdos335.FiniteFourier.convolution (cyclicFourierWindow r n (2 * H) (4 * H))
        (cyclicInput g H (4 * H)) ((H + i : ℕ) : ZMod (4 * H)) := by
  let : NeZero (4 * H) := ⟨by omega⟩
  have hfilter : (range (4 * H)).filter (fun m => m < H) = range H := by
    ext m
    simp only [mem_filter, mem_range]
    omega
  have hsum : (∑ x : ZMod (4 * H), cyclicInput g H (4 * H) x *
      cyclicFourierWindow r n (2 * H) (4 * H) (((H + i : ℕ) : ZMod (4 * H)) - x)) =
      ∑ m ∈ range H, (r (n + H + i - m) : ℂ) * g m := by
    rw [sum_zmod_eq_range]
    calc
      _ = ∑ m ∈ range (4 * H), if m < H then (r (n + H + i - m) : ℂ) * g m else 0 := by
        apply sum_congr rfl
        intro m hm
        have hm4 : m < 4 * H := mem_range.mp hm
        by_cases hmH : m < H
        · have hmle : m ≤ H + i := by omega
          have hz : ((H + i : ℕ) : ZMod (4 * H)) - (m : ZMod (4 * H)) =
              ((H + i - m : ℕ) : ZMod (4 * H)) := (Nat.cast_sub hmle).symm
          have hd4 : H + i - m < 4 * H := by omega
          have hd2 : H + i - m < 2 * H := by omega
          have hadd : n + (H + i - m) = n + H + i - m := by omega
          simp only [cyclicInput, ZMod.val_cast_of_lt hm4, hmH, ite_true, hz,
            cyclicFourierWindow, ZMod.val_cast_of_lt hd4, hd2, hadd]
          ring
        · simp only [cyclicInput, ZMod.val_cast_of_lt hm4, hmH, ite_false, zero_mul]
      _ = ∑ m ∈ (range (4 * H)).filter (fun m => m < H),
          (r (n + H + i - m) : ℂ) * g m := by rw [sum_filter]
      _ = _ := by rw [hfilter]
  rw [Erdos335.FiniteFourier.convolution_comm,
    Erdos335.FiniteFourier.convolution, Fintype.expect_eq_sum_div_card, ZMod.card, hsum]
  unfold linearWindowConvolution
  have hHC : (H : ℂ) ≠ 0 := by exact_mod_cast hH.ne'
  push_cast
  field_simp

theorem sum_zmod_eq_range_real {M : ℕ} [NeZero M] (f : ZMod M → ℝ) :
    (∑ x : ZMod M, f x) = ∑ i ∈ range M, f (i : ZMod M) := by
  have h := sum_zmod_eq_range (fun x : ZMod M => (f x : ℂ))
  exact_mod_cast h

theorem linear_window_convolution_average_le (r : ℕ → ℝ) (g : ℕ → ℂ)
    (hg : ∀ m, ‖g m‖ ≤ 1) (n H : ℕ) (hH : 0 < H) :
    (∑ i ∈ range H, ‖linearWindowConvolution r g H (n + H + i)‖) / H ≤
      16 * windowFourierNorm r n (2 * H) := by
  let : NeZero (4 * H) := ⟨by omega⟩
  let v : ZMod (4 * H) → ℂ := Erdos335.FiniteFourier.convolution
    (cyclicFourierWindow r n (2 * H) (4 * H)) (cyclicInput g H (4 * H))
  have hcyc := cyclicFourierWindow_convolution_l1_le r n (2 * H) (4 * H)
    (by omega) (by omega) (cyclicInput g H (4 * H)) (cyclicInput_norm_le g H (4 * H) hg)
  have hsub : (∑ i ∈ range H, ‖v ((H + i : ℕ) : ZMod (4 * H))‖) ≤
      ∑ x : ZMod (4 * H), ‖v x‖ := by
    rw [sum_zmod_eq_range_real]
    have hsplit := sum_range_add (fun j => ‖v (j : ZMod (4 * H))‖) H H
    have hfirst : (∑ i ∈ range H, ‖v ((H + i : ℕ) : ZMod (4 * H))‖) ≤
        ∑ i ∈ range (2 * H), ‖v (i : ZMod (4 * H))‖ := by
      rw [show 2 * H = H + H by omega, hsplit]
      exact le_add_of_nonneg_left (sum_nonneg fun j hj => norm_nonneg _)
    exact hfirst.trans (sum_le_sum_of_subset_of_nonneg (range_mono (by omega))
      (fun j hj hjnot => norm_nonneg _))
  have hHr : (0 : ℝ) < H := by exact_mod_cast hH
  have htotal : (∑ x : ZMod (4 * H), ‖v x‖) ≤
      windowFourierNorm r n (2 * H) * (4 * H) := by
    simpa only [v, Nat.cast_mul, Nat.cast_ofNat] using
      (div_le_iff₀ (by positivity : (0 : ℝ) < (4 * H : ℕ))).mp hcyc
  apply (div_le_iff₀ hHr).mpr
  calc
    _ = 4 * (∑ i ∈ range H, ‖v ((H + i : ℕ) : ZMod (4 * H))‖) := by
      rw [mul_sum]
      apply sum_congr rfl
      intro i hi
      rw [linearWindowConvolution_cyclic r g n H i hH (mem_range.mp hi), norm_mul]
      norm_num [v]
    _ ≤ 4 * (windowFourierNorm r n (2 * H) * (4 * H)) :=
      mul_le_mul_of_nonneg_left (hsub.trans htotal) (by norm_num)
    _ = _ := by ring

end Erdos335.IntermediateScale
