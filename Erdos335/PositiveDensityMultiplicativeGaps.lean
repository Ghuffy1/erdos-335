import Erdos335.IntermediateScale

/-!
# Multiplicative gaps in a set of positive ordinary density

Privately checked supporting development.
A sublinear prefix-error envelope controls a short proportional interval.
-/

set_option autoImplicit false

open Filter Set Topology

namespace Erdos335

theorem positive_density_multiplicative_gap
    (A : Set ℕ) (a : ℝ) (hA : HasDensity A a) (ha : 0 < a)
    (ε : ℝ) (hε : 0 < ε) :
    ∀ᶠ N : ℕ in atTop, ∃ n ∈ A, N < n ∧ (n : ℝ) ≤ (1 + ε) * N := by
  classical
  let η : ℝ := min (ε / 2) (1 / 2)
  have hη : 0 < η := by
    dsimp only [η]
    exact lt_min (by positivity) (by norm_num)
  have hηε : η ≤ ε / 2 := min_le_left _ _
  have hηhalf : η ≤ (1 / 2 : ℝ) := min_le_right _ _
  have herror : Tendsto (fun N : ℕ => prefixError A a (2 * N) / N) atTop (𝓝 0) := by
    simpa using (hA.prefixError_mul_tendsto_zero (2 : ℕ+))
  have hmargin : 0 < a * η / 4 := by positivity
  filter_upwards [herror.eventually (gt_mem_nhds hmargin),
    (tendsto_const_div_atTop_nhds_zero_nat (1 : ℝ)).eventually (gt_mem_nhds hη),
    eventually_ge_atTop 1] with N herrorN hscaleN hN
  have hNpos : 0 < N := by omega
  have hNr : (0 : ℝ) < N := by exact_mod_cast hNpos
  have hone : 1 < η * (N : ℝ) := (div_lt_iff₀ hNr).mp hscaleN
  let L : ℕ := Nat.ceil (η * (N : ℝ))
  have hLlower : η * (N : ℝ) ≤ (L : ℝ) := Nat.le_ceil _
  have hLupper : (L : ℝ) < η * (N : ℝ) + 1 :=
    Nat.ceil_lt_add_one (mul_nonneg hη.le hNr.le)
  have hLN : (L : ℝ) ≤ N := by
    nlinarith [mul_le_mul_of_nonneg_right hηhalf hNr.le]
  have hLε : (L : ℝ) ≤ ε * (N : ℝ) := by
    nlinarith [mul_le_mul_of_nonneg_right hηε hNr.le]
  have hinside : N + L ≤ 2 * N := by
    have hLn : L ≤ N := by exact_mod_cast hLN
    omega
  by_contra hnone
  have hno (n : ℕ) (hnA : n ∈ A) (hnN : N < n) (hnL : n ≤ N + L) : False := by
    apply hnone
    refine ⟨n, hnA, hnN, ?_⟩
    have hnR : (n : ℝ) ≤ (N : ℝ) + L := by exact_mod_cast hnL
    nlinarith
  have hcount : count A (N + L) = count A N := by
    unfold count
    apply congrArg Finset.card
    ext n
    simp only [Finset.mem_filter, Finset.mem_Icc]
    constructor
    · rintro ⟨⟨hnpos, hnL⟩, hnA⟩
      by_cases hnN : n ≤ N
      · exact ⟨⟨hnpos, hnN⟩, hnA⟩
      · exact False.elim (hno n hnA (Nat.lt_of_not_ge hnN) hnL)
    · rintro ⟨⟨hnpos, hnN⟩, hnA⟩
      exact ⟨⟨hnpos, by omega⟩, hnA⟩
  have hwindow := window_error_le_prefixError A a hinside
  rw [hcount] at hwindow
  have hdeficit : a * (L : ℝ) ≤ 2 * prefixError A a (2 * N) := by
    have hnegative := (abs_le.mp hwindow).1
    linarith
  have herrorR : prefixError A a (2 * N) < (a * η / 4) * (N : ℝ) :=
    (div_lt_iff₀ hNr).mp herrorN
  have hscaledLower := mul_le_mul_of_nonneg_left hLlower ha.le
  have hpositiveProduct : 0 < a * η * (N : ℝ) := mul_pos (mul_pos ha hη) hNr
  nlinarith

theorem exists_next_point_ratio_tendsto_one
    (A : Set ℕ) (a : ℝ) (hA : HasDensity A a) (ha : 0 < a) :
    ∃ k : ℕ → ℕ, (∀ N, k N ∈ A ∧ N < k N) ∧
      Tendsto (fun N => (k N : ℝ) / N) atTop (𝓝 1) := by
  classical
  obtain ⟨N₀, hN₀⟩ := eventually_atTop.mp
    (positive_density_multiplicative_gap A a hA ha 1 (by norm_num))
  have hfuture (N : ℕ) : ∃ n, n ∈ A ∧ N < n := by
    obtain ⟨n, hnA, hnlarge, _⟩ := hN₀ (max N₀ N) (le_max_left _ _)
    exact ⟨n, hnA, lt_of_le_of_lt (le_max_right _ _) hnlarge⟩
  let k : ℕ → ℕ := fun N => Nat.find (hfuture N)
  have hk (N : ℕ) : k N ∈ A ∧ N < k N := Nat.find_spec (hfuture N)
  have hminimal (N n : ℕ) (hnA : n ∈ A) (hnN : N < n) : k N ≤ n :=
    Nat.find_min' (hfuture N) ⟨hnA, hnN⟩
  refine ⟨k, hk, ?_⟩
  apply tendsto_order.mpr
  constructor
  · intro l hl
    filter_upwards [eventually_ge_atTop 1] with N hN
    have hNr : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
    have hratio : (1 : ℝ) < (k N : ℝ) / N :=
      (one_lt_div hNr).mpr (by exact_mod_cast (hk N).2)
    exact hl.trans hratio
  · intro u hu
    let ε : ℝ := (u - 1) / 2
    have hε : 0 < ε := by dsimp only [ε]; linarith
    filter_upwards [positive_density_multiplicative_gap A a hA ha ε hε,
      eventually_ge_atTop 1] with N hpoint hN
    obtain ⟨n, hnA, hnN, hnupper⟩ := hpoint
    have hNr : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
    have hkn : (k N : ℝ) ≤ n := by exact_mod_cast hminimal N n hnA hnN
    have hratio : (k N : ℝ) / N ≤ 1 + ε :=
      (div_le_iff₀ hNr).mpr (hkn.trans hnupper)
    have hupper : 1 + ε < u := by dsimp only [ε]; linarith
    exact hratio.trans_lt hupper

end Erdos335
