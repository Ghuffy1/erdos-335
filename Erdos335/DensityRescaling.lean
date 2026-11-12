import Erdos335.DensityLimits
import Erdos335.DysonCounting

/-!
# Regular subsequences of density ratios

Uniformly bounded gaps between cutoffs preserve lower density. This permits
exact block counts to be used when residue classes are packed together.
-/

set_option autoImplicit false

open Filter Topology

namespace Erdos335

theorem count_ratio_rounding_error (A : Set ℕ) (q : ℕ+) (N : ℕ) :
    |(count A N : ℝ) / N -
      (count A ((q : ℕ) * (N / (q : ℕ))) : ℝ) / ((q : ℕ) * (N / (q : ℕ)) : ℕ)| ≤
        (q : ℕ) / (N : ℝ) := by
  let M := (q : ℕ) * (N / (q : ℕ))
  change |(count A N : ℝ) / N - (count A M : ℝ) / M| ≤ (q : ℕ) / (N : ℝ)
  have hdiv := Nat.mod_add_div N (q : ℕ)
  have hrem := Nat.mod_lt N q.pos
  have hMN : M ≤ N := by dsimp [M]; omega
  have hNM : N ≤ M + (q : ℕ) := by dsimp [M]; omega
  have hmono := count_mono_cutoff A hMN
  have hstep := (count_mono_cutoff A hNM).trans (count_add_le A M q)
  rcases eq_or_ne N 0 with rfl | hN
  · simp [M]
  have hNR : (0 : ℝ) < N := by exact_mod_cast Nat.pos_of_ne_zero hN
  rcases eq_or_ne M 0 with hM | hM
  · simp only [hM, count_zero, Nat.cast_zero, zero_div, sub_zero,
      abs_of_nonneg (count_ratio_nonneg A N)]
    apply div_le_div_of_nonneg_right _ hNR.le
    have hstep' : count A N ≤ (q : ℕ) := by simpa [hM, count_zero] using hstep
    exact_mod_cast hstep'
  have hMR : (0 : ℝ) < M := by exact_mod_cast Nat.pos_of_ne_zero hM
  have hMNR : (M : ℝ) ≤ N := by exact_mod_cast hMN
  have hcountM : (count A M : ℝ) ≤ M := by exact_mod_cast count_le A M
  have hcount0 : (0 : ℝ) ≤ count A M := by positivity
  have hmonoR : (count A M : ℝ) ≤ count A N := by exact_mod_cast hmono
  have hstepR : (count A N : ℝ) ≤ count A M + (q : ℕ) := by exact_mod_cast hstep
  have hdiff : (N : ℝ) - M ≤ (q : ℕ) := by
    have hNMR : (N : ℝ) ≤ M + (q : ℕ) := by exact_mod_cast hNM
    linarith
  have hup : (count A N : ℝ) / N ≤ (count A M : ℝ) / M + (q : ℕ) / (N : ℝ) := by
    calc
      (count A N : ℝ) / N ≤ (count A M + (q : ℕ) : ℝ) / N :=
        div_le_div_of_nonneg_right hstepR hNR.le
      _ = (count A M : ℝ) / N + (q : ℕ) / (N : ℝ) := add_div _ _ _
      _ ≤ (count A M : ℝ) / M + (q : ℕ) / (N : ℝ) := by gcongr
  have hlo : (count A M : ℝ) / M ≤ (count A N : ℝ) / N + (q : ℕ) / (N : ℝ) := by
    have hprod : (count A M : ℝ) * ((N : ℝ) - M) ≤ (M : ℝ) * (q : ℕ) :=
      mul_le_mul hcountM hdiff (sub_nonneg.mpr hMNR) hMR.le
    calc
      (count A M : ℝ) / M ≤ (count A M + (q : ℕ) : ℝ) / N := by
        apply (div_le_div_iff₀ hMR hNR).mpr
        nlinarith
      _ = (count A M : ℝ) / N + (q : ℕ) / (N : ℝ) := add_div _ _ _
      _ ≤ (count A N : ℝ) / N + (q : ℕ) / (N : ℝ) := by gcongr
  rw [abs_le]
  constructor <;> linarith

theorem count_ratio_rounding_tendsto_zero (A : Set ℕ) (q : ℕ+) :
    Tendsto (fun N : ℕ => (count A N : ℝ) / N -
      (count A ((q : ℕ) * (N / (q : ℕ))) : ℝ) / ((q : ℕ) * (N / (q : ℕ)) : ℕ))
      atTop (𝓝 0) := by
  rw [tendsto_iff_norm_sub_tendsto_zero]
  simp only [sub_zero, Real.norm_eq_abs]
  exact squeeze_zero (fun N => abs_nonneg _) (count_ratio_rounding_error A q)
    (tendsto_const_div_atTop_nhds_zero_nat ((q : ℕ) : ℝ))

theorem liminf_eq_liminf_multiples_of_rounding {u : ℕ → ℝ} (q : ℕ+) {K : ℝ}
    (hlo : ∀ N, 0 ≤ u N) (hhi : ∀ N, u N ≤ K)
    (herr : Tendsto (fun N : ℕ => u N - u ((q : ℕ) * (N / (q : ℕ)))) atTop (𝓝 0)) :
    liminf u atTop = liminf (fun N : ℕ => u ((q : ℕ) * N)) atTop := by
  let v : ℕ → ℝ := fun N => u ((q : ℕ) * (N / (q : ℕ)))
  have hvlo : IsBoundedUnder (· ≥ ·) atTop v := by
    refine ⟨0, ?_⟩
    change ∀ᶠ N : ℕ in atTop, 0 ≤ v N
    exact Eventually.of_forall fun N => hlo _
  have hvhi : IsBoundedUnder (· ≤ ·) atTop v := by
    refine ⟨K, ?_⟩
    change ∀ᶠ N : ℕ in atTop, v N ≤ K
    exact Eventually.of_forall fun N => hhi _
  have hlim := liminf_add_of_tendsto_zero herr hvlo hvhi
  have heq : liminf u atTop = liminf v atTop := by
    rw [← hlim]
    apply liminf_congr
    exact Eventually.of_forall fun N => by simp only [Pi.add_apply, v]; ring
  rw [heq]
  change liminf ((fun N : ℕ => u ((q : ℕ) * N)) ∘ (fun N : ℕ => N / (q : ℕ))) atTop = _
  rw [liminf_comp, map_div_atTop_eq_nat (q : ℕ) q.pos]

theorem lowerDensity_eq_liminf_multiples (A : Set ℕ) (q : ℕ+) :
    lowerDensity A = liminf (fun N : ℕ =>
      (count A ((q : ℕ) * N) : ℝ) / ((q : ℕ) * N : ℕ)) atTop := by
  exact liminf_eq_liminf_multiples_of_rounding q (count_ratio_nonneg A) (count_ratio_le_one A)
    (count_ratio_rounding_tendsto_zero A q)

theorem jointLowerDensity_eq_liminf_multiples (A B : Set ℕ) (q : ℕ+) :
    jointLowerDensity A B = liminf (fun N : ℕ =>
      ((count A ((q : ℕ) * N) : ℝ) + count B ((q : ℕ) * N)) / ((q : ℕ) * N : ℕ)) atTop := by
  have herr := (count_ratio_rounding_tendsto_zero A q).add (count_ratio_rounding_tendsto_zero B q)
  have herr' : Tendsto (fun N : ℕ => ((count A N : ℝ) + count B N) / N -
      ((count A ((q : ℕ) * (N / (q : ℕ))) : ℝ) + count B ((q : ℕ) * (N / (q : ℕ)))) /
        ((q : ℕ) * (N / (q : ℕ)) : ℕ)) atTop (𝓝 0) := by
    simpa only [add_zero] using herr.congr (fun N => by ring)
  apply liminf_eq_liminf_multiples_of_rounding (K := 2) q (fun N => by positivity) ?_ herr'
  intro N
  rw [add_div]
  linarith [count_ratio_le_one A N, count_ratio_le_one B N]

theorem prefix_count_difference_tendsto (A : Set ℕ) :
    Tendsto (fun N : ℕ => ((prefixCount A N : ℝ) - count A N) / N) atTop (𝓝 0) := by
  have h := tendsto_div_of_bounded (fun N => (prefixCount A N : ℝ) - count A N) 0 1
    (fun N => by simpa only [zero_mul, sub_zero] using prefixCount_error A N)
  simpa using h

theorem tendsto_mul_nat_atTop (q : ℕ+) :
    Tendsto (fun N : ℕ => (q : ℕ) * N) atTop atTop := by
  apply tendsto_atTop.mpr
  intro b
  filter_upwards [eventually_ge_atTop b] with N hN
  have hq := q.pos
  nlinarith

theorem lowerDensity_eq_liminf_prefix_multiples (A : Set ℕ) (q : ℕ+) :
    lowerDensity A = liminf (fun N : ℕ =>
      (prefixCount A ((q : ℕ) * N) : ℝ) / ((q : ℕ) * N : ℕ)) atTop := by
  let f : ℕ → ℝ := fun N => (count A ((q : ℕ) * N) : ℝ) / ((q : ℕ) * N : ℕ)
  have hflo : IsBoundedUnder (· ≥ ·) atTop f := by
    refine ⟨0, ?_⟩
    change ∀ᶠ N : ℕ in atTop, 0 ≤ f N
    exact Eventually.of_forall fun N => count_ratio_nonneg A _
  have hfhi : IsBoundedUnder (· ≤ ·) atTop f := by
    refine ⟨1, ?_⟩
    change ∀ᶠ N : ℕ in atTop, f N ≤ 1
    exact Eventually.of_forall fun N => count_ratio_le_one A _
  have he := (prefix_count_difference_tendsto A).comp (tendsto_mul_nat_atTop q)
  have hl := liminf_add_of_tendsto_zero he hflo hfhi
  rw [lowerDensity_eq_liminf_multiples A q]
  rw [← hl]
  apply liminf_congr
  exact Eventually.of_forall fun N => by simp only [Pi.add_apply, f, Function.comp_apply]; ring

theorem jointLowerDensity_eq_liminf_prefix_multiples (A B : Set ℕ) (q : ℕ+) :
    jointLowerDensity A B = liminf (fun N : ℕ =>
      ((prefixCount A ((q : ℕ) * N) : ℝ) + prefixCount B ((q : ℕ) * N)) /
        ((q : ℕ) * N : ℕ)) atTop := by
  let f : ℕ → ℝ := fun N => ((count A ((q : ℕ) * N) : ℝ) + count B ((q : ℕ) * N)) /
    ((q : ℕ) * N : ℕ)
  have hflo : IsBoundedUnder (· ≥ ·) atTop f := by
    refine ⟨0, ?_⟩
    change ∀ᶠ N : ℕ in atTop, 0 ≤ f N
    exact Eventually.of_forall fun N => by dsimp [f]; positivity
  have hfhi : IsBoundedUnder (· ≤ ·) atTop f := by
    refine ⟨2, ?_⟩
    change ∀ᶠ N : ℕ in atTop, f N ≤ 2
    apply Eventually.of_forall
    intro N
    dsimp [f]
    rw [add_div]
    linarith [count_ratio_le_one A ((q : ℕ) * N), count_ratio_le_one B ((q : ℕ) * N)]
  have he0 := ((prefix_count_difference_tendsto A).add (prefix_count_difference_tendsto B)).comp
    (tendsto_mul_nat_atTop q)
  have he : Tendsto (fun N : ℕ =>
      (((prefixCount A ((q : ℕ) * N) : ℝ) + prefixCount B ((q : ℕ) * N)) -
        (count A ((q : ℕ) * N) + count B ((q : ℕ) * N))) / ((q : ℕ) * N : ℕ)) atTop (𝓝 0) := by
    simpa only [add_zero] using he0.congr (fun N => by simp only [Function.comp_apply]; ring)
  have hl := liminf_add_of_tendsto_zero he hflo hfhi
  rw [jointLowerDensity_eq_liminf_multiples A B q]
  rw [← hl]
  apply liminf_congr
  exact Eventually.of_forall fun N => by simp only [Pi.add_apply, f]; ring

theorem liminf_const_mul_of_nonneg {f : ℕ → ℝ} {c : ℝ} (hc : 0 ≤ c)
    (hflo : IsBoundedUnder (· ≥ ·) atTop f) (hfhi : IsBoundedUnder (· ≤ ·) atTop f) :
    liminf (fun N => c * f N) atTop = c * liminf f atTop := by
  have hm : Monotone (fun x : ℝ => c * x) := fun x y h => mul_le_mul_of_nonneg_left h hc
  exact (hm.map_liminf_of_continuousAt f (by fun_prop) hfhi.isCobounded_flip hflo).symm

theorem lowerDensity_scale_of_prefix_identity (A P : Set ℕ) (g h : ℕ+)
    (hcounts : ∀ N : ℕ, prefixCount P ((h : ℕ) * N) = prefixCount A ((g : ℕ) * N)) :
    lowerDensity P = ((g : ℕ) : ℝ) / (h : ℕ) * lowerDensity A := by
  let f : ℕ → ℝ := fun N => (prefixCount A ((g : ℕ) * N) : ℝ) / ((g : ℕ) * N : ℕ)
  have hflo : IsBoundedUnder (· ≥ ·) atTop f := by
    refine ⟨0, ?_⟩
    change ∀ᶠ N : ℕ in atTop, 0 ≤ f N
    exact Eventually.of_forall fun N => by dsimp [f]; positivity
  have hfhi : IsBoundedUnder (· ≤ ·) atTop f := by
    refine ⟨1, ?_⟩
    change ∀ᶠ N : ℕ in atTop, f N ≤ 1
    apply Eventually.of_forall
    intro N
    rcases N with _ | N
    · simp [f, prefixCount]
    · apply (div_le_one (by positivity)).mpr
      exact_mod_cast prefixCount_le A ((g : ℕ) * (N + 1))
  rw [lowerDensity_eq_liminf_prefix_multiples P h, lowerDensity_eq_liminf_prefix_multiples A g]
  calc
    liminf (fun N : ℕ => (prefixCount P ((h : ℕ) * N) : ℝ) / ((h : ℕ) * N : ℕ)) atTop =
        liminf (fun N => ((g : ℕ) : ℝ) / (h : ℕ) * f N) atTop := by
          apply liminf_congr
          apply Eventually.of_forall
          intro N
          rw [hcounts]
          rcases N with _ | N
          · simp [f, prefixCount]
          · dsimp [f]
            push_cast
            field_simp
    _ = _ := liminf_const_mul_of_nonneg (by positivity) hflo hfhi

theorem jointLowerDensity_scale_of_prefix_identities (A B P Q : Set ℕ) (g h : ℕ+)
    (hA : ∀ N : ℕ, prefixCount P ((h : ℕ) * N) = prefixCount A ((g : ℕ) * N))
    (hB : ∀ N : ℕ, prefixCount Q ((h : ℕ) * N) = prefixCount B ((g : ℕ) * N)) :
    jointLowerDensity P Q = ((g : ℕ) : ℝ) / (h : ℕ) * jointLowerDensity A B := by
  let f : ℕ → ℝ := fun N =>
    ((prefixCount A ((g : ℕ) * N) : ℝ) + prefixCount B ((g : ℕ) * N)) / ((g : ℕ) * N : ℕ)
  have hflo : IsBoundedUnder (· ≥ ·) atTop f := by
    refine ⟨0, ?_⟩
    change ∀ᶠ N : ℕ in atTop, 0 ≤ f N
    exact Eventually.of_forall fun N => by dsimp [f]; positivity
  have hfhi : IsBoundedUnder (· ≤ ·) atTop f := by
    refine ⟨2, ?_⟩
    change ∀ᶠ N : ℕ in atTop, f N ≤ 2
    apply Eventually.of_forall
    intro N
    rcases N with _ | N
    · simp [f, prefixCount]
    · dsimp [f]
      rw [add_div]
      have ha : (prefixCount A ((g : ℕ) * (N + 1)) : ℝ) / ((g : ℕ) * (N + 1) : ℕ) ≤ 1 := by
        apply (div_le_one (by positivity)).mpr
        exact_mod_cast prefixCount_le A ((g : ℕ) * (N + 1))
      have hb : (prefixCount B ((g : ℕ) * (N + 1)) : ℝ) / ((g : ℕ) * (N + 1) : ℕ) ≤ 1 := by
        apply (div_le_one (by positivity)).mpr
        exact_mod_cast prefixCount_le B ((g : ℕ) * (N + 1))
      linarith
  rw [jointLowerDensity_eq_liminf_prefix_multiples P Q h,
    jointLowerDensity_eq_liminf_prefix_multiples A B g]
  calc
    liminf (fun N : ℕ =>
      ((prefixCount P ((h : ℕ) * N) : ℝ) + prefixCount Q ((h : ℕ) * N)) /
        ((h : ℕ) * N : ℕ)) atTop =
      liminf (fun N => ((g : ℕ) : ℝ) / (h : ℕ) * f N) atTop := by
        apply liminf_congr
        apply Eventually.of_forall
        intro N
        rw [hA, hB]
        rcases N with _ | N
        · simp [f, prefixCount]
        · dsimp [f]
          push_cast
          field_simp
    _ = _ := liminf_const_mul_of_nonneg (by positivity) hflo hfhi

end Erdos335
