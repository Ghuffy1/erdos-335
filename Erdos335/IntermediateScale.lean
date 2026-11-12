import Erdos335.PrefixEnvelope
import Erdos335.DensityRescaling
import Mathlib.Analysis.SpecialFunctions.Sqrt

/-!
# Choosing an intermediate scale above all prefix errors

A square-root choice produces a diverging integer scale below the ambient
cutoff and above a prescribed sublinear error envelope.
-/

set_option autoImplicit false

open Filter Topology

namespace Erdos335

theorem exists_intermediate_scale (R : ℕ → ℝ) (hR : ∀ N, 1 ≤ R N)
    (hlim : Tendsto (fun N : ℕ => R N / N) atTop (𝓝 0)) :
    ∃ H : ℕ → ℕ, (∀ N, 0 < H N) ∧ Tendsto H atTop atTop ∧
      Tendsto (fun N : ℕ => (H N : ℝ) / N) atTop (𝓝 0) ∧
      Tendsto (fun N : ℕ => R N / H N) atTop (𝓝 0) := by
  let x := fun N : ℕ => Real.sqrt (R N / N)
  let H := fun N : ℕ => Nat.ceil ((N : ℝ) * x N) + 1
  have hx0 : ∀ N, 0 ≤ x N := fun N => Real.sqrt_nonneg _
  have hxlim : Tendsto x atTop (𝓝 0) := by
    simpa only [x, Function.comp_def, Real.sqrt_zero] using (Real.continuous_sqrt.tendsto 0).comp hlim
  have hHpos : ∀ N, 0 < H N := fun N => Nat.succ_pos _
  have hH0 : ∀ N, (0 : ℝ) < H N := fun N => by exact_mod_cast hHpos N
  have hlow : ∀ N : ℕ, (N : ℝ) * x N ≤ H N := by
    intro N
    have h := Nat.le_ceil ((N : ℝ) * x N)
    dsimp only [H]
    push_cast
    linarith
  have hhigh : ∀ N : ℕ, (H N : ℝ) ≤ (N : ℝ) * x N + 2 := by
    intro N
    have h := Nat.ceil_lt_add_one (mul_nonneg (Nat.cast_nonneg N) (hx0 N))
    dsimp only [H]
    push_cast
    linarith
  have hidentity : ∀ N, 1 ≤ N → R N = (N : ℝ) * (x N) ^ 2 := by
    intro N hN
    have hN0 : (N : ℝ) ≠ 0 := by exact_mod_cast (show N ≠ 0 by omega)
    have hx2 : (x N) ^ 2 = R N / N := Real.sq_sqrt (div_nonneg (by linarith [hR N]) (Nat.cast_nonneg N))
    rw [hx2]
    field_simp
  have hRbound : ∀ N, 1 ≤ N → R N / H N ≤ x N := by
    intro N hN
    apply (div_le_iff₀ (hH0 N)).mpr
    have hm := mul_le_mul_of_nonneg_right (hlow N) (hx0 N)
    rw [hidentity N hN]
    nlinarith
  have hHbound : ∀ N, 1 ≤ N → (H N : ℝ) / N ≤ x N + 2 / N := by
    intro N hN
    have hNR : (0 : ℝ) < N := by exact_mod_cast hN
    apply (div_le_iff₀ hNR).mpr
    have heq : (x N + 2 / N) * N = (N : ℝ) * x N + 2 := by field_simp
    rw [heq]
    exact hhigh N
  have hHlim : Tendsto (fun N : ℕ => (H N : ℝ) / N) atTop (𝓝 0) := by
    have hup : Tendsto (fun N : ℕ => x N + 2 / N) atTop (𝓝 0) := by
      simpa only [add_zero] using hxlim.add (tendsto_const_div_atTop_nhds_zero_nat 2)
    apply squeeze_zero' (Eventually.of_forall fun N => by positivity) ?_ hup
    exact (eventually_ge_atTop 1).mono fun N hN => hHbound N hN
  have hRlim : Tendsto (fun N : ℕ => R N / H N) atTop (𝓝 0) := by
    apply squeeze_zero' (Eventually.of_forall fun N => div_nonneg (by linarith [hR N]) (hH0 N).le) ?_ hxlim
    exact (eventually_ge_atTop 1).mono fun N hN => hRbound N hN
  have hsq : ∀ N, 1 ≤ N → N ≤ H N * H N := by
    intro N hN
    have hprod := mul_nonneg (sub_nonneg.mpr (hlow N))
      (add_nonneg (hH0 N).le (mul_nonneg (Nat.cast_nonneg N) (hx0 N)))
    have hRn := mul_le_mul_of_nonneg_left (hR N) (Nat.cast_nonneg N)
    have hident := congrArg (fun r : ℝ => (N : ℝ) * r) (hidentity N hN)
    have hreal : (N : ℝ) ≤ (H N : ℝ) * H N := by nlinarith
    exact_mod_cast hreal
  have hHtop : Tendsto H atTop atTop := by
    apply tendsto_atTop.mpr
    intro K
    filter_upwards [eventually_ge_atTop (max 1 (K * K + 1))] with N hN
    have hN1 : 1 ≤ N := (le_max_left _ _).trans hN
    have hNK : K * K + 1 ≤ N := (le_max_right _ _).trans hN
    have hNN := hsq N hN1
    by_contra hsmall
    have hHK : H N ≤ K := by omega
    have hHH := Nat.mul_le_mul hHK hHK
    omega
  exact ⟨H, hHpos, hHtop, hHlim, hRlim⟩

theorem HasDensity.prefixError_mul_tendsto_zero {A : Set ℕ} {d : ℝ}
    (hA : HasDensity A d) (m : ℕ+) :
    Tendsto (fun N : ℕ => prefixError A d ((m : ℕ) * N) / N) atTop (𝓝 0) := by
  have hE := hA.prefixError_tendsto_zero.comp (tendsto_mul_nat_atTop m)
  have hscaled : Tendsto
      (fun N : ℕ => ((m : ℕ) : ℝ) *
        (prefixError A d ((m : ℕ) * N) / ((m : ℕ) * N : ℕ))) atTop (𝓝 0) := by
    simpa only [Function.comp_def, mul_zero] using tendsto_const_nhds.mul hE
  apply hscaled.congr
  intro N
  by_cases hN : N = 0
  · simp [hN]
  · have hNR : (N : ℝ) ≠ 0 := by exact_mod_cast hN
    have hmR : ((m : ℕ) : ℝ) ≠ 0 := by exact_mod_cast m.ne_zero
    push_cast
    field_simp

theorem exists_common_error_dominating_scale (A B C : Set ℕ) (a b c : ℝ)
    (hA : HasDensity A a) (hB : HasDensity B b) (hC : HasDensity C c) :
    ∃ H : ℕ → ℕ, (∀ N, 0 < H N) ∧ Tendsto H atTop atTop ∧
      Tendsto (fun N : ℕ => (H N : ℝ) / N) atTop (𝓝 0) ∧
      Tendsto (fun N : ℕ => prefixError A a (2 * N) / H N) atTop (𝓝 0) ∧
      Tendsto (fun N : ℕ => prefixError B b (2 * N) / H N) atTop (𝓝 0) ∧
      Tendsto (fun N : ℕ => prefixError C c (2 * N) / H N) atTop (𝓝 0) := by
  let R := fun N => prefixError A a (2 * N) + prefixError B b (2 * N) +
    prefixError C c (2 * N) + 1
  have hR : ∀ N, 1 ≤ R N := by
    intro N
    dsimp only [R]
    linarith [prefixError_nonneg A a (2 * N), prefixError_nonneg B b (2 * N),
      prefixError_nonneg C c (2 * N)]
  have hlim : Tendsto (fun N : ℕ => R N / N) atTop (𝓝 0) := by
    have h := ((hA.prefixError_mul_tendsto_zero 2).add
      (hB.prefixError_mul_tendsto_zero 2)).add (hC.prefixError_mul_tendsto_zero 2)
    have hh := h.add (tendsto_const_div_atTop_nhds_zero_nat 1)
    simpa [R, add_div] using hh
  obtain ⟨H, hHpos, hHtop, hHlim, hRH⟩ := exists_intermediate_scale R hR hlim
  have hcontrol : ∀ E : ℕ → ℝ, (∀ N, 0 ≤ E N) → (∀ N, E N ≤ R N) →
      Tendsto (fun N : ℕ => E N / H N) atTop (𝓝 0) := by
    intro E hE0 hER
    apply squeeze_zero (fun N => div_nonneg (hE0 N) (Nat.cast_nonneg _))
      (fun N => div_le_div_of_nonneg_right (hER N) (Nat.cast_nonneg _)) hRH
  refine ⟨H, hHpos, hHtop, hHlim, ?_, ?_, ?_⟩
  · apply hcontrol (fun N => prefixError A a (2 * N)) (fun N => prefixError_nonneg A a (2 * N))
    intro N
    dsimp only [R]
    linarith [prefixError_nonneg B b (2 * N), prefixError_nonneg C c (2 * N)]
  · apply hcontrol (fun N => prefixError B b (2 * N)) (fun N => prefixError_nonneg B b (2 * N))
    intro N
    dsimp only [R]
    linarith [prefixError_nonneg A a (2 * N), prefixError_nonneg C c (2 * N)]
  · apply hcontrol (fun N => prefixError C c (2 * N)) (fun N => prefixError_nonneg C c (2 * N))
    intro N
    dsimp only [R]
    linarith [prefixError_nonneg A a (2 * N), prefixError_nonneg B b (2 * N)]

end Erdos335
