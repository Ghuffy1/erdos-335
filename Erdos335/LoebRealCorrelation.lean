import Erdos335.LoebRealHilbert

/-!
# Real internal correlations as Hilbert inner products
-/

set_option autoImplicit false

open Filter Set Topology MeasureTheory Finset
open scoped BigOperators InnerProductSpace

namespace Erdos335.Loeb

variable {X : ℕ → Type*} [∀ n, Fintype (X n)] [∀ n, Nonempty (X n)]

omit [∀ n, Fintype (X n)] [∀ n, Nonempty (X n)] in
theorem tendsto_realLoebFunction (U : Ultrafilter ℕ) (f : ∀ n, X n → ℝ)
    (hf : ∀ n x, f n x ∈ Icc (0 : ℝ) 1) (x : ∀ n, X n) :
    Tendsto (fun n => f n (x n)) (U : Filter ℕ)
      (𝓝 (realLoebFunction U f hf (x : (U : Filter ℕ).Product X))) := by
  exact (continuous_subtype_val.tendsto _).comp
    (tendsto_ultralimitFunction U (fun n y => (⟨f n y, hf n y⟩ : Icc (0 : ℝ) 1)) x)

omit [∀ n, Fintype (X n)] [∀ n, Nonempty (X n)] in
theorem realLoebFunction_mul (U : Ultrafilter ℕ) (f g : ∀ n, X n → ℝ)
    (hf : ∀ n x, f n x ∈ Icc (0 : ℝ) 1) (hg : ∀ n x, g n x ∈ Icc (0 : ℝ) 1)
    (hfg : ∀ n x, f n x * g n x ∈ Icc (0 : ℝ) 1) :
    realLoebFunction U (fun n x => f n x * g n x) hfg =
      fun x => realLoebFunction U f hf x * realLoebFunction U g hg x := by
  funext x
  induction x using Quotient.inductionOn with
  | h a =>
    exact tendsto_nhds_unique (tendsto_realLoebFunction U _ hfg a)
      ((tendsto_realLoebFunction U f hf a).mul (tendsto_realLoebFunction U g hg a))

theorem tendsto_realLoebFunction_averages (U : Ultrafilter ℕ) (hU : (U : Filter ℕ) ≤ atTop)
    (f : ∀ n, X n → ℝ) (hf : ∀ n x, f n x ∈ Icc (0 : ℝ) 1) :
    Tendsto (fun n => (∑ x : X n, f n x) / (Nat.card (X n) : ℝ)) (U : Filter ℕ)
      (𝓝 (∫ x, realLoebFunction U f hf x ∂loebMeasure U hU)) := by
  exact tendsto_continuous_coordinate_averages U hU
    (fun n y => (⟨f n y, hf n y⟩ : Icc (0 : ℝ) 1))
    (fun z : Icc (0 : ℝ) 1 => z.val) continuous_subtype_val

theorem realLoebVector_inner (U : Ultrafilter ℕ) (hU : (U : Filter ℕ) ≤ atTop)
    (f g : ∀ n, X n → ℝ)
    (hf : ∀ n x, f n x ∈ Icc (0 : ℝ) 1) (hg : ∀ n x, g n x ∈ Icc (0 : ℝ) 1) :
    ⟪realLoebVector U hU f hf, realLoebVector U hU g hg⟫_ℝ =
      ∫ x, realLoebFunction U f hf x * realLoebFunction U g hg x ∂loebMeasure U hU := by
  rw [L2.inner_def]
  apply integral_congr_ae
  filter_upwards [(realLoebFunction_memLp U hU f hf).coeFn_toLp,
    (realLoebFunction_memLp U hU g hg).coeFn_toLp] with x hfx hgx
  change ⟪(realLoebFunction_memLp U hU f hf).toLp (realLoebFunction U f hf) x,
    (realLoebFunction_memLp U hU g hg).toLp (realLoebFunction U g hg) x⟫_ℝ = _
  rw [hfx, hgx]
  simp [RCLike.inner_apply, mul_comm]

theorem tendsto_realLoebVector_inner (U : Ultrafilter ℕ) (hU : (U : Filter ℕ) ≤ atTop)
    (f g : ∀ n, X n → ℝ)
    (hf : ∀ n x, f n x ∈ Icc (0 : ℝ) 1) (hg : ∀ n x, g n x ∈ Icc (0 : ℝ) 1) :
    Tendsto (fun n => (∑ x : X n, f n x * g n x) / (Nat.card (X n) : ℝ)) (U : Filter ℕ)
      (𝓝 ⟪realLoebVector U hU f hf, realLoebVector U hU g hg⟫_ℝ) := by
  have hfg (n) (x : X n) : f n x * g n x ∈ Icc (0 : ℝ) 1 := by
    refine ⟨mul_nonneg (hf n x).1 (hg n x).1, ?_⟩
    exact (mul_le_mul (hf n x).2 (hg n x).2 (hg n x).1 zero_le_one).trans (by norm_num)
  have h := tendsto_realLoebFunction_averages U hU (fun n x => f n x * g n x) hfg
  rw [realLoebFunction_mul U f g hf hg hfg, ← realLoebVector_inner U hU f g hf hg] at h
  exact h

theorem tendsto_realLoebVector_residual_correlation
    (U : Ultrafilter ℕ) (hU : (U : Filter ℕ) ≤ atTop) (F f g : ∀ n, X n → ℝ)
    (hF : ∀ n x, F n x ∈ Icc (0 : ℝ) 1)
    (hf : ∀ n x, f n x ∈ Icc (0 : ℝ) 1) (hg : ∀ n x, g n x ∈ Icc (0 : ℝ) 1) :
    Tendsto (fun n => (∑ x : X n, f n x * (F n x - g n x)) / (Nat.card (X n) : ℝ))
      (U : Filter ℕ)
      (𝓝 ⟪realLoebVector U hU f hf, realLoebVector U hU F hF - realLoebVector U hU g hg⟫_ℝ) := by
  have h := (tendsto_realLoebVector_inner U hU f F hf hF).sub
    (tendsto_realLoebVector_inner U hU f g hf hg)
  simpa only [mul_sub, sum_sub_distrib, sub_div, inner_sub_right] using h

end Erdos335.Loeb
