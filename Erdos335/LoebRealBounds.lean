import Erdos335.LoebRealCorrelation

/-!
# Hilbert norm and orthogonality bounds from finite averages
-/

set_option autoImplicit false

open Filter Set Topology MeasureTheory Finset
open scoped BigOperators InnerProductSpace

namespace Erdos335.Loeb

variable {X : ℕ → Type*} [∀ n, Fintype (X n)] [∀ n, Nonempty (X n)]

theorem realLoebVector_norm_le_one (U : Ultrafilter ℕ) (hU : (U : Filter ℕ) ≤ atTop)
    (f : ∀ n, X n → ℝ) (hf : ∀ n x, f n x ∈ Icc (0 : ℝ) 1) :
    ‖realLoebVector U hU f hf‖ ≤ 1 := by
  have hfinite (n : ℕ) : (∑ x : X n, f n x ^ 2) / (Nat.card (X n) : ℝ) ≤ 1 := by
    rw [Nat.card_eq_fintype_card]
    have hcard : (0 : ℝ) < Fintype.card (X n) := by exact_mod_cast Fintype.card_pos
    apply (div_le_one hcard).mpr
    calc
      _ ≤ ∑ _x : X n, (1 : ℝ) := by
        apply sum_le_sum
        intro x hx
        nlinarith [(hf n x).1, (hf n x).2]
      _ = _ := by simp
  have hsq := le_of_tendsto' (tendsto_realLoebVector_energy U hU f hf) hfinite
  nlinarith [norm_nonneg (realLoebVector U hU f hf)]

theorem realLoebVector_residual_inner_eq_zero
    (U : Ultrafilter ℕ) (hU : (U : Filter ℕ) ≤ atTop) (F f : ∀ n, X n → ℝ)
    (hF : ∀ n x, F n x ∈ Icc (0 : ℝ) 1) (hf : ∀ n x, f n x ∈ Icc (0 : ℝ) 1)
    (hzero : Tendsto (fun n => (∑ x : X n, f n x * (F n x - f n x)) /
      (Nat.card (X n) : ℝ)) (U : Filter ℕ) (𝓝 0)) :
    ⟪realLoebVector U hU f hf, realLoebVector U hU F hF - realLoebVector U hU f hf⟫_ℝ = 0 :=
  tendsto_nhds_unique (tendsto_realLoebVector_residual_correlation U hU F f f hF hf hf) hzero

theorem realLoebVector_residual_inner_bound
    (U : Ultrafilter ℕ) (hU : (U : Filter ℕ) ≤ atTop) (F f g : ∀ n, X n → ℝ)
    (hF : ∀ n x, F n x ∈ Icc (0 : ℝ) 1)
    (hf : ∀ n x, f n x ∈ Icc (0 : ℝ) 1) (hg : ∀ n x, g n x ∈ Icc (0 : ℝ) 1)
    (ε : ℝ) (hbound : ∀ᶠ n in (U : Filter ℕ),
      |(∑ x : X n, f n x * (F n x - g n x)) / (Nat.card (X n) : ℝ)| ≤ ε) :
    |⟪realLoebVector U hU f hf, realLoebVector U hU F hF - realLoebVector U hU g hg⟫_ℝ| ≤ ε := by
  exact le_of_tendsto (tendsto_realLoebVector_residual_correlation U hU F f g hF hf hg).abs hbound

end Erdos335.Loeb
