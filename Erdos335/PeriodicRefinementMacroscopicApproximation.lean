import Erdos335.PeriodicRefinementUniformErrors
import Erdos335.PeriodicRefinementInputFamily

/-!
# Joint cumulative limits and countable uniform error bounds
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Filter Set Topology
open scoped BigOperators

noncomputable section

namespace Erdos335.PeriodicRefinement

structure CompactCumulativeData (A B : Set ℕ) (M : ℕ+) (N : ℕ → ℕ) where
  curve : Fin 3 → ZMod (M : ℕ) → C(ℝ, ℝ)
  primitive : Fin 3 → ZMod (M : ℕ) → ℝ → ℝ
  primitive_lipschitz : ∀ i r, LipschitzWith 1 (primitive i r)
  primitive_grid : ∀ (i : Fin 3) (r : ZMod (M : ℕ)) (k : ℕ), primitive i r k =
    prefixCount {n : ℕ | n ∈ macroInput A B i ∧ (n : ZMod (M : ℕ)) = r} k
  curve_lipschitz : ∀ i r, LipschitzWith 1 (curve i r)
  curve_zero : ∀ i r, curve i r 0 = 0
  error : ℕ → ℕ → ℝ
  error_nonnegative : ∀ j n, 0 ≤ error j n
  error_tendsto : ∀ j, Tendsto (error j) atTop (𝓝 0)
  error_bound : ∀ (j n : ℕ) (i : Fin 3) (r : ZMod (M : ℕ)) (t : ℝ),
    t ∈ Icc (0 : ℝ) ((j : ℝ) + 1) →
    |primitive i r (t * N n) / N n - curve i r t| ≤ error j n

def CompactCumulativeData.subsequence
    {A B : Set ℕ} {M : ℕ+} {N : ℕ → ℕ}
    (d : CompactCumulativeData A B M N) (σ : ℕ → ℕ) (hσ : Tendsto σ atTop atTop) :
    CompactCumulativeData A B M (N ∘ σ) where
  curve := d.curve
  primitive := d.primitive
  primitive_lipschitz := d.primitive_lipschitz
  primitive_grid := d.primitive_grid
  curve_lipschitz := d.curve_lipschitz
  curve_zero := d.curve_zero
  error := fun j n => d.error j (σ n)
  error_nonnegative := fun j n => d.error_nonnegative j (σ n)
  error_tendsto := fun j => (d.error_tendsto j).comp hσ
  error_bound := fun j n i r t ht => d.error_bound j (σ n) i r t ht

theorem exists_compact_cumulative_data
    (A B : Set ℕ) (M : ℕ+) (N : ℕ → ℕ) (hN : ∀ n, 0 < N n) :
    ∃ (σ : ℕ → ℕ), StrictMono σ ∧ Nonempty (CompactCumulativeData A B M (N ∘ σ)) := by
  classical
  let I := Fin 3 × ZMod (M : ℕ)
  let S : I → Set ℕ := fun p =>
    {n : ℕ | n ∈ macroInput A B p.1 ∧ (n : ZMod (M : ℕ)) = p.2}
  obtain ⟨σ, G, F, hσ, hG, hF, hlim, _⟩ := exists_joint_cumulative_limits S N hN
  let f : I → ℕ → C(ℝ, ℝ) := fun i n =>
    ⟨fun t => G i (t * N (σ n)) / N (σ n),
      (rescaled_prefix_count_lipschitz (G i) (hG i).1 (N (σ n)) (hN (σ n))).continuous⟩
  have hconverges (i : I) : Tendsto (f i) atTop (𝓝 (F i)) := by
    apply ContinuousMap.tendsto_iff_forall_isCompact_tendstoUniformlyOn.mpr
    intro K hK
    exact hlim i K hK
  have herr (j : ℕ) (i : I) := exists_compact_uniform_error (f i) (F i) (hconverges i) (j + 1)
  choose ε hεnonnegative hεtendsto hεbound using herr
  let error : ℕ → ℕ → ℝ := fun j n => ∑ i : I, ε j i n
  have he_nonnegative (j n : ℕ) : 0 ≤ error j n :=
    Finset.sum_nonneg (fun i _ => hεnonnegative j i n)
  have he_tendsto (j : ℕ) : Tendsto (error j) atTop (𝓝 0) := by
    have h := tendsto_finset_sum (Finset.univ : Finset I) (fun i _ => hεtendsto j i)
    simpa only [error, Finset.sum_const_zero] using h
  refine ⟨σ, hσ, ⟨{
    curve := fun i r => F (i, r)
    primitive := fun i r => G (i, r)
    primitive_lipschitz := fun i r => (hG (i, r)).1
    primitive_grid := fun i r => (hG (i, r)).2
    curve_lipschitz := fun i r => (hF (i, r)).1
    curve_zero := fun i r => (hF (i, r)).2
    error := error
    error_nonnegative := he_nonnegative
    error_tendsto := he_tendsto
    error_bound := ?_
  }⟩⟩
  intro j n i r t ht
  exact (hεbound j (i, r) n t ht).trans
    (Finset.single_le_sum (fun p _ => hεnonnegative j p n) (Finset.mem_univ (i, r)))

end Erdos335.PeriodicRefinement

end
