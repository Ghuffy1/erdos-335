import Erdos335.LoebUltralimit

/-!
# Compact ranges of internal ultralimit maps

Countable saturation realizes every limiting approximate value. In
particular, the range of a compact metric valued internal map is closed.
-/

set_option autoImplicit false

open Filter Set Topology

namespace Erdos335.Loeb

variable {X : ℕ → Type*} [∀ n, Nonempty (X n)]
  {E : Type*} [MetricSpace E] [CompactSpace E]

theorem exists_ultralimit_preimage_of_approximation
    (U : Ultrafilter ℕ) (hU : (U : Filter ℕ) ≤ atTop)
    (f : ∀ n, X n → E) (y : E)
    (hy : ∀ ε : ℝ, 0 < ε → ∀ᶠ n in U, ∃ x : X n, dist (f n x) y < ε) :
    ∃ x : (U : Filter ℕ).Product X, ultralimitFunction U f x = y := by
  let P (j n : ℕ) : Set (X n) := {x | dist (f n x) y ≤ 1 / (j + 1 : ℝ)}
  have hfinite : ∀ k, ∀ᶠ n in U, ∃ x : X n, ∀ j ≤ k, x ∈ P j n := by
    intro k
    have he := hy (1 / (k + 1 : ℝ)) (by positivity)
    apply he.mono
    rintro n ⟨x, hx⟩
    refine ⟨x, fun j hj => hx.le.trans ?_⟩
    apply one_div_le_one_div_of_le
    · positivity
    · exact_mod_cast Nat.add_le_add_right hj 1
  obtain ⟨a, ha⟩ := exists_representative_of_eventually_finite U hU P hfinite
  refine ⟨(a : (U : Filter ℕ).Product X), dist_eq_zero.mp ?_⟩
  have hdist : ∀ j : ℕ,
      dist (ultralimitFunction U f (a : (U : Filter ℕ).Product X)) y ≤ 1 / (j + 1 : ℝ) := by
    intro j
    exact le_of_tendsto ((tendsto_ultralimitFunction U f a).dist tendsto_const_nhds) (ha j)
  apply le_antisymm ?_ dist_nonneg
  by_contra hn
  obtain ⟨j, hj⟩ := exists_nat_one_div_lt (lt_of_not_ge hn)
  exact (not_lt_of_ge (hdist j)) hj

theorem isClosed_range_ultralimitFunction
    (U : Ultrafilter ℕ) (hU : (U : Filter ℕ) ≤ atTop) (f : ∀ n, X n → E) :
    IsClosed (Set.range (ultralimitFunction U f)) := by
  apply closure_subset_iff_isClosed.mp
  intro y hy
  apply exists_ultralimit_preimage_of_approximation U hU f y
  intro ε hε
  obtain ⟨z, hz, hzy⟩ := (Metric.mem_closure_iff.mp hy) (ε / 2) (by positivity)
  obtain ⟨x, rfl⟩ := hz
  obtain ⟨a, ha⟩ := Quotient.exists_rep x
  have hrep : (a : (U : Filter ℕ).Product X) = x := ha
  have hdist : dist (ultralimitFunction U f (a : (U : Filter ℕ).Product X)) y < ε / 2 := by
    rw [hrep]
    simpa only [dist_comm] using hzy
  have he := (tendsto_ultralimitFunction U f a).eventually
    (Metric.ball_mem_nhds _ (by positivity : 0 < ε / 2))
  apply he.mono
  intro n hn
  refine ⟨a n, ?_⟩
  have ht := dist_triangle (f n (a n))
    (ultralimitFunction U f (a : (U : Filter ℕ).Product X)) y
  change dist (f n (a n)) (ultralimitFunction U f (a : (U : Filter ℕ).Product X)) < ε / 2 at hn
  linarith

theorem isCompact_range_ultralimitFunction
    (U : Ultrafilter ℕ) (hU : (U : Filter ℕ) ≤ atTop) (f : ∀ n, X n → E) :
    IsCompact (Set.range (ultralimitFunction U f)) :=
  (isClosed_range_ultralimitFunction U hU f).isCompact

end Erdos335.Loeb
