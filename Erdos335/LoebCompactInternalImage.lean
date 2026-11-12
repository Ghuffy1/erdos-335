import Erdos335.LoebCompactHom
import Erdos335.LoebSubgroup

/-!
# Compact images of internal sets

Countable saturation preserves an internal membership constraint while
realizing a limiting compact-valued image. Consequently the image of an
internal subgroup in a compact ultralimit factor is compact.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Filter Set Topology

namespace Erdos335.Loeb

variable {X : ℕ → Type*} [∀ n, Nonempty (X n)]
variable {E : Type*} [MetricSpace E] [CompactSpace E]

theorem exists_ultralimit_in_internal_of_approximation
    (U : Ultrafilter ℕ) (hU : (U : Filter ℕ) ≤ atTop)
    (A : ∀ n, Set (X n)) (f : ∀ n, X n → E) (y : E)
    (hy : ∀ ε : ℝ, 0 < ε → ∀ᶠ n in U, ∃ x ∈ A n, dist (f n x) y < ε) :
    ∃ x ∈ internalSet U A, ultralimitFunction U f x = y := by
  let P (j n : ℕ) : Set (X n) := {x | x ∈ A n ∧ dist (f n x) y ≤ 1 / (j + 1 : ℝ)}
  have hfinite : ∀ k, ∀ᶠ n in U, ∃ x : X n, ∀ j ≤ k, x ∈ P j n := by
    intro k
    have he := hy (1 / (k + 1 : ℝ)) (by positivity)
    apply he.mono
    rintro n ⟨x, hxA, hx⟩
    refine ⟨x, fun j hj => ⟨hxA, hx.le.trans ?_⟩⟩
    apply one_div_le_one_div_of_le
    · positivity
    · exact_mod_cast Nat.add_le_add_right hj 1
  obtain ⟨a, ha⟩ := exists_representative_of_eventually_finite U hU P hfinite
  have haA : (a : (U : Filter ℕ).Product X) ∈ internalSet U A :=
    (ha 0).mono fun n hn => hn.1
  refine ⟨(a : (U : Filter ℕ).Product X), haA, dist_eq_zero.mp ?_⟩
  have hdist : ∀ j : ℕ, dist (ultralimitFunction U f (a : (U : Filter ℕ).Product X)) y ≤ 1 / (j + 1 : ℝ) := by
    intro j
    exact le_of_tendsto ((tendsto_ultralimitFunction U f a).dist tendsto_const_nhds)
      ((ha j).mono fun n hn => hn.2)
  apply le_antisymm ?_ dist_nonneg
  by_contra hn
  obtain ⟨j, hj⟩ := exists_nat_one_div_lt (lt_of_not_ge hn)
  exact (not_lt_of_ge (hdist j)) hj

theorem isCompact_image_internalSet_ultralimitFunction
    (U : Ultrafilter ℕ) (hU : (U : Filter ℕ) ≤ atTop)
    (A : ∀ n, Set (X n)) (f : ∀ n, X n → E) :
    IsCompact (ultralimitFunction U f '' internalSet U A) := by
  apply IsClosed.isCompact
  apply closure_subset_iff_isClosed.mp
  intro y hy
  apply exists_ultralimit_in_internal_of_approximation U hU A f y
  intro ε hε
  obtain ⟨z, hz, hzy⟩ := (Metric.mem_closure_iff.mp hy) (ε / 2) (by positivity)
  obtain ⟨x, hx, rfl⟩ := hz
  obtain ⟨a, ha⟩ := Quotient.exists_rep x
  have hrep : (a : (U : Filter ℕ).Product X) = x := ha
  have haA : ∀ᶠ n in U, a n ∈ A n := by
    change (a : (U : Filter ℕ).Product X) ∈ internalSet U A
    rwa [hrep]
  have hdist : dist (ultralimitFunction U f (a : (U : Filter ℕ).Product X)) y < ε / 2 := by
    rw [hrep]
    simpa only [dist_comm] using hzy
  have he := (tendsto_ultralimitFunction U f a).eventually
    (Metric.ball_mem_nhds _ (by positivity : 0 < ε / 2))
  filter_upwards [haA, he] with n hnA hn
  refine ⟨a n, hnA, ?_⟩
  have ht := dist_triangle (f n (a n))
    (ultralimitFunction U f (a : (U : Filter ℕ).Product X)) y
  change dist (f n (a n)) (ultralimitFunction U f (a : (U : Filter ℕ).Product X)) < ε / 2 at hn
  linarith

theorem isCompact_image_internalAddSubgroup
    {X : ℕ → Type*} [∀ n, AddCommGroup (X n)]
    {E : Type*} [AddCommGroup E] [MetricSpace E] [CompactSpace E] [IsTopologicalAddGroup E]
    (U : Ultrafilter ℕ) (hU : (U : Filter ℕ) ≤ atTop)
    (H : ∀ n, AddSubgroup (X n)) (f : ∀ n, X n →+ E) :
    IsCompact (ultralimitAddHom U f '' (internalAddSubgroup U H : Set ((U : Filter ℕ).Product X))) :=
  isCompact_image_internalSet_ultralimitFunction U hU (fun n => (H n : Set (X n))) (fun n => f n)

end Erdos335.Loeb
