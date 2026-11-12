import Mathlib.Topology.MetricSpace.Basic
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Tactic

/-!
# Convergence of asymptotically finite profiles

If a sequence approaches a finite set of templates and its successive
increments tend to zero, its approximating template is eventually fixed.
-/

set_option autoImplicit false

open Filter Topology

namespace Erdos335

theorem tendsto_of_separated_approximants
    {X : Type*} [MetricSpace X] (u v : ℕ → X) (δ : ℝ) (hδ : 0 < δ)
    (hseparated : ∀ n m, v n ≠ v m → δ ≤ dist (v n) (v m))
    (happrox : Tendsto (fun n => dist (u n) (v n)) atTop (𝓝 0))
    (hstep : Tendsto (fun n => dist (u (n + 1)) (u n)) atTop (𝓝 0)) :
    ∃ N, Tendsto u atTop (𝓝 (v N)) := by
  have hnext := happrox.comp (tendsto_add_atTop_nat 1)
  have hbound (n : ℕ) : dist (v (n + 1)) (v n) ≤
      dist (u (n + 1)) (v (n + 1)) + dist (u (n + 1)) (u n) + dist (u n) (v n) := by
    calc
      dist (v (n + 1)) (v n) ≤ dist (v (n + 1)) (u (n + 1)) + dist (u (n + 1)) (v n) :=
        dist_triangle _ _ _
      _ ≤ dist (v (n + 1)) (u (n + 1)) + (dist (u (n + 1)) (u n) + dist (u n) (v n)) :=
        add_le_add le_rfl (dist_triangle _ _ _)
      _ = _ := by rw [dist_comm (v (n + 1)) (u (n + 1))]; ring
  have hlim : Tendsto (fun n => dist (v (n + 1)) (v n)) atTop (𝓝 0) :=
    squeeze_zero (fun _ => dist_nonneg) hbound (by simpa using (hnext.add hstep).add happrox)
  have heventually : ∀ᶠ n in atTop, v (n + 1) = v n := by
    filter_upwards [(tendsto_order.mp hlim).2 δ hδ] with n hn
    by_contra hne
    exact (not_le_of_gt hn) (hseparated (n + 1) n hne)
  obtain ⟨N, hN⟩ := eventually_atTop.mp heventually
  have hfixed (n : ℕ) (hn : N ≤ n) : v n = v N := by
    obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hn
    induction k with
    | zero => simp
    | succ k ih =>
      calc
        v (N + (k + 1)) = v ((N + k) + 1) := by congr 1
        _ = v (N + k) := hN _ (by omega)
        _ = v N := ih (by omega)
  refine ⟨N, Metric.tendsto_nhds.mpr ?_⟩
  intro ε hε
  filter_upwards [(tendsto_order.mp happrox).2 ε hε, eventually_ge_atTop N] with n hn hnN
  simpa only [hfixed n hnN] using hn

theorem tendsto_of_finite_approximants
    {X : Type*} [MetricSpace X] (u v : ℕ → X) (F : Finset X)
    (hmem : ∀ n, v n ∈ F)
    (happrox : Tendsto (fun n => dist (u n) (v n)) atTop (𝓝 0))
    (hstep : Tendsto (fun n => dist (u (n + 1)) (u n)) atTop (𝓝 0)) :
    ∃ p ∈ F, Tendsto u atTop (𝓝 p) := by
  classical
  let pairs := (F.product F).filter (fun p => p.1 ≠ p.2)
  let distances := pairs.image (fun p => dist p.1 p.2)
  have hseparation : ∃ δ : ℝ, 0 < δ ∧ ∀ n m, v n ≠ v m → δ ≤ dist (v n) (v m) := by
    by_cases hne : distances.Nonempty
    · refine ⟨distances.min' hne, ?_, ?_⟩
      · obtain ⟨p, hp, heq⟩ := Finset.mem_image.mp (Finset.min'_mem distances hne)
        have hneq := (Finset.mem_filter.mp hp).2
        rw [← heq]
        exact dist_pos.mpr hneq
      · intro n m hnm
        apply Finset.min'_le
        apply Finset.mem_image.mpr
        exact ⟨(v n, v m), Finset.mem_filter.mpr ⟨Finset.mem_product.mpr ⟨hmem n, hmem m⟩, hnm⟩, rfl⟩
    · refine ⟨1, by norm_num, ?_⟩
      intro n m hnm
      exfalso
      apply hne
      exact ⟨dist (v n) (v m), Finset.mem_image.mpr
        ⟨(v n, v m), Finset.mem_filter.mpr ⟨Finset.mem_product.mpr ⟨hmem n, hmem m⟩, hnm⟩, rfl⟩⟩
  obtain ⟨δ, hδ, hsep⟩ := hseparation
  obtain ⟨N, hN⟩ := tendsto_of_separated_approximants u v δ hδ hsep happrox hstep
  exact ⟨v N, hmem N, hN⟩

theorem tendsto_of_finite_template_approximation
    {X : Type*} [MetricSpace X] (u : ℕ → X) (F : Finset X)
    (hclose : ∀ ε : ℝ, 0 < ε → ∀ᶠ n in atTop, ∃ p ∈ F, dist (u n) p < ε)
    (hstep : Tendsto (fun n => dist (u (n + 1)) (u n)) atTop (𝓝 0)) :
    ∃ p ∈ F, Tendsto u atTop (𝓝 p) := by
  classical
  obtain ⟨n, hn⟩ := (hclose 1 zero_lt_one).exists
  obtain ⟨p, hp, _⟩ := hn
  have hF : (F : Set X).Nonempty := ⟨p, hp⟩
  choose v hv hmin using fun n : ℕ =>
    Set.exists_min_image (F : Set X) (fun p => dist (u n) p) F.finite_toSet hF
  have happrox : Tendsto (fun n => dist (u n) (v n)) atTop (𝓝 0) := by
    apply tendsto_order.mpr
    constructor
    · intro a ha
      exact Eventually.of_forall (fun _ => ha.trans_le dist_nonneg)
    · intro ε hε
      filter_upwards [hclose ε hε] with n hn
      obtain ⟨p, hp, hnear⟩ := hn
      exact (hmin n p hp).trans_lt hnear
  exact tendsto_of_finite_approximants u v F hv happrox hstep

end Erdos335
