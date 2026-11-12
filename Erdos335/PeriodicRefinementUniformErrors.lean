import Erdos335.PeriodicRefinementCompactness

/-!
# Uniform error sequences for compact-open cumulative limits
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Filter Set Topology

noncomputable section

namespace Erdos335.PeriodicRefinement

theorem exists_compact_uniform_error
    (f : ℕ → C(ℝ, ℝ)) (F : C(ℝ, ℝ)) (hlim : Tendsto f atTop (𝓝 F)) (L : ℝ) :
    ∃ ε : ℕ → ℝ, (∀ n, 0 ≤ ε n) ∧ Tendsto ε atTop (𝓝 0) ∧
      ∀ n t, t ∈ Set.Icc (0 : ℝ) L → |f n t - F t| ≤ ε n := by
  let K := Set.Icc (0 : ℝ) L
  let u : ℕ → C(K, ℝ) := fun n =>
    ⟨K.domRestrict (f n), (f n).continuous.continuousOn.domRestrict⟩
  let v : C(K, ℝ) := ⟨K.domRestrict F, F.continuous.continuousOn.domRestrict⟩
  have hU : Tendsto u atTop (𝓝 v) := by
    have hcompact : IsCompact K := isCompact_Icc
    have h := (ContinuousMap.tendsto_iff_forall_isCompact_tendstoUniformlyOn.mp hlim) K hcompact
    exact
      (F.continuous.continuousOn.tendsto_domRestrict_iff_tendstoUniformlyOn
        (fun n => (f n).continuous.continuousOn)).mpr h
  refine ⟨fun n => dist (u n) v, fun _ => dist_nonneg, ?_, ?_⟩
  · have hv : Tendsto (fun _ : ℕ => v) atTop (𝓝 v) := tendsto_const_nhds
    simpa only [dist_self] using hU.dist hv
  · intro n t ht
    have hb := ContinuousMap.dist_apply_le_dist (f := u n) (g := v) ⟨t, ht⟩
    rw [Real.dist_eq] at hb
    exact hb

end Erdos335.PeriodicRefinement

end
