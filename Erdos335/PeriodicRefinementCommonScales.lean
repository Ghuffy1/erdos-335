import Erdos335.PeriodicRefinementCommonScalesEnvelope
import Erdos335.PeriodicRefinementCommonScalesDiagonal
import Erdos335.IntermediateFourierModel
import Erdos335.SparseScaleSubsequence

/-!
# Shared Fourier windows for all fixed ambient enlargements

Private proof development. Verification status is recorded separately. The functions and ambient multipliers form an
arbitrary countable family. Error domination is retained on the same final
subsequence as every Fourier model.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2000000

open Filter Topology
open scoped BigOperators

noncomputable section

namespace Erdos335.IntermediateScale

def IntermediateFourierModel.ambientCongr
    {F : ℕ → ℝ} {N N' L V : ℕ → ℕ}
    (model : IntermediateFourierModel F N L V) (hNN' : N =ᶠ[atTop] N') :
    IntermediateFourierModel F N' L V where
  structured := model.structured
  dimension := model.dimension
  coefficient := model.coefficient
  frequency := model.frequency
  bounded := model.bounded
  coefficient_bound := model.coefficient_bound
  approximation := by
    intro δ hδ
    obtain ⟨k, hk⟩ := model.approximation δ hδ
    refine ⟨k, ?_⟩
    filter_upwards [hk, hNN'] with n hn heq
    simpa only [← heq] using hn
  control := by
    intro W hW hLW hWV
    obtain ⟨hfirst, hsecond, hthird⟩ := model.control W hW hLW hWV
    refine ⟨?_, ?_, ?_⟩
    · apply hfirst.congr'
      filter_upwards [hNN'] with n hn
      rw [hn]
    · intro k
      apply (hsecond k).congr'
      filter_upwards [hNN'] with n hn
      rw [hn]
    · intro k C hC
      apply (hthird k C hC).congr'
      filter_upwards [hNN'] with n hn
      rw [hn]

private structure RefinementStage
    (F : ℕ → ℕ → ℝ) (multiple : ℕ → ℕ+) (N : ℕ → ℕ) (n : ℕ) where
  index : ℕ → ℕ
  index_strict : StrictMono index
  lower : ℕ → ℕ
  upper : ℕ → ℕ
  lower_positive : ∀ s, 0 < lower s
  upper_positive : ∀ s, 0 < upper s
  lower_tendsto : Tendsto lower atTop atTop
  ratio : Tendsto (fun s => (lower s : ℝ) / upper s) atTop (𝓝 0)
  upper_inside : ∀ᶠ s in atTop, upper s ≤ N (index s)
  model : ∀ j, j < n → IntermediateFourierModel (F j)
    (fun s => (multiple j : ℕ) * N (index s)) lower upper

private structure RefinementExtension
    {F : ℕ → ℕ → ℝ} {multiple : ℕ → ℕ+} {N : ℕ → ℕ} {n : ℕ}
    (stage : RefinementStage F multiple N n) where
  next : RefinementStage F multiple N (n + 1)
  index : ℕ → ℕ
  index_strict : StrictMono index
  index_equation : next.index = stage.index ∘ index
  lower_refine : ∀ᶠ s in atTop, stage.lower (index s) ≤ next.lower s
  upper_refine : ∀ᶠ s in atTop, next.upper s ≤ stage.upper (index s)

private def refinementStage_extend
    (F : ℕ → ℕ → ℝ) (multiple : ℕ → ℕ+) (N : ℕ → ℕ)
    (hF : ∀ j n, F j n ∈ Set.Icc (0 : ℝ) 1)
    (hNpos : ∀ s, 0 < N s) (hN : Tendsto N atTop atTop) (hmono : Monotone N)
    (hprev : Tendsto (fun s => (N (s - 1) : ℝ) / N s) atTop (𝓝 0))
    (U : Ultrafilter ℕ) (hU : (U : Filter ℕ) ≤ atTop)
    (n : ℕ) (stage : RefinementStage F multiple N n) : RefinementExtension stage := Classical.choice (by
  let ambient := fun s => (multiple n : ℕ) * N (stage.index s)
  have hambpos (s : ℕ) : 0 < ambient s := Nat.mul_pos (multiple n).pos (hNpos _)
  letI : ∀ s, NeZero (ambient s) := fun s => ⟨(hambpos s).ne'⟩
  have hbase := hN.comp stage.index_strict.tendsto_atTop
  have hamb : Tendsto ambient atTop atTop := by
    apply tendsto_atTop_mono' atTop _ hbase
    exact Eventually.of_forall fun s => by
      dsimp only [ambient, Function.comp_apply]
      have hp := (multiple n).pos
      nlinarith
  have hambmono : Monotone ambient := by
    intro i j hij
    exact Nat.mul_le_mul_left _ (hmono (stage.index_strict.monotone hij))
  have hbaseprev := sparse_prefix_ratio_subsequence N hmono hprev stage.index stage.index_strict
  have hambprev : Tendsto (fun s => (ambient (s - 1) : ℝ) / ambient s) atTop (𝓝 0) := by
    apply hbaseprev.congr
    intro s
    dsimp only [ambient, Function.comp_apply]
    push_cast
    have hm : ((multiple n : ℕ) : ℝ) ≠ 0 := by exact_mod_cast (multiple n).ne_zero
    have hn : (N (stage.index s) : ℝ) ≠ 0 := by exact_mod_cast (hNpos _).ne'
    field_simp [hm, hn] <;> ring
  have hupper := scale_tendsto_atTop_of_smaller stage.lower stage.upper
    stage.lower_tendsto stage.upper_positive stage.ratio
  have hreverse := reciprocal_scale_ratio_tendsto_atTop stage.lower stage.upper
    stage.lower_positive stage.upper_positive stage.ratio
  have hinside : ∀ᶠ s in atTop, stage.upper s ≤ ambient s := by
    filter_upwards [stage.upper_inside] with s hs
    have hp := (multiple n).pos
    dsimp only [ambient, Function.comp_apply]
    nlinarith
  obtain ⟨ρ, L, V, hρ, _, hpos, hL, hlo, hLV, hhi, ⟨newModel⟩⟩ :=
    exists_intermediate_fourier_model ambient hamb hambmono hambprev stage.lower stage.upper
      stage.lower_tendsto hupper hreverse hinside (F n) (hF n) U hU
  have hlowLe : ∀ᶠ s in atTop, stage.lower (ρ s) ≤ L s :=
    eventually_scale_le_of_ratio_zero (stage.lower ∘ ρ) L (fun s => (hpos s).1) hlo
  have huppLe : ∀ᶠ s in atTop, V s ≤ stage.upper (ρ s) :=
    eventually_scale_le_of_ratio_zero V (stage.upper ∘ ρ)
      (fun s => stage.upper_positive (ρ s)) hhi
  let next : RefinementStage F multiple N (n + 1) := {
    index := stage.index ∘ ρ
    index_strict := stage.index_strict.comp hρ
    lower := L
    upper := V
    lower_positive := fun s => (hpos s).1
    upper_positive := fun s => (hpos s).2
    lower_tendsto := hL
    ratio := hLV
    upper_inside := by
      filter_upwards [huppLe, hρ.tendsto_atTop.eventually stage.upper_inside] with s hs ht
      exact hs.trans ht
    model := by
      intro j hj
      by_cases hold : j < n
      · exact (stage.model j hold).restrict stage.lower_positive stage.upper_positive
          stage.lower_tendsto stage.ratio ρ hρ L V
          (fun s => (hpos s).1) (fun s => (hpos s).2) hlo hhi
      · have heq : j = n := by omega
        subst j
        exact newModel
  }
  exact ⟨⟨next, ρ, hρ, rfl, hlowLe, huppLe⟩⟩)

theorem exists_periodic_refinement_common_scales
    (N : ℕ → ℕ) (hNpos : ∀ s, 0 < N s)
    (hN : Tendsto N atTop atTop) (hmono : Monotone N)
    (hprev : Tendsto (fun s => (N (s - 1) : ℝ) / N s) atTop (𝓝 0))
    (F : ℕ → ℕ → ℝ) (multiple : ℕ → ℕ+)
    (hF : ∀ j n, F j n ∈ Set.Icc (0 : ℝ) 1)
    (error : ℕ → ℕ → ℝ)
    (herror : ∀ j, Tendsto (fun s => error j s / N s) atTop (𝓝 0))
    (U : Ultrafilter ℕ) (hU : (U : Filter ℕ) ≤ atTop) :
    ∃ τ L V H : ℕ → ℕ,
      StrictMono τ ∧
      Tendsto (fun s => (N (τ (s - 1)) : ℝ) / N (τ s)) atTop (𝓝 0) ∧
      (∀ s, 0 < L s ∧ 0 < V s ∧ 0 < H s) ∧
      Tendsto L atTop atTop ∧ Tendsto H atTop atTop ∧
      Tendsto (fun s => (L s : ℝ) / H s) atTop (𝓝 0) ∧
      Tendsto (fun s => (H s : ℝ) / V s) atTop (𝓝 0) ∧
      Tendsto (fun s => (H s : ℝ) / N (τ s)) atTop (𝓝 0) ∧
      (∀ j, Tendsto (fun s => error j (τ s) / H s) atTop (𝓝 0)) ∧
      ∀ j, Nonempty (IntermediateFourierModel (F j)
        (fun s => (multiple j : ℕ) * N (τ s)) L V) := by
  classical
  obtain ⟨K, hKpos, hK, hKN, herrorK⟩ :=
    exists_countable_sublinear_error_scale N hNpos hN error herror
  let initial : RefinementStage F multiple N 0 := {
    index := id
    index_strict := strictMono_id
    lower := K
    upper := N
    lower_positive := hKpos
    upper_positive := hNpos
    lower_tendsto := hK
    ratio := hKN
    upper_inside := Eventually.of_forall fun _ => le_rfl
    model := by intro j hj; omega
  }
  let extend := refinementStage_extend F multiple N hF hNpos hN hmono hprev U hU
  let stages : (n : ℕ) → RefinementStage F multiple N n :=
    Nat.rec initial (fun n stage => (extend n stage).next)
  let index := fun n => (stages n).index
  let ρ := fun n => (extend n (stages n)).index
  let lower := fun n => (stages n).lower
  let upper := fun n => (stages n).upper
  have hindex (j : ℕ) : StrictMono (index j) := (stages j).index_strict
  have hρ (j : ℕ) : StrictMono (ρ j) := (extend j (stages j)).index_strict
  have hindexStep (j : ℕ) : index (j + 1) = index j ∘ ρ j :=
    (extend j (stages j)).index_equation
  have hLowerStep (j : ℕ) : ∀ᶠ s in atTop, lower j (ρ j s) ≤ lower (j + 1) s :=
    (extend j (stages j)).lower_refine
  have hUpperStep (j : ℕ) : ∀ᶠ s in atTop, upper (j + 1) s ≤ upper j (ρ j s) :=
    (extend j (stages j)).upper_refine
  obtain ⟨τ, L, V, H, hτ, hpos, hL, hH, hLH, hHV, hHN, hfactor⟩ :=
    exists_nested_interval_diagonal N index ρ hindex hρ hindexStep lower upper
      (fun j => (stages j).lower_positive) (fun j => (stages j).upper_positive)
      (fun j => (stages j).lower_tendsto) (fun j => (stages j).ratio)
      hLowerStep hUpperStep (fun j => (stages j).upper_inside)
  obtain ⟨σ0, _, heq0, hKL, _⟩ := hfactor 0
  change Tendsto (fun n => (K (σ0 n) : ℝ) / L n) atTop (𝓝 0) at hKL
  have hKτL : Tendsto (fun s => (K (τ s) : ℝ) / L s) atTop (𝓝 0) := by
    apply hKL.congr'
    filter_upwards [heq0] with s hs
    change σ0 s = τ s at hs
    simpa only [hs]
  have hKτH : Tendsto (fun s => (K (τ s) : ℝ) / H s) atTop (𝓝 0) := by
    have ht := hKτL.mul hLH
    simp only [mul_zero] at ht
    apply ht.congr
    intro s
    have hne : (L s : ℝ) ≠ 0 := by exact_mod_cast (hpos s).1.ne'
    field_simp [hne] <;> ring
  refine ⟨τ, L, V, H, hτ, sparse_prefix_ratio_subsequence N hmono hprev τ hτ,
    hpos, hL, hH, hLH, hHV, hHN, ?_, ?_⟩
  · intro j
    have ht := ((herrorK j).comp hτ.tendsto_atTop).mul hKτH
    simp only [mul_zero] at ht
    apply ht.congr
    intro s
    have hne : (K (τ s) : ℝ) ≠ 0 := by exact_mod_cast (hKpos (τ s)).ne'
    simp only [Function.comp_apply]
    field_simp [hne] <;> ring
  · intro j
    obtain ⟨σ, hσ, heq, hlo, hhi⟩ := hfactor (j + 1)
    let old := (stages (j + 1)).model j (Nat.lt_succ_self j)
    let new := old.restrict (stages (j + 1)).lower_positive (stages (j + 1)).upper_positive
      (stages (j + 1)).lower_tendsto (stages (j + 1)).ratio σ hσ L V
      (fun s => (hpos s).1) (fun s => (hpos s).2.1) hlo hhi
    refine ⟨new.ambientCongr ?_⟩
    filter_upwards [heq] with s hs
    change (multiple j : ℕ) * N (index (j + 1) (σ s)) = (multiple j : ℕ) * N (τ s)
    rw [show index (j + 1) (σ s) = τ s from hs]

end Erdos335.IntermediateScale

end
