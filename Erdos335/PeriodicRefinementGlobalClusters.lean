import Erdos335.FiniteProfileConvergence
import Mathlib.Topology.Compactness.Compact
import Mathlib.Topology.MetricSpace.Thickening
import Mathlib.Topology.Order.Compact
import Mathlib.Topology.Sequences

/-!
# Finite closed slices of a slowly varying bounded sequence

Private proof development. Verification status is recorded separately. The compact slices may contain many
points. Only their labels become fixed. The sequence itself can continue
to vary inside the selected slice.
-/

set_option autoImplicit false
set_option maxHeartbeats 1000000

open Filter Set Topology Metric

noncomputable section

namespace Erdos335.PeriodicRefinementGlobal

theorem eventually_constant_of_separated_slice_approximants
    {X I : Type*} [MetricSpace X]
    (u v : ℕ → X) (label : ℕ → I) (δ : ℝ) (hδ : 0 < δ)
    (hsep : ∀ n m, label n ≠ label m → δ ≤ dist (v n) (v m))
    (happrox : Tendsto (fun n => dist (u n) (v n)) atTop (𝓝 0))
    (hstep : Tendsto (fun n => dist (u (n + 1)) (u n)) atTop (𝓝 0)) :
    ∃ i, ∀ᶠ n in atTop, label n = i := by
  have hnext := happrox.comp (tendsto_add_atTop_nat 1)
  have hbound (n : ℕ) : dist (v (n + 1)) (v n) ≤
      dist (u (n + 1)) (v (n + 1)) +
        dist (u (n + 1)) (u n) + dist (u n) (v n) := by
    calc
      dist (v (n + 1)) (v n) ≤
          dist (v (n + 1)) (u (n + 1)) + dist (u (n + 1)) (v n) :=
        dist_triangle _ _ _
      _ ≤ dist (v (n + 1)) (u (n + 1)) +
          (dist (u (n + 1)) (u n) + dist (u n) (v n)) :=
        add_le_add le_rfl (dist_triangle _ _ _)
      _ = _ := by rw [dist_comm (v (n + 1)) (u (n + 1))]; ring
  have hlim : Tendsto (fun n => dist (v (n + 1)) (v n)) atTop (𝓝 0) :=
    squeeze_zero (fun _ => dist_nonneg) hbound
      (by simpa using (hnext.add hstep).add happrox)
  have hlabels : ∀ᶠ n in atTop, label (n + 1) = label n := by
    filter_upwards [(tendsto_order.mp hlim).2 δ hδ] with n hn
    by_contra hne
    exact (not_le_of_gt hn) (hsep (n + 1) n hne)
  obtain ⟨N, hN⟩ := eventually_atTop.mp hlabels
  refine ⟨label N, eventually_atTop.mpr ⟨N, ?_⟩⟩
  intro n hn
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hn
  induction k with
  | zero => simp
  | succ k ih =>
    calc
      label (N + (k + 1)) = label ((N + k) + 1) := by congr 1
      _ = label (N + k) := hN _ (by omega)
      _ = label N := ih (by omega)

theorem compact_disjoint_slices_separated
    {X I : Type*} [MetricSpace X] [Fintype I]
    (S : I → Set X) (hcompact : ∀ i, IsCompact (S i))
    (hdisjoint : ∀ i j, i ≠ j → Disjoint (S i) (S j)) :
    ∃ δ : ℝ, 0 < δ ∧
      ∀ i j, i ≠ j → ∀ x ∈ S i, ∀ y ∈ S j, δ ≤ dist x y := by
  classical
  have hp (p : I × I) : ∃ δ : ℝ, 0 < δ ∧
      ∀ x ∈ S p.1, ∀ y ∈ S p.2, p.1 ≠ p.2 → δ ≤ dist x y := by
    by_cases hij : p.1 = p.2
    · exact ⟨1, zero_lt_one, fun _ _ _ _ h => (h hij).elim⟩
    by_cases hne : (S p.1 ×ˢ S p.2).Nonempty
    · obtain ⟨z, hz, hmin⟩ := ((hcompact p.1).prod (hcompact p.2)).exists_isMinOn hne
        (continuous_fst.dist continuous_snd).continuousOn
      have hneq : z.1 ≠ z.2 := by
        intro heq
        exact (Set.disjoint_left.mp (hdisjoint p.1 p.2 hij)) hz.1 (heq.symm ▸ hz.2)
      refine ⟨dist z.1 z.2, dist_pos.mpr hneq, ?_⟩
      intro x hx y hy _
      exact hmin (show (x, y) ∈ S p.1 ×ˢ S p.2 from ⟨hx, hy⟩)
    · refine ⟨1, zero_lt_one, ?_⟩
      intro x hx y hy _
      exact (hne ⟨(x, y), hx, hy⟩).elim
  choose d hdpos hd using hp
  by_cases hne : (Finset.univ : Finset (I × I)).Nonempty
  · let values := (Finset.univ : Finset (I × I)).image d
    have hv : values.Nonempty := hne.image d
    refine ⟨values.min' hv, ?_, ?_⟩
    · obtain ⟨p, _, hpmin⟩ := Finset.mem_image.mp (Finset.min'_mem values hv)
      rw [← hpmin]
      exact hdpos p
    · intro i j hij x hx y hy
      exact (Finset.min'_le values (d (i, j))
        (Finset.mem_image.mpr ⟨(i, j), Finset.mem_univ _, rfl⟩)).trans
        (hd (i, j) x hx y hy hij)
  · refine ⟨1, zero_lt_one, ?_⟩
    intro i j _ _ _ _ _
    exact (hne ⟨(i, j), Finset.mem_univ _⟩).elim

theorem exists_single_compact_cluster_slice
    {X I : Type*} [MetricSpace X] [Fintype I]
    (u : ℕ → X) (K : Set X) (S : I → Set X)
    (hK : IsCompact K) (hmem : ∀ᶠ n in atTop, u n ∈ K)
    (hcompact : ∀ i, IsCompact (S i))
    (hdisjoint : ∀ i j, i ≠ j → Disjoint (S i) (S j))
    (hcover : ∀ x, MapClusterPt x atTop u → ∃ i, x ∈ S i)
    (hstep : Tendsto (fun n => dist (u (n + 1)) (u n)) atTop (𝓝 0)) :
    ∃ i, ∀ x, MapClusterPt x atTop u → x ∈ S i := by
  classical
  let U : Set X := ⋃ i, S i
  have hU : IsCompact U := isCompact_iUnion hcompact
  obtain ⟨x₀, _, hx₀⟩ := hK.exists_mapClusterPt_of_frequently hmem.frequently
  obtain ⟨i₀, hi₀⟩ := hcover x₀ hx₀
  have hUne : U.Nonempty := ⟨x₀, Set.mem_iUnion.mpr ⟨i₀, hi₀⟩⟩
  have hnear : Tendsto u atTop (𝓝ˢ U) :=
    hK.tendsto_nhdsSet_of_mapClusterPt hmem
      (fun x _ hx => Set.mem_iUnion.mpr (hcover x hx))
  have hex (n : ℕ) : ∃ p ∈ U, ∀ q ∈ U, dist (u n) p ≤ dist (u n) q := by
    obtain ⟨p, hp, hmin⟩ := hU.exists_isMinOn hUne
      (continuous_const.dist continuous_id).continuousOn
    exact ⟨p, hp, fun q hq => hmin hq⟩
  choose p hp hmin using hex
  have hlabel (n : ℕ) : ∃ i, p n ∈ S i := Set.mem_iUnion.mp (hp n)
  choose label hlabel using hlabel
  have happrox : Tendsto (fun n => dist (u n) (p n)) atTop (𝓝 0) := by
    apply tendsto_order.mpr
    constructor
    · intro a ha
      exact Eventually.of_forall (fun _ => ha.trans_le dist_nonneg)
    · intro ε hε
      filter_upwards [hnear (Metric.thickening_mem_nhdsSet U hε)] with n hn
      obtain ⟨q, hq, hdist⟩ := Metric.mem_thickening_iff.mp hn
      exact (hmin n q hq).trans_lt hdist
  obtain ⟨δ, hδ, hsep⟩ := compact_disjoint_slices_separated S hcompact hdisjoint
  obtain ⟨i, hi⟩ := eventually_constant_of_separated_slice_approximants u p label δ hδ
    (fun n m hnm => hsep (label n) (label m) hnm (p n) (hlabel n) (p m) (hlabel m))
    happrox hstep
  refine ⟨i, ?_⟩
  intro x hx
  apply (hcompact i).isClosed.closure_subset
  rw [Metric.mem_closure_iff]
  intro ε hε
  have hfreq := hx.frequently (Metric.ball_mem_nhds x (half_pos hε))
  obtain ⟨n, hnball, hnclose, hni⟩ :=
    (hfreq.and_eventually (((tendsto_order.mp happrox).2 (ε / 2) (half_pos hε)).and hi)).exists
  refine ⟨p n, ?_, ?_⟩
  · simpa only [hni] using hlabel n
  · have hball : dist (u n) x < ε / 2 := Metric.mem_ball.mp hnball
    have htotal : dist (p n) x < ε := by
      calc
        dist (p n) x ≤ dist (p n) (u n) + dist (u n) x := dist_triangle _ _ _
        _ < ε / 2 + ε / 2 := add_lt_add (by simpa only [dist_comm] using hnclose) hball
        _ = ε := by ring
    simpa only [dist_comm] using htotal

theorem tendsto_of_compact_cluster_slice_constant
    {X Y : Type*} [MetricSpace X] [TopologicalSpace Y]
    (u : ℕ → X) (K S : Set X) (f : X → Y) (c : Y)
    (hK : IsCompact K) (hmem : ∀ᶠ n in atTop, u n ∈ K)
    (hcluster : ∀ x, MapClusterPt x atTop u → x ∈ S)
    (hf : Continuous f) (hconstant : ∀ x ∈ S, f x = c) :
    Tendsto (fun n => f (u n)) atTop (𝓝 c) := by
  have hu : Tendsto u atTop (𝓝ˢ S) :=
    hK.tendsto_nhdsSet_of_mapClusterPt hmem (fun x _ hx => hcluster x hx)
  have hfc : Tendsto f (𝓝ˢ S) (𝓝 c) := by
    apply Filter.tendsto_def.mpr
    intro V hV
    apply mem_nhdsSet_iff_forall.mpr
    intro x hx
    exact hf.continuousAt.preimage_mem_nhds (by simpa only [hconstant x hx] using hV)
  exact hfc.comp hu

theorem exists_single_closed_cluster_slice
    {X I : Type*} [MetricSpace X] [Fintype I]
    (u : ℕ → X) (K : Set X) (S : I → Set X)
    (hK : IsCompact K) (hmem : ∀ᶠ n in atTop, u n ∈ K)
    (hclosed : ∀ i, IsClosed (S i))
    (hcover : ∀ x, MapClusterPt x atTop u → ∃ i, x ∈ S i)
    (hdisjoint : ∀ i j, i ≠ j → ∀ x, MapClusterPt x atTop u →
      x ∈ S i → x ∈ S j → False)
    (hstep : Tendsto (fun n => dist (u (n + 1)) (u n)) atTop (𝓝 0)) :
    ∃ i, ∀ x, MapClusterPt x atTop u → x ∈ S i := by
  let C : Set X := {x | MapClusterPt x atTop u}
  let slices : I → Set X := fun i => K ∩ (C ∩ S i)
  have hCclosed : IsClosed C := isClosed_setOfPred_clusterPt
  have hslices : ∀ i, IsCompact (slices i) :=
    fun i => hK.inter_right (hCclosed.inter (hclosed i))
  have hpairwise : ∀ i j, i ≠ j → Disjoint (slices i) (slices j) := by
    intro i j hij
    apply Set.disjoint_left.mpr
    intro x hxi hxj
    exact hdisjoint i j hij x hxi.2.1 hxi.2.2 hxj.2.2
  have hcover' : ∀ x, MapClusterPt x atTop u → ∃ i, x ∈ slices i := by
    intro x hx
    obtain ⟨i, hi⟩ := hcover x hx
    exact ⟨i, hK.isClosed.mem_of_mapClusterPt hx hmem, hx, hi⟩
  obtain ⟨i, hi⟩ := exists_single_compact_cluster_slice u K slices hK hmem hslices
    hpairwise hcover' hstep
  exact ⟨i, fun x hx => (hi x hx).2.2⟩

end Erdos335.PeriodicRefinementGlobal

end
