import Erdos335.PeriodicRefinementMacroAssemblyLabels
import Erdos335.PeriodicRefinementGlobalClusters
import Erdos335.PeriodicRefinementCumulativeDensity

/-!
# From macroscopic local profiles to a fixed periodic input coordinate

Private proof development. Verification status is recorded separately. The cumulative functions and their
almost-everywhere local profiles are explicit upstream data. This module
assembles their label and finite-slice consequences.
-/

set_option autoImplicit false
set_option maxHeartbeats 1200000

open Filter Set Topology MeasureTheory
open MeasureTheory.Measure
open Erdos335.PeriodicRefinementLabelClosure
open scoped Pointwise BigOperators NNReal

noncomputable section

namespace Erdos335.PeriodicRefinementMacroAssembly

variable {G : Type*} [AddCommGroup G] [Fintype G] [DecidableEq G]

structure MacroProfileData (R S : Finset G) (a b : ℝ) where
  leftCumulative : G → ℝ → ℝ
  rightCumulative : G → ℝ → ℝ
  leftLipschitzConstant : ℝ≥0
  rightLipschitzConstant : ℝ≥0
  leftLipschitz : ∀ r, LipschitzWith leftLipschitzConstant (leftCumulative r)
  rightLipschitz : ∀ r, LipschitzWith rightLipschitzConstant (rightCumulative r)
  leftZero : ∀ r, leftCumulative r 0 = 0
  rightZero : ∀ r, rightCumulative r 0 = 0
  profile : ℝ → LocalProfile R S a b
  leftMeasurable : ∀ r, Measurable (fun t => (profile t).left r)
  rightMeasurable : ∀ r, Measurable (fun t => (profile t).right r)
  leftDerivative : ∀ᵐ t : ℝ, 0 < t →
    ∀ r, deriv (leftCumulative r) t = (profile t).left r
  rightDerivative : ∀ᵐ t : ℝ, 0 < t →
    ∀ r, deriv (rightCumulative r) t = (profile t).right r
  frames : ∀ᵐ t : ℝ, 0 < t →
    ∃ label, HasLabel (profile t) label ∧ LabelFrame (profile t) label
  cross : ∀ᵐ w : ℝ × ℝ ∂volume.prod volume,
    0 < w.1 → 0 < w.2 →
      CrossInequality (profile w.1) (profile w.2) (profile (w.1 + w.2))

def MacroProfileData.endpoint {R S : Finset G} {a b : ℝ}
    (d : MacroProfileData R S a b) : ProfilePair G :=
  (fun r => d.leftCumulative r 1, fun r => d.rightCumulative r 1)

theorem cumulative_mask_at_one
    (F : G → ℝ → ℝ) (K : ℝ≥0) (P : Finset G)
    (hF : ∀ r, LipschitzWith K (F r)) (hzero : ∀ r, F r 0 = 0)
    (hderiv : ∀ᵐ t : ℝ, 0 < t → ∀ r, deriv (F r) t = maskVector P r) :
    (fun r => F r 1) = maskVector P := by
  funext r
  have hd : ∀ᵐ t : ℝ, 0 < t → deriv (F r) t = maskVector P r := by
    filter_upwards [hderiv] with t ht hpos
    exact ht hpos r
  simpa only [one_mul] using PeriodicRefinement.cumulative_value_of_ae_derivative
    (F r) K (hF r) (hzero r) (maskVector P r) 1 zero_le_one hd

theorem MacroProfileData.left_endpoint_of_ae_indicator
    {R S : Finset G} {a b : ℝ} (d : MacroProfileData R S a b) (P : Finset G)
    (hP : ∀ᵐ t : ℝ, 0 < t → IsIndicator (d.profile t).left P) :
    d.endpoint.1 = maskVector P := by
  apply cumulative_mask_at_one d.leftCumulative d.leftLipschitzConstant P
    d.leftLipschitz d.leftZero
  filter_upwards [d.leftDerivative, hP] with t hderiv hprofile hpos
  intro r
  exact (hderiv hpos r).trans (hprofile hpos r)

theorem MacroProfileData.right_endpoint_of_ae_indicator
    {R S : Finset G} {a b : ℝ} (d : MacroProfileData R S a b) (Q : Finset G)
    (hQ : ∀ᵐ t : ℝ, 0 < t → IsIndicator (d.profile t).right Q) :
    d.endpoint.2 = maskVector Q := by
  apply cumulative_mask_at_one d.rightCumulative d.rightLipschitzConstant Q
    d.rightLipschitz d.rightZero
  filter_upwards [d.rightDerivative, hQ] with t hderiv hprofile hpos
  intro r
  exact (hderiv hpos r).trans (hprofile hpos r)

theorem MacroProfileData.endpoint_mem_slice_of_ae_label
    {R S : Finset G} {a b : ℝ} (d : MacroProfileData R S a b) (label : LocalLabel G)
    (hlabel : ∀ᵐ t : ℝ, 0 < t → HasLabel (d.profile t) label) :
    d.endpoint ∈ periodicInputSlice R S a b label := by
  have hunit : volume (Ioo (0 : ℝ) 1) ≠ 0 := by simp
  obtain ⟨t, ht, htag⟩ := exists_mem_of_measure_ne_zero_of_ae hunit
    (ae_restrict_of_ae hlabel)
  have htag := htag ht.1
  cases label with
  | left P =>
    refine ⟨d.left_endpoint_of_ae_indicator P ?_, htag.2⟩
    filter_upwards [hlabel] with t ht hpos
    exact (ht hpos).1
  | right Q =>
    refine ⟨d.right_endpoint_of_ae_indicator Q ?_, htag.2⟩
    filter_upwards [hlabel] with t ht hpos
    exact (ht hpos).1
  | both P Q =>
    refine ⟨d.left_endpoint_of_ae_indicator P ?_, d.right_endpoint_of_ae_indicator Q ?_,
      htag.2.2.1, htag.2.2.2⟩
    · filter_upwards [hlabel] with t ht hpos
      exact (ht hpos).1
    · filter_upwards [hlabel] with t ht hpos
      exact (ht hpos).2.1

theorem MacroProfileData.exists_endpoint_slice
    {R S : Finset G} {a b : ℝ} (d : MacroProfileData R S a b)
    (ha : 0 < a) (hb : 0 < b) (hgap : a + b < ((R + S).card : ℝ)) :
    ∃ label, d.endpoint ∈ periodicInputSlice R S a b label := by
  obtain ⟨label, hlabel⟩ := exists_ae_profile_label d.profile ha hb hgap
    d.leftMeasurable d.rightMeasurable d.frames d.cross
  exact ⟨label, d.endpoint_mem_slice_of_ae_label label hlabel⟩

theorem exists_single_prefix_cluster_slice
    {R S : Finset G} {a b : ℝ}
    (u : ℕ → ProfilePair G) (K : Set (ProfilePair G))
    (ha : 0 < a) (hb : 0 < b) (hgap : a + b < ((R + S).card : ℝ))
    (hK : IsCompact K) (hmem : ∀ᶠ n in atTop, u n ∈ K)
    (hstep : Tendsto (fun n => dist (u (n + 1)) (u n)) atTop (𝓝 0))
    (hmacro : ∀ v, MapClusterPt v atTop u →
      ∃ d : MacroProfileData R S a b, d.endpoint = v)
    (hdisjoint : ∀ label target : LocalLabel G, label ≠ target →
      ∀ v, MapClusterPt v atTop u →
        v ∈ periodicInputSlice R S a b label →
        v ∈ periodicInputSlice R S a b target → False) :
    ∃ label, ∀ v, MapClusterPt v atTop u →
      v ∈ periodicInputSlice R S a b label := by
  classical
  letI : Fintype (LocalLabel G) := Fintype.ofFinite _
  apply PeriodicRefinementGlobal.exists_single_closed_cluster_slice
    u K (periodicInputSlice R S a b) hK hmem
    (isClosed_periodicInputSlice R S a b) ?_ hdisjoint hstep
  intro v hv
  obtain ⟨d, hd⟩ := hmacro v hv
  obtain ⟨label, hlabel⟩ := d.exists_endpoint_slice ha hb hgap
  exact ⟨label, hd ▸ hlabel⟩

theorem exists_periodic_coordinate_limit
    {R S : Finset G} {a b : ℝ}
    (u : ℕ → ProfilePair G) (K : Set (ProfilePair G))
    (ha : 0 < a) (hb : 0 < b) (hgap : a + b < ((R + S).card : ℝ))
    (hK : IsCompact K) (hmem : ∀ᶠ n in atTop, u n ∈ K)
    (hstep : Tendsto (fun n => dist (u (n + 1)) (u n)) atTop (𝓝 0))
    (hmacro : ∀ v, MapClusterPt v atTop u →
      ∃ d : MacroProfileData R S a b, d.endpoint = v)
    (hdisjoint : ∀ label target : LocalLabel G, label ≠ target →
      ∀ v, MapClusterPt v atTop u →
        v ∈ periodicInputSlice R S a b label →
        v ∈ periodicInputSlice R S a b target → False) :
    (∃ P : Finset G, Tendsto (fun n => (u n).1) atTop (𝓝 (maskVector P))) ∨
      (∃ Q : Finset G, Tendsto (fun n => (u n).2) atTop (𝓝 (maskVector Q))) := by
  obtain ⟨label, hcluster⟩ := exists_single_prefix_cluster_slice
    u K ha hb hgap hK hmem hstep hmacro hdisjoint
  cases label with
  | left P =>
    left
    refine ⟨P, ?_⟩
    exact PeriodicRefinementGlobal.tendsto_of_compact_cluster_slice_constant
      u K (periodicInputSlice R S a b (.left P)) Prod.fst (maskVector P)
      hK hmem hcluster continuous_fst (fun _ hv => hv.1)
  | right Q =>
    right
    refine ⟨Q, ?_⟩
    exact PeriodicRefinementGlobal.tendsto_of_compact_cluster_slice_constant
      u K (periodicInputSlice R S a b (.right Q)) Prod.snd (maskVector Q)
      hK hmem hcluster continuous_snd (fun _ hv => hv.1)
  | both P Q =>
    left
    refine ⟨P, ?_⟩
    exact PeriodicRefinementGlobal.tendsto_of_compact_cluster_slice_constant
      u K (periodicInputSlice R S a b (.both P Q)) Prod.fst (maskVector P)
      hK hmem hcluster continuous_fst (fun _ hv => hv.1)

theorem exists_periodic_coordinate_limit_of_cluster_profiles
    {R S : Finset G} {a b : ℝ}
    (u : ℕ → ProfilePair G) (K : Set (ProfilePair G))
    (ha : 0 < a) (hb : 0 < b) (hgap : a + b < ((R + S).card : ℝ))
    (hK : IsCompact K) (hmem : ∀ᶠ n in atTop, u n ∈ K)
    (hstep : Tendsto (fun n => dist (u (n + 1)) (u n)) atTop (𝓝 0))
    (hmacro : ∀ v, MapClusterPt v atTop u →
      ∃ d : MacroProfileData R S a b, d.endpoint = v)
    (hprefix : ∀ v, MapClusterPt v atTop u →
      ∃ p : LocalProfile R S a b, p.left = v.1 ∧ p.right = v.2) :
    (∃ P : Finset G, Tendsto (fun n => (u n).1) atTop (𝓝 (maskVector P))) ∨
      (∃ Q : Finset G, Tendsto (fun n => (u n).2) atTop (𝓝 (maskVector Q))) := by
  apply exists_periodic_coordinate_limit u K ha hb hgap hK hmem hstep hmacro
  intro label target hne v hv hlabel htarget
  obtain ⟨p, hleft, hright⟩ := hprefix v hv
  exact hne (label_eq_of_local_profile_slices p ha hb hgap v hleft hright
    label target hlabel htarget)

end Erdos335.PeriodicRefinementMacroAssembly

end
