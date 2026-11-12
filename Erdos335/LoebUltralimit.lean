import Erdos335.LoebMeasure
import Erdos335.LoebFiniteFunctions
import Mathlib.Topology.MetricSpace.HausdorffDistance
import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic

/-!
# Compact-valued internal functions

Pointwise ultralimits of compact metric valued coordinate functions are
well-defined on the ultraproduct and are measurable for the Loeb sigma algebra.
-/

set_option autoImplicit false

open Filter Set Topology MeasureTheory

namespace Erdos335.Loeb

variable {I E : Type*} {X : I → Type*}
  [MetricSpace E] [CompactSpace E]

noncomputable def ultralimitFunction (U : Ultrafilter I) (f : ∀ i, X i → E) :
    (U : Filter I).Product X → E :=
  Quotient.lift (fun x => (U.map (fun i => f i (x i))).lim) (by
    intro x y h
    have hx : Tendsto (fun i => f i (x i)) (U : Filter I)
        (𝓝 (U.map (fun i => f i (x i))).lim) := (U.map _).le_nhds_lim
    have hy : Tendsto (fun i => f i (y i)) (U : Filter I)
        (𝓝 (U.map (fun i => f i (y i))).lim) := (U.map _).le_nhds_lim
    exact tendsto_nhds_unique hx
      (hy.congr' (h.mono fun i hi => congrArg (f i) hi.symm)))

theorem tendsto_ultralimitFunction (U : Ultrafilter I) (f : ∀ i, X i → E)
    (x : ∀ i, X i) :
    Tendsto (fun i => f i (x i)) (U : Filter I)
      (𝓝 (ultralimitFunction U f (x : (U : Filter I).Product X))) :=
  (U.map _).le_nhds_lim

theorem ultralimitFunction_mem_open_iff (U : Ultrafilter I) (f : ∀ i, X i → E)
    (S : Set E) (hS : IsOpen S) (hne : Sᶜ.Nonempty) (x : ∀ i, X i) :
    ultralimitFunction U f (x : (U : Filter I).Product X) ∈ S ↔
      ∃ m : ℕ, ∀ᶠ i in U, 1 / (m + 1 : ℝ) ≤ Metric.infDist (f i (x i)) Sᶜ := by
  have hlim := ((Metric.continuous_infDist_pt Sᶜ).tendsto
    (ultralimitFunction U f (x : (U : Filter I).Product X))).comp
      (tendsto_ultralimitFunction U f x)
  constructor
  · intro hx
    have hnot : ultralimitFunction U f (x : (U : Filter I).Product X) ∉ Sᶜ :=
      fun h => h hx
    have hpos := (hS.isClosed_compl.notMem_iff_infDist_pos hne).mp hnot
    obtain ⟨m, hm⟩ := exists_nat_one_div_lt hpos
    exact ⟨m, (hlim.eventually (lt_mem_nhds hm)).mono fun i hi => hi.le⟩
  · rintro ⟨m, hm⟩
    have hbound : 1 / (m + 1 : ℝ) ≤
        Metric.infDist (ultralimitFunction U f (x : (U : Filter I).Product X)) Sᶜ :=
      ge_of_tendsto hlim hm
    have hpos : 0 < Metric.infDist
        (ultralimitFunction U f (x : (U : Filter I).Product X)) Sᶜ :=
      (by positivity : 0 < 1 / (m + 1 : ℝ)).trans_le hbound
    by_contra hx
    change ultralimitFunction U f (x : (U : Filter I).Product X) ∈ Sᶜ at hx
    have hz := Metric.infDist_zero_of_mem hx
    rw [hz] at hpos
    exact (lt_irrefl 0) hpos

theorem ultralimitFunction_preimage_open (U : Ultrafilter I) (f : ∀ i, X i → E)
    (S : Set E) (hS : IsOpen S) (hne : Sᶜ.Nonempty) :
    ultralimitFunction U f ⁻¹' S = ⋃ m : ℕ, internalSet U
      (fun i => {x | 1 / (m + 1 : ℝ) ≤ Metric.infDist (f i x) Sᶜ}) := by
  ext x
  induction x using Quotient.inductionOn with
  | h g =>
    constructor
    · intro hx
      obtain ⟨m, hm⟩ := (ultralimitFunction_mem_open_iff U f S hS hne g).mp hx
      exact mem_iUnion.mpr ⟨m, hm⟩
    · intro hx
      obtain ⟨m, hm⟩ := mem_iUnion.mp hx
      exact (ultralimitFunction_mem_open_iff U f S hS hne g).mpr ⟨m, hm⟩

theorem measurable_ultralimitFunction
    {Y : ℕ → Type*} [∀ n, Finite (Y n)] [∀ n, Nonempty (Y n)]
    [MeasurableSpace E] [BorelSpace E] (U : Ultrafilter ℕ) (f : ∀ n, Y n → E) :
    @Measurable ((U : Filter ℕ).Product Y) E (loebMeasurableSpace U) _
      (ultralimitFunction U f) := by
  let : MeasurableSpace ((U : Filter ℕ).Product Y) := loebMeasurableSpace U
  apply measurable_of_isOpen
  intro S hS
  by_cases hne : Sᶜ.Nonempty
  · rw [ultralimitFunction_preimage_open U f S hS hne]
    exact MeasurableSet.iUnion fun m => measurable_internalSet U _
  · have hSu : S = univ := by
      apply eq_univ_of_forall
      intro x
      by_contra hx
      exact hne ⟨x, hx⟩
    rw [hSu, preimage_univ]
    exact MeasurableSet.univ

theorem ultralimitFunction_comp_continuous
    {F : Type*} [MetricSpace F] [CompactSpace F]
    (U : Ultrafilter I) (f : ∀ i, X i → E) (g : E → F) (hg : Continuous g) :
    ultralimitFunction U (fun i x => g (f i x)) = g ∘ ultralimitFunction U f := by
  funext x
  induction x using Quotient.inductionOn with
  | h a =>
    exact tendsto_nhds_unique (tendsto_ultralimitFunction U _ a)
      ((hg.tendsto _).comp (tendsto_ultralimitFunction U f a))

theorem ultralimitFunction_of_finite_index
    {G : Type*} [Finite G] (U : Ultrafilter I) (f : ∀ i, X i → G) (v : G → E) :
    ultralimitFunction U (fun i x => v (f i x)) = v ∘ finiteFunction U f := by
  funext x
  induction x using Quotient.inductionOn with
  | h a =>
    apply tendsto_nhds_unique (tendsto_ultralimitFunction U _ a)
    apply tendsto_const_nhds.congr'
    exact (eventually_eq_finiteValue U (fun i => f i (a i))).mono
      fun i hi => (congrArg v hi).symm

theorem ultralimitFunction_dist_le (U : Ultrafilter I) (f g : ∀ i, X i → E)
    (r : ℝ) (h : ∀ i x, dist (f i x) (g i x) ≤ r)
    (x : (U : Filter I).Product X) :
    dist (ultralimitFunction U f x) (ultralimitFunction U g x) ≤ r := by
  induction x using Quotient.inductionOn with
  | h a =>
    exact le_of_tendsto ((tendsto_ultralimitFunction U f a).dist
      (tendsto_ultralimitFunction U g a)) (.of_forall fun i => h i (a i))

theorem continuous_finite_approximation_bound
    {G : Type*} [Finite G] (U : Ultrafilter I) (f : ∀ i, X i → E)
    (q : ∀ i, X i → G) (g : E → ℝ) (hg : Continuous g) (v : G → ℝ)
    (r : ℝ) (h : ∀ i x, dist (g (f i x)) (v (q i x)) ≤ r)
    (x : (U : Filter I).Product X) :
    dist (g (ultralimitFunction U f x)) (v (finiteFunction U q x)) ≤ r := by
  induction x using Quotient.inductionOn with
  | h a =>
    have hc : Tendsto (fun _ : I => v (finiteValue U (fun i => q i (a i))))
        (U : Filter I) (𝓝 (v (finiteValue U (fun i => q i (a i))))) := tendsto_const_nhds
    have hlim := ((hg.tendsto _).comp (tendsto_ultralimitFunction U f a)).dist hc
    apply le_of_tendsto hlim
    apply (eventually_eq_finiteValue U (fun i => q i (a i))).mono
    intro i hi
    change dist (g (f i (a i))) (v (finiteValue U (fun j => q j (a j)))) ≤ r
    rw [← hi]
    exact h i (a i)

end Erdos335.Loeb
