import Mathlib.Topology.Algebra.Group.Pointwise
import Mathlib.MeasureTheory.Measure.Continuity
import Mathlib.MeasureTheory.Group.AddCircle

/-!
# Open sums of orbit closures and finite-union measure bounds

Private proof development. Verification status is recorded separately.
An open summand absorbs the difference between an image and its closure.
Increasing finite-prefix unions then transfer a uniform finite-union bound.
-/

set_option autoImplicit false

open Set Filter Topology MeasureTheory
open scoped Pointwise ENNReal

namespace Erdos335

theorem closure_image_add_open_eq_iUnion
    {ι G : Type*} [AddGroup G] [TopologicalSpace G] [IsTopologicalAddGroup G]
    (f : ι → G) (E : Set ι) (J : Set G) (hJ : IsOpen J) :
    closure (f '' E) + J = ⋃ i ∈ E, f i +ᵥ J := by
  rw [hJ.closure_add (f '' E)]
  ext z
  constructor
  · rintro ⟨x, ⟨i, hi, rfl⟩, y, hy, rfl⟩
    exact Set.mem_iUnion.mpr ⟨i, Set.mem_iUnion.mpr ⟨hi, ⟨y, hy, rfl⟩⟩⟩
  · intro hz
    obtain ⟨i, hi⟩ := Set.mem_iUnion.mp hz
    obtain ⟨hiE, y, hy, heq⟩ := Set.mem_iUnion.mp hi
    exact ⟨f i, ⟨i, hiE, rfl⟩, y, hy, heq⟩

theorem measure_biUnion_le_of_finset_bounds
    {X : Type*} [MeasurableSpace X] (μ : Measure X)
    (E : Set ℕ) (T : ℕ → Set X) (M : ℝ≥0∞)
    (hbound : ∀ F : Finset ℕ, (F : Set ℕ) ⊆ E →
      μ (⋃ n ∈ F, T n) ≤ M) :
    μ (⋃ n ∈ E, T n) ≤ M := by
  classical
  let F : ℕ → Finset ℕ := fun N => (Finset.range N).filter (fun n => n ∈ E)
  let V : ℕ → Set X := fun N => ⋃ n ∈ F N, T n
  have hFsubset (N : ℕ) : (F N : Set ℕ) ⊆ E := by
    intro n hn
    exact (Finset.mem_filter.mp hn).2
  have hFmono : Monotone F := by
    intro N K hNK
    apply Finset.filter_subset_filter
    exact Finset.range_mono hNK
  have hVmono : Monotone V := by
    intro N K hNK z hz
    obtain ⟨n, hn⟩ := Set.mem_iUnion.mp hz
    obtain ⟨hnF, hzn⟩ := Set.mem_iUnion.mp hn
    exact Set.mem_iUnion.mpr
      ⟨n, Set.mem_iUnion.mpr ⟨hFmono hNK hnF, hzn⟩⟩
  have hUnion : (⋃ N, V N) = ⋃ n ∈ E, T n := by
    ext z
    constructor
    · intro hz
      obtain ⟨N, hzN⟩ := Set.mem_iUnion.mp hz
      obtain ⟨n, hn⟩ := Set.mem_iUnion.mp hzN
      obtain ⟨hnF, hzn⟩ := Set.mem_iUnion.mp hn
      exact Set.mem_iUnion.mpr
        ⟨n, Set.mem_iUnion.mpr ⟨hFsubset N hnF, hzn⟩⟩
    · intro hz
      obtain ⟨n, hn⟩ := Set.mem_iUnion.mp hz
      obtain ⟨hnE, hzn⟩ := Set.mem_iUnion.mp hn
      apply Set.mem_iUnion.mpr
      refine ⟨n + 1, Set.mem_iUnion.mpr ⟨n, Set.mem_iUnion.mpr ⟨?_, hzn⟩⟩⟩
      exact Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (Nat.lt_succ_self n), hnE⟩
  rw [← hUnion, hVmono.measure_iUnion]
  exact iSup_le fun N => hbound (F N) (hFsubset N)

theorem orbit_closure_add_open_eq_iUnion
    (θ : ℝ) (E : Set ℕ) (J : Set (AddCircle (1 : ℝ))) (hJ : IsOpen J) :
    closure ((fun n : ℕ => n • (θ : AddCircle (1 : ℝ))) '' E) + J =
      ⋃ n ∈ E, n • (θ : AddCircle (1 : ℝ)) +ᵥ J :=
  closure_image_add_open_eq_iUnion
    (fun n : ℕ => n • (θ : AddCircle (1 : ℝ))) E J hJ

theorem volume_orbit_closure_add_open_le
    (θ : ℝ) (E : Set ℕ) (J : Set (AddCircle (1 : ℝ))) (hJ : IsOpen J)
    (M : ℝ≥0∞)
    (hbound : ∀ F : Finset ℕ, (F : Set ℕ) ⊆ E →
      volume (⋃ n ∈ F, n • (θ : AddCircle (1 : ℝ)) +ᵥ J) ≤ M) :
    volume (closure ((fun n : ℕ => n • (θ : AddCircle (1 : ℝ))) '' E) + J) ≤ M := by
  rw [orbit_closure_add_open_eq_iUnion θ E J hJ]
  exact measure_biUnion_le_of_finset_bounds volume E
    (fun n => n • (θ : AddCircle (1 : ℝ)) +ᵥ J) M hbound

theorem volume_orbit_closure_add_open_toReal_le
    (θ : ℝ) (E : Set ℕ) (J : Set (AddCircle (1 : ℝ))) (hJ : IsOpen J)
    (M : ℝ)
    (hbound : ∀ F : Finset ℕ, (F : Set ℕ) ⊆ E →
      (volume (⋃ n ∈ F, n • (θ : AddCircle (1 : ℝ)) +ᵥ J)).toReal ≤ M) :
    (volume (closure ((fun n : ℕ => n • (θ : AddCircle (1 : ℝ))) '' E) + J)).toReal ≤ M := by
  letI : Fact (0 < (1 : ℝ)) := ⟨zero_lt_one⟩
  letI : IsProbabilityMeasure (volume : Measure (AddCircle (1 : ℝ))) :=
    ⟨by simpa using AddCircle.measure_univ (1 : ℝ)⟩
  have hM : 0 ≤ M := by
    simpa using hbound ∅ (by simp)
  have hENN : ∀ F : Finset ℕ, (F : Set ℕ) ⊆ E →
      volume (⋃ n ∈ F, n • (θ : AddCircle (1 : ℝ)) +ᵥ J) ≤ ENNReal.ofReal M := by
    intro F hFE
    calc
      volume (⋃ n ∈ F, n • (θ : AddCircle (1 : ℝ)) +ᵥ J) =
          ENNReal.ofReal
            ((volume (⋃ n ∈ F, n • (θ : AddCircle (1 : ℝ)) +ᵥ J)).toReal) :=
        (ENNReal.ofReal_toReal (measure_ne_top volume _)).symm
      _ ≤ ENNReal.ofReal M := ENNReal.ofReal_le_ofReal (hbound F hFE)
  have hsum := volume_orbit_closure_add_open_le θ E J hJ (ENNReal.ofReal M) hENN
  have hreal := ENNReal.toReal_mono (by simp : ENNReal.ofReal M ≠ ∞) hsum
  simpa only [ENNReal.toReal_ofReal hM] using hreal

end Erdos335
