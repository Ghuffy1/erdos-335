import Erdos335.DensityAlgebra
import Mathlib.Topology.Instances.AddCircle.Defs

/-!
# Fixed translates of positive orbit pullbacks

Private proof development. Verification status is recorded separately.
The orbit pullback uses positive natural indices. A fixed translate agrees
with the corresponding shifted set above its translation parameter.
-/

set_option autoImplicit false

open Set
open scoped Pointwise

namespace Erdos335

def positiveOrbitPullback (θ : ℝ) (S : Set (AddCircle (1 : ℝ))) : Set ℕ :=
  {n | 0 < n ∧ n • (θ : AddCircle (1 : ℝ)) ∈ S}

theorem shift_positiveOrbitPullback_subset
    (θ : ℝ) (S : Set (AddCircle (1 : ℝ))) (t : ℕ) :
    shift (positiveOrbitPullback θ S) t ⊆
      positiveOrbitPullback θ (t • (θ : AddCircle (1 : ℝ)) +ᵥ S) := by
  rintro n ⟨m, ⟨hm0, hmS⟩, rfl⟩
  refine ⟨by change 0 < m + t; omega, ?_⟩
  refine ⟨m • (θ : AddCircle (1 : ℝ)), hmS, ?_⟩
  change t • (θ : AddCircle (1 : ℝ)) + m • (θ : AddCircle (1 : ℝ)) =
    (m + t) • (θ : AddCircle (1 : ℝ))
  rw [add_nsmul, add_comm]

theorem mem_positiveOrbitPullback_translate_iff
    (θ : ℝ) (S : Set (AddCircle (1 : ℝ))) (t n : ℕ) (hn : t < n) :
    n ∈ positiveOrbitPullback θ (t • (θ : AddCircle (1 : ℝ)) +ᵥ S) ↔
      n ∈ shift (positiveOrbitPullback θ S) t := by
  constructor
  · rintro ⟨_, y, hy, heq⟩
    change t • (θ : AddCircle (1 : ℝ)) + y = n • (θ : AddCircle (1 : ℝ)) at heq
    have hphase : (n - t) • (θ : AddCircle (1 : ℝ)) = y := by
      apply add_left_cancel (a := t • (θ : AddCircle (1 : ℝ)))
      calc
        t • (θ : AddCircle (1 : ℝ)) + (n - t) • (θ : AddCircle (1 : ℝ)) =
            n • (θ : AddCircle (1 : ℝ)) := by
          rw [← add_nsmul, Nat.add_comm t (n - t), Nat.sub_add_cancel hn.le]
        _ = t • (θ : AddCircle (1 : ℝ)) + y := heq.symm
    refine ⟨n - t, ⟨by omega, ?_⟩, Nat.sub_add_cancel hn.le⟩
    rwa [hphase]
  · exact fun h => shift_positiveOrbitPullback_subset θ S t h

theorem positiveOrbitPullback_translate_densityEquivalent
    (θ : ℝ) (S : Set (AddCircle (1 : ℝ))) (t : ℕ) :
    DensityEquivalent
      (positiveOrbitPullback θ (t • (θ : AddCircle (1 : ℝ)) +ᵥ S))
      (shift (positiveOrbitPullback θ S) t) :=
  DensityEquivalent.of_eventually_eq t
    (fun n hn => mem_positiveOrbitPullback_translate_iff θ S t n hn)

theorem positiveOrbitPullback_translate_sdiff_sum_negligible
    (θ : ℝ) (S : Set (AddCircle (1 : ℝ))) (A B : Set ℕ)
    (hB : DensityEquivalent B (positiveOrbitPullback θ S))
    (t : ℕ) (ht : t ∈ A) :
    Negligible
      (positiveOrbitPullback θ (t • (θ : AddCircle (1 : ℝ)) +ᵥ S) \ (A + B)) := by
  have htranslate : DensityEquivalent
      (positiveOrbitPullback θ (t • (θ : AddCircle (1 : ℝ)) +ᵥ S)) (shift B t) :=
    (positiveOrbitPullback_translate_densityEquivalent θ S t).trans (hB.shift t).symm
  have hsub : shift B t ⊆ A + B := shift_subset_sum ht
  apply htranslate.1.mono
  rintro n ⟨hn, hnot⟩
  exact ⟨hn, fun hshift => hnot (hsub hshift)⟩

theorem positiveOrbitPullback_finite_translates_sdiff_sum_negligible
    (θ : ℝ) (S : Set (AddCircle (1 : ℝ))) (A B : Set ℕ)
    (hB : DensityEquivalent B (positiveOrbitPullback θ S))
    (F : Finset ℕ) (hFA : (F : Set ℕ) ⊆ A) :
    Negligible
      (positiveOrbitPullback θ
        (⋃ t ∈ F, t • (θ : AddCircle (1 : ℝ)) +ᵥ S) \ (A + B)) := by
  have herrors : Negligible (finiteUnion F (fun t =>
      positiveOrbitPullback θ (t • (θ : AddCircle (1 : ℝ)) +ᵥ S) \ (A + B))) :=
    negligible_finiteUnion F _ (fun t ht =>
      positiveOrbitPullback_translate_sdiff_sum_negligible θ S A B hB t (hFA ht))
  apply herrors.mono
  rintro n ⟨⟨hn0, hnUnion⟩, hnSum⟩
  obtain ⟨t, ht⟩ := Set.mem_iUnion.mp hnUnion
  obtain ⟨htF, hnS⟩ := Set.mem_iUnion.mp ht
  exact ⟨t, htF, ⟨⟨hn0, hnS⟩, hnSum⟩⟩

end Erdos335
