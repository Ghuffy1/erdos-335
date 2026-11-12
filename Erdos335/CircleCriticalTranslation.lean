import Erdos335.CircleDifferenceSequence
import Erdos335.CircleOverlapIntegral
import Erdos335.HaarOverlapTranslation
import Erdos335.CompactSumLocalization

/-!
# Sharp translation losses from localized critical circle pairs
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter Topology MeasureTheory
open scoped Pointwise

namespace Erdos335.Loeb

theorem unitCircle_critical_overlap_loss_le
    (S A B : Set (AddCircle (1 : ℝ))) (hsum : A + B ≤ᵐ[volume] S)
    (hmass : (volume S).toReal = (volume A).toReal + (volume B).toReal)
    (x y : AddCircle (1 : ℝ)) (hx : x ∈ B) (hy : y ∈ B) :
    (volume S).toReal - haarOverlap volume S (x - y) ≤ (volume B).toReal := by
  have : Fact (0 < (1 : ℝ)) := ⟨zero_lt_one⟩
  have h := haarOverlap_ge_of_sumset_ae_subset volume A B S hsum x y hx hy
  linarith

theorem exists_unitCircle_sharp_translation_sequence
    (S : Set (AddCircle (1 : ℝ))) (hS : MeasurableSet S)
    (A B : ℕ → Set (AddCircle (1 : ℝ)))
    (hB : ∀ n, MeasurableSet (B n)) (hpositive : ∀ n, 0 < volume (B n))
    (hsum : ∀ n, A n + B n ≤ᵐ[volume] S)
    (hmass : ∀ n, (volume S).toReal = (volume (A n)).toReal + (volume (B n)).toReal)
    (hlocal : ∀ V ∈ 𝓝 (0 : AddCircle (1 : ℝ)), ∀ᶠ n in atTop, B n - B n ⊆ V)
    (ε : ℕ → ℝ) (hε : ∀ n, 0 < ε n) :
    ∃ t : ℕ → ℝ, (∀ n, 0 < t n ∧ t n < 1) ∧ Tendsto t atTop (𝓝 0) ∧
      ∀ c : AddCircle (1 : ℝ), ∀ n,
        (∫ (x : ℝ) in 0..1,
          max ((c +ᵥ S).indicator (fun _ => (1 : ℝ)) (x : AddCircle (1 : ℝ)) -
            (c +ᵥ S).indicator (fun _ => (1 : ℝ)) ((x + t n : ℝ) : AddCircle (1 : ℝ))) 0)
          ≤ (1 + ε n) * t n := by
  have : Fact (0 < (1 : ℝ)) := ⟨zero_lt_one⟩
  obtain ⟨N, t, hdata, hlimit⟩ := exists_unitCircle_difference_sequence B hB hpositive hlocal ε hε
  refine ⟨t, fun n => ⟨(hdata n).1, (hdata n).2.1⟩, hlimit, ?_⟩
  intro c n
  obtain ⟨_, _, x, hx, y, hy, heq, hbound⟩ := hdata n
  have htranslate : MeasurableSet (c +ᵥ S) := by
    rw [vadd_set_eq_neg_preimage]
    exact hS.preimage (measurable_const.add measurable_id)
  have hmeasure : volume (c +ᵥ S) = volume S := by
    rw [vadd_set_eq_neg_preimage, measure_preimage_add]
  rw [← unitCircle_overlap_loss_eq_interval_integral (c +ᵥ S) htranslate (t n),
    hmeasure, haarOverlap_translate_eq, heq]
  exact (unitCircle_critical_overlap_loss_le S (A (n + N)) (B (n + N))
    (hsum (n + N)) (hmass (n + N)) x y hx hy).trans hbound

end Erdos335.Loeb
