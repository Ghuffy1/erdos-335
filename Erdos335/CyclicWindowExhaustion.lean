import Erdos335.CyclicWindowRepresentatives
import Erdos335.SlowPrefixRestoration

/-!
# Exhaustive prefix inputs after cyclic removal

Every fixed element of the original prefix input can be restored while
preserving vanishing deletion and sumset errors.
-/

set_option autoImplicit false

open Filter Topology Finset
open scoped Pointwise

namespace Erdos335.IntermediateScale

theorem restore_exhaustive_cyclic_prefix (A B : Set ℕ) (q start : ℕ → ℕ)
    [∀ n, NeZero (q n)] (hq : Tendsto q atTop atTop)
    (A' B' : ∀ n, Finset (ZMod (q n)))
    (hA' : ∀ n, A' n ⊆ cyclicWindow A (start n) (q n))
    (hB' : ∀ n, B' n ⊆ cyclicWindow B 0 (q n))
    (hcut : Tendsto (fun n =>
      ((cyclicWindow B 0 (q n) \ B' n).card : ℝ) / q n) atTop (𝓝 0))
    (hsum : Tendsto (fun n =>
      (((A' n + B' n) \ cyclicWindow (A + B) (start n) (q n)).card : ℝ) / q n)
      atTop (𝓝 0)) :
    ∃ B'' : ∀ n, Finset (ZMod (q n)),
      (∀ n, B' n ⊆ B'' n ∧ B'' n ⊆ cyclicWindow B 0 (q n)) ∧
      (∀ b ∈ B, ∀ᶠ n in atTop, (b : ZMod (q n)) ∈ B'' n) ∧
      Tendsto (fun n => ((cyclicWindow B 0 (q n) \ B'' n).card : ℝ) / q n)
        atTop (𝓝 0) ∧
      Tendsto (fun n =>
        (((A' n + B'' n) \ cyclicWindow (A + B) (start n) (q n)).card : ℝ) / q n)
        atTop (𝓝 0) := by
  classical
  obtain ⟨J, hJq, hJ, hJsq⟩ := exists_slow_square_prefix q hq
  let F := fun n => finitePrefix B (J n)
  let B'' := fun n => B' n ∪ (F n).image (fun b : ℕ => (b : ZMod (q n)))
  have hF (n : ℕ) (b : ℕ) (hb : b ∈ F n) : b ∈ B ∧ b < q n := by
    obtain ⟨hbJ, hbB⟩ := mem_filter.mp hb
    exact ⟨hbB, (mem_range.mp hbJ).trans_le (hJq n)⟩
  have hBsub (n : ℕ) : B' n ⊆ B'' n := subset_union_left
  have hBfull (n : ℕ) : B'' n ⊆ cyclicWindow B 0 (q n) := by
    intro x hx
    rcases mem_union.mp hx with hx | hx
    · exact hB' n hx
    · obtain ⟨b, hb, rfl⟩ := mem_image.mp hx
      apply mem_filter.mpr
      refine ⟨mem_univ _, ?_⟩
      rw [ZMod.val_natCast_of_lt (hF n b hb).2, zero_add]
      exact (hF n b hb).1
  have hqpos (n : ℕ) : (0 : ℝ) < q n := by
    exact_mod_cast (NeZero.pos (q n))
  refine ⟨B'', (fun n => ⟨hBsub n, hBfull n⟩), ?_, ?_, ?_⟩
  · intro b hb
    filter_upwards [hJ.eventually (eventually_gt_atTop b)] with n hn
    apply mem_union_right
    apply mem_image.mpr
    exact ⟨b, mem_filter.mpr ⟨mem_range.mpr hn, hb⟩, rfl⟩
  · apply squeeze_zero (fun n => by positivity) _ hcut
    intro n
    apply div_le_div_of_nonneg_right _ (hqpos n).le
    exact_mod_cast card_le_card (Finset.sdiff_subset_sdiff
      (Finset.Subset.refl _) (hBsub n))
  · have htotal : Tendsto (fun n =>
        (((A' n + B' n) \ cyclicWindow (A + B) (start n) (q n)).card : ℝ) / q n +
          (J n : ℝ) ^ 2 / q n) atTop (𝓝 0) := by
      simpa only [add_zero] using hsum.add hJsq
    apply squeeze_zero (fun n => by positivity) _ htotal
    intro n
    have hbound := restored_representatives_error_le A B (start n) (q n)
      (A' n) (B' n) (hA' n) (F n) (hF n)
    have hsumF := prefix_sum_le_square B (J n)
    have hnat : (((A' n + B'' n) \ cyclicWindow (A + B) (start n) (q n)).card) ≤
        (((A' n + B' n) \ cyclicWindow (A + B) (start n) (q n)).card) + (J n) ^ 2 :=
      hbound.trans (Nat.add_le_add_left hsumF _)
    rw [← add_div]
    apply div_le_div_of_nonneg_right _ (hqpos n).le
    exact_mod_cast hnat

end Erdos335.IntermediateScale
