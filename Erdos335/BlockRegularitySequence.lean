import Erdos335.BlockRegularModel
import Erdos335.RegularityAccuracySequence

/-!
# A decreasing accuracy schedule with compatible regularity complexities
-/

set_option autoImplicit false

open Filter Topology

namespace Erdos335.IntermediateScale

theorem exists_block_regularity_sequence (F : ℕ → ℝ)
    (hF : ∀ n, F n ∈ Set.Icc (0 : ℝ) 1) :
    ∃ (ε : ℕ → ℝ) (L : ℕ → ℕ),
      (∀ k, 0 < ε k ∧ ε k ≤ 1 ∧ 0 < L k) ∧
      Tendsto ε atTop (𝓝 0) ∧
      (∀ k l, k < l → (L k : ℝ) * ε l ≤ ε k) ∧
      ∀ k H, 0 < H → Nonempty (BlockRegularModel F H (L k) (ε k)) := by
  classical
  have hex (ε : ℝ) : ∃ L : ℕ, 0 < L ∧
      (0 < ε → ∀ H, 0 < H → Nonempty (BlockRegularModel F H L ε)) := by
    by_cases hε : 0 < ε
    · obtain ⟨L, hL, hm⟩ := exists_block_regular_model ε hε
      exact ⟨L, hL, fun _ H hH => hm H hH F hF⟩
    · exact ⟨1, by omega, fun h => (hε h).elim⟩
  choose d hdpos hdmodel using hex
  let ε := regularityAccuracy d
  let L := fun k => d (ε k)
  have hpos (k : ℕ) : 0 < ε k := regularityAccuracy_pos d k
  have hmono : Antitone ε := antitone_nat_of_succ_le fun k => by
    have h := regularityAccuracy_step_le d k
    change ε (k + 1) ≤ ε k / 2 at h
    linarith [hpos k]
  refine ⟨ε, L, ?_, regularityAccuracy_tendsto_zero d, ?_, ?_⟩
  · intro k
    exact ⟨hpos k, (hmono (Nat.zero_le k)).trans (by simp [ε, regularityAccuracy]), hdpos (ε k)⟩
  · intro k l hkl
    calc
      (L k : ℝ) * ε l ≤ (L k : ℝ) * ε (k + 1) :=
        mul_le_mul_of_nonneg_left (hmono (by omega)) (Nat.cast_nonneg _)
      _ ≤ ε k := regularityAccuracy_complexity_bound d k
  · exact fun k H hH => hdmodel (ε k) (hpos k) H hH

end Erdos335.IntermediateScale
