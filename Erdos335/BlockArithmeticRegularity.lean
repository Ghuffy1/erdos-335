import Erdos335.IntegerSampleRegularity
import Erdos335.FiniteBlockSums

/-!
# Uniform arithmetic regularity on all blocks of a fixed length
-/

set_option autoImplicit false

open Finset
open scoped BigOperators Classical

namespace Erdos335.IntermediateScale

theorem blockwise_arithmetic_regularity (ε : ℝ) (hε : 0 < ε) :
    ∃ L : ℕ, 0 < L ∧ ∀ (H : ℕ), 0 < H → ∀ F : ℕ → ℝ,
      (∀ n, F n ∈ Set.Icc (0 : ℝ) 1) →
      ∃ (g : ℕ → ℝ) (α : ℕ → Fin L → ℝ) (a : ℕ → Fin L → ℂ),
        (∀ n, g n ∈ Set.Icc (0 : ℝ) 1) ∧
        (∀ b j, ‖a b j‖ ≤ 1) ∧
        ∀ b : ℕ,
          (∑ i : Fin H, (F (H * b + i.val) - g (H * b + i.val))) = 0 ∧
          (∑ i : Fin H, g (H * b + i.val) * (F (H * b + i.val) - g (H * b + i.val))) = 0 ∧
          (∀ β : ℝ,
            ‖∑ i : Fin H, ((F (H * b + i.val) - g (H * b + i.val) : ℝ) : ℂ) *
              unitCharacter (((H * b + i.val : ℕ) : ℝ) * β)‖ ≤ ε * H) ∧
          (∑ i : Fin H, ‖(g (H * b + i.val) : ℂ) -
            ∑ j, a b j * unitCharacter (((H * b + i.val : ℕ) : ℝ) * α b j)‖ ^ 2) / H ≤ ε ^ 2 := by
  obtain ⟨L, hL, hreg⟩ := integer_sample_regularity.{0} ε hε
  refine ⟨L, hL, ?_⟩
  intro H hH F hF
  let : NeZero H := ⟨hH.ne'⟩
  have hex (b : ℕ) := hreg (Fin H) (fun i => ((H * b + i.val : ℕ) : ℤ))
    (fun i => F (H * b + i.val)) (fun i => hF (H * b + i.val))
  choose s α a hs hsum horth ha htest happrox using hex
  let g := blockLift H hH s
  have hg (b : ℕ) (i : Fin H) : g (H * b + i.val) = s b i := blockLift_apply H hH s b i
  refine ⟨g, α, a, fun n => hs (n / H) ⟨n % H, Nat.mod_lt n hH⟩, ha, fun b => ?_⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · simp only [hg, sum_sub_distrib, ← hsum b, sub_self]
  · simpa only [hg] using horth b
  · intro β
    simpa only [hg, Int.cast_natCast, Fintype.card_fin] using htest b β
  · simpa only [hg, Int.cast_natCast, Fintype.card_fin] using happrox b

end Erdos335.IntermediateScale
