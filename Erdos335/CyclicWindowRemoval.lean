import Erdos335.AsymptoticSumsetRemoval
import Erdos335.CyclicWindowExhaustion

/-!
# Cyclic window trimming with literal exhaustion

This is the removal-theorem step of Ackelsberg--Richter, Theorem 9.1,
given its preceding popular-sumset estimate.
-/

set_option autoImplicit false

open Filter Topology Finset
open scoped Pointwise

namespace Erdos335.IntermediateScale

theorem cyclic_window_removal_with_exhaustion (A B : Set ℕ) (q start : ℕ → ℕ)
    [∀ n, NeZero (q n)] (hq : Tendsto q atTop atTop) (δ η : ℕ → ℝ)
    (hδ : Tendsto δ atTop (𝓝 0)) (hη : Tendsto η atTop (𝓝 0))
    (hpopular : ∀ᶠ n in atTop,
      ((ArithmeticRemoval.popularSum (cyclicWindow A (start n) (q n))
        (cyclicWindow B 0 (q n)) (δ n) \ cyclicWindow (A + B) (start n) (q n)).card : ℝ)
          ≤ η n * q n) :
    ∃ A' B' : ∀ n, Finset (ZMod (q n)),
      (∀ n, A' n ⊆ cyclicWindow A (start n) (q n) ∧ B' n ⊆ cyclicWindow B 0 (q n)) ∧
      (∀ b ∈ B, ∀ᶠ n in atTop, (b : ZMod (q n)) ∈ B' n) ∧
      Tendsto (fun n => ((cyclicWindow A (start n) (q n) \ A' n).card : ℝ) / q n)
        atTop (𝓝 0) ∧
      Tendsto (fun n => ((cyclicWindow B 0 (q n) \ B' n).card : ℝ) / q n)
        atTop (𝓝 0) ∧
      Tendsto (fun n =>
        (((A' n + B' n) \ cyclicWindow (A + B) (start n) (q n)).card : ℝ) / q n)
        atTop (𝓝 0) := by
  have hpop : ∀ᶠ n in atTop,
      ((ArithmeticRemoval.popularSum (cyclicWindow A (start n) (q n))
        (cyclicWindow B 0 (q n)) (δ n) \ cyclicWindow (A + B) (start n) (q n)).card : ℝ)
          ≤ η n * Fintype.card (ZMod (q n)) := by
    simpa only [ZMod.card] using hpopular
  obtain ⟨A', B', hsub, hAcut, hBcut, hsum⟩ := ArithmeticRemoval.asymptotic_sumset_removal
    (fun n => cyclicWindow A (start n) (q n)) (fun n => cyclicWindow B 0 (q n))
    (fun n => cyclicWindow (A + B) (start n) (q n)) δ η hδ hη hpop
  simp only [ZMod.card] at hAcut hBcut hsum
  obtain ⟨B'', hB'', hexhaust, hBcut'', hsum''⟩ := restore_exhaustive_cyclic_prefix
    A B q start hq A' B' (fun n => (hsub n).1) (fun n => (hsub n).2) hBcut hsum
  exact ⟨A', B'', (fun n => ⟨(hsub n).1, (hB'' n).2⟩), hexhaust,
    hAcut, hBcut'', hsum''⟩

end Erdos335.IntermediateScale
