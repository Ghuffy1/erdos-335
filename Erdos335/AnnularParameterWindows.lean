import Erdos335.AnnularBlockParameters

/-!
# Counting windows on which stitched polynomial parameters can change
-/

set_option autoImplicit false

open Filter Topology Finset
open scoped Classical

namespace Erdos335.IntermediateScale

theorem terminal_window_count (N W : ℕ) :
    ((range N).filter (fun n => N ≤ n + W)).card ≤ W := by
  have hcard : ((range N).filter (fun n => N ≤ n + W)).card ≤ (range W).card := by
    apply card_le_card_of_injOn (fun n => n + W - N)
    · intro n hn
      obtain ⟨hnN, hterminal⟩ := mem_filter.mp hn
      dsimp only
      exact mem_range.mpr (by have := mem_range.mp hnN; omega)
    · intro n hn m hm heq
      dsimp only at heq
      have hn' := (mem_filter.mp hn).2
      have hm' := (mem_filter.mp hm).2
      omega
  simpa only [card_range] using hcard

noncomputable def varyingParameterWindows {F : ℕ → ℝ} {H : ℕ → ℕ} {L : ℕ} {ε : ℝ}
    (N : ℕ → ℕ) (hN : Tendsto N atTop atTop)
    (m : ∀ s, BlockRegularModel F (H s) L ε) (s W : ℕ) : Finset ℕ :=
  (range (N s)).filter fun n => ∃ i ≤ W, ∃ j : Fin L,
    stitchedBlockCoefficient N hN m (n + i) j ≠ stitchedBlockCoefficient N hN m n j ∨
    stitchedBlockFrequency N hN m (n + i) j ≠ stitchedBlockFrequency N hN m n j

theorem varyingParameterWindows_card {F : ℕ → ℝ} {H : ℕ → ℕ} {L : ℕ} {ε : ℝ}
    (N : ℕ → ℕ) (hN : Tendsto N atTop atTop) (hmono : Monotone N)
    (m : ∀ s, BlockRegularModel F (H s) L ε) (s W : ℕ) (hH : 0 < H s) :
    (varyingParameterWindows N hN m s W).card ≤ N (s - 1) + W + (N s / H s + 1) * W := by
  let early := (range (N s)).filter (fun n => n < N (s - 1))
  let late := (range (N s)).filter (fun n => N s ≤ n + W)
  let crossing := (range (N s)).filter (fun n => n / H s ≠ (n + W) / H s)
  have hsubset : varyingParameterWindows N hN m s W ⊆ early ∪ late ∪ crossing := by
    intro n hn
    obtain ⟨hnN, i, hi, j, hvary⟩ := mem_filter.mp hn
    by_cases hearly : n < N (s - 1)
    · exact mem_union_left _ (mem_union_left _ (mem_filter.mpr ⟨hnN, hearly⟩))
    by_cases hlate : N s ≤ n + W
    · exact mem_union_left _ (mem_union_right _ (mem_filter.mpr ⟨hnN, hlate⟩))
    by_cases hcross : n / H s ≠ (n + W) / H s
    · exact mem_union_right _ (mem_filter.mpr ⟨hnN, hcross⟩)
    have hconstant := stitchedBlockParameters_constant_on_window N hN hmono m s n W
      (by omega) (by omega) (not_ne_iff.mp hcross) i hi j
    exact False.elim (hvary.elim (fun h => h hconstant.1) (fun h => h hconstant.2))
  have hearlyCard : early.card ≤ N (s - 1) := by
    calc
      _ ≤ (range (N (s - 1))).card := card_le_card fun n hn => mem_range.mpr (mem_filter.mp hn).2
      _ = _ := card_range _
  have hlateCard : late.card ≤ W := terminal_window_count (N s) W
  have hcrossCard : crossing.card ≤ (N s / H s + 1) * W := block_crossing_window_card (N s) (H s) W hH
  calc
    _ ≤ (early ∪ late ∪ crossing).card := card_le_card hsubset
    _ ≤ (early ∪ late).card + crossing.card := card_union_le _ _
    _ ≤ early.card + late.card + crossing.card := Nat.add_le_add_right (card_union_le _ _) _
    _ ≤ _ := by omega

end Erdos335.IntermediateScale
